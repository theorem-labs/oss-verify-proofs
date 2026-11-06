(* This file carries the kit's text of the HPOS premise of tcheck_as_written_specX (the unit
   owner's ruling D2, 21:54Z) and of the re-hiding move for its six crossing texts (`PRIMED-SHAPES.md (sha256 9e4880d18317; internal record)`
   sec. 2.3-2.8): tparse_noting, tcheck_no_overread, tcheck_as_written, tcheck_reject_clean_starved, tround_trip_text
   and tcheck_round_trip conclude SRr' segs RZ_cf; their posts (fpostFbm / fpostFm) are AFTER-FREE-ONLY families,
   already at wle' segs RZ_cf in PRH_Base.v.
   The unit owner's ruling C2 (2026-10-31 04:19Z) struck the scratch notice that stood here, by a
   comment-only edit that keeps the header at 7 lines, so every line after it keeps its number. *)
(* fuzz_preset, program part (the kit's check texts): the ASan contract TEXTS of the harness's checks and their helpers
   (fuzz_preset.c @0b89c6c1bd, the rebuilt image's harness): check_bounded_alloc, check_reject_clean, parse_noting,
   check_no_overread, check_as_written, check_reject_clean_starved, round_trip_text, check_round_trip. Form: PRH_FnAlloc.v's
   (cgif_file lib/YC21.v:33-66; the fm port's FMH_Fn.v:101-180): fpre (YCbqG's afn_pre_x + the read-only view), argument
   registers, the alloc.c ledger (PRH_Base.v prh_ledger), the allocation traces in the image's universe where the
   function reaches the allocator, the room invariant (below), and SRr to the return address through fpost / fpostF
   (YCbqG's apost_base_x at PST := prh_pst, or its float-state twin); the NULL-site abort arms are DEFERRED (fixed
   harness #102, see ABORTS). Every conclusion is `srealizes`, through SRr.
   room: room_live_cf (PRH_Base.v, owned by the allocator-model owner), room_cf at none (the kit owner's ruling "(i)": no text states the
   primary room); margins removed. The six allocating texts take room_live_cf S on entry and give room_live_cf S' in
   every post arm; check_bounded_alloc and check_reject_clean carry room_live_cf S -> room_live_cf S'. The primary room
   of every allocator call in these texts' subtrees - check_as_written's scratch malloc (its first allocator call, at
   its entry state on both images: A 0x81f78, B 0x82084), check_no_overread's three copy mallocs, and the rest - comes
   from P8's preset_room through the driver's slot (the driver-contract owner).
   NOT HERE: LLVMFuzzerTestOneInput, whose statement is the driver-contract owner's preset_lib_contract_x (lib/A/PresetCfnA.v); its
   callee interface (afn_spec_cf, PresetCfnA.v:1024-1035) takes these texts: the same pre (afn_pre + the universe closure
   + frames bound + read-only view + live room + room_live_cf + own pre) and post (the journal post with Hp in Q).
   IMAGE-PARAMETRIC: the image is the listing class (YC4aP PAImg L); each entry is pa_sigma AS_<fn>; no image constant.
   ALLOCATOR-PARAMETRIC: ARx is an explicit argument.
   FUNCTIONAL CONTENT: preset's plain contracts lib/Prog/<fn>_c.v (named per text), restated over the ASan state. Their
   pure models are reused by qualified name (lib/Spec PjTree, PjGrammar, PjRoundTrip; lib/Prog ReaderRes,
   WriterValue / PjWriteHyp, TxModel); no plain lemma is cited. Plain-only machinery is dropped: rf_ok / rf_room /
   room_run become the live room `blocks_bytes S + LIVE_<fn> <= LIVE_MAX` (LIVE_<fn> below, derived from the plain
   peak bounds, heads included); reader_env -> fpre; rpost -> fpost(F); rd_cells / ro_agree -> fpre's read-only view.
   The tree predicates are the recursive-reader author's lib/A/PRH_Reader.v R-names over `mrestrict (w_H W) mem` with lblk := prh_lin
   Lam (pj_nodeR / pj_zeroR; no plain memory-predicate file is Required), the one set the kit's texts (pj_parse,
   pj_write, tx_*, same, ex_value, pj_set, pj_string, pj_free) state over.
   ABORTS. Per text, the premises that make each PROPERTY abort unreachable (as the plain contract has them):
   - check_bounded_alloc: held <= PJ_ALLOC_BOUND (size), size <= 2 ^ 40 (no wrap in 256u * size).
   - check_reject_clean: rc <> 0; the 56 bytes at doc are 0; live_before = g_live (= lsum Lam).
   - parse_noting: no abort of its own; check_reject_clean is reached only when the reading ran out, where the
     reader's refusal arm (rc = -1, *doc all zero, the reader's blocks all freed) meets check_reject_clean's three. A
     refusal inside the reading sets g_ran_out (prh_oks: its request is at most g_most by the text's RQ_pj_parse tb
     <= most premise) and the reading is refused cleanly: no NULL site.
   - check_no_overread: g_fail_at = SIZE_MAX (no injected failure), so a reading that did not run out is the grammar's
     reading of the first `size` bytes whatever follows them, and the two compares hold; readings that ran out are
     not compared.
   - check_as_written: rc = 0 and the grammar reads the tree at doc, or rc <> 0 and the grammar refuses.
   - check_reject_clean_starved: 0 <= took <= the reading's call count (the injected failure is reached); g_fail_at =
     SIZE_MAX at entry; doc = NULL or the grammar's tree of the input with the writer's bounds. No NULL site: by the
     source an allocator refusal does not reach its abort (the starved reading is refused either way, the reader
     frees and zeroes; the writer stops at its first failed allocation and pj_write frees its buffer and returns
     NULL, preset_file.c:454-470, :565-568; the injected write reaches its pick-th allocation or fails before), so
     its post tolerates refusal: g_count grows by at most ck_crcs_max, exactly ck_crcs_growth when g_ran_out ends 0.
   - round_trip_text: pj_wf t, depth <= 32, wlen + 1 <= 2 ^ 28 (the writer's text is the rendered one and reads back
     to t), g_fail_at = SIZE_MAX.
   - check_round_trip: json_read x = Some t with the plain length bounds, g_fail_at = SIZE_MAX.
   DEFERRED (fixed harness #102). In the harness at 0b89c6c1bd an allocator REFUSAL (the class-full NULL; a class
   does fill on accepted input) reaches abort() at the NULL sites below. By the kit owner's ruling a NULL-site arm is
   DEFERRED: check_no_overread, check_as_written, round_trip_text and check_round_trip are stated as the FIXED pin's
   kit texts WITHOUT an abort disjunct (no fabort / fabortW arm, no free-standing hypothesis), to be proved against
   the fixed pins when they land. So, against TODAY's binaries, they hold only on the runs where every allocation at
   these sites succeeds. The NULL sites (fuzz_preset.c line; the branch to the abort tail pi_abort F, image A
   f0d2e8d4 / B 3b5e1a09, neutral listings):
   - check_no_overread: the three fuzz_copy mallocs (fuzz.h:27-28, `if (!b) abort ()`): `beqz` A 0x81bdc / 0x81c10 /
     0x81c48, B 0x81cc4 / 0x81d00 / 0x81d3c; tail A 0x81f08, B 0x82004.
   - check_as_written: expected()'s scratch malloc (:339-340): `beqz` A 0x81f84, B 0x82090; tail A 0x82058, B
     0x82110. And :528-529 when the reading ran out (an allocator refusal inside pj_parse: rc <> 0, g_ran_out = 1)
     on a text the grammar reads: the pre is NARROWED to exclude this case (rc <> 0 /\ g_ran_out = 1 /\ json_read x
     <> None is outside it); a narrower pre is a weaker text, which is how the ruling defers.
   - round_trip_text: pj_write NULL (:612) `beqz` A 0x84794, B 0x84cc8; the read-back refused (:622) `bnez` A
     0x847c4, B 0x84cf8; tail A 0x84900, B 0x84e34. rendered()'s tx_put realloc NULL (:364-367) A 0x849b8 / B
     0x84ef8, to tx_put's own tail (PRH_FnTx.v:91-94: there too the refused outcome replaced the abort arm).
   - check_round_trip: pj_string / pj_set failed (:647) A 0x82714 / 0x8272c, B 0x82850 / 0x82868; the rewrite's
     pj_write NULL / pj_parse refused (:653) A 0x82740 / 0x82764, B 0x8287c / 0x828a8; tail A 0x82b14, B 0x82d88;
     and the sites of its two round_trip_text calls above.
  CLOSED 2026-10-29 (refusal outcome), the fixed source is readable in the src-102 source tree,
  new/fuzz_preset.c 836 lines sha256 c7b4007bba7bab3e and base/fuzz_preset.c 739 lines sha256 5055c96b878f121f,
  both verified against that directory's SHA256SUMS. WHAT #102 DOES at these sites: it does not abort and it does
  not continue - it ENDS THE CALL. A new file-level predicate out_of_memory() = `g_own_ran_out || fuzz_alloc_ran_out()`
  (new:79-82) is tested after each site, and the four texts' functions became int-returning, "1 when memory ran out,
  and the call ends" (new:523, :569, :668, :771). So the second post arm is NOT an abort arm: it is the r = 1 return,
  which each of the four texts below now carries. check_as_written's pre is NOT yet widened back (its narrowing is
  about the reading that ran out, which the new source ends the call on instead; widening it needs the walk, not the
  text). NO LONGER MISSING for these arms: g_own_ran_out has its generated row (PRH_Img.v:158-159), which the ledger
  reads (PRH_Base.prh_own, PRH_Base.v:806), so the four r = 1 arms state own' = 1 \/ ran' = 1 (check_as_written's
  own' = 1) by the ledger's own fields, not only by what the call did.
  The address table above is the TODAY'S-BINARY table (0b89c6c1bd) and stays until the new pins land.
   The abort-arm evidence below (ck_E_null, ck_E_txnull, ck_E_ran, ck_Ek) is KEPT though no text here uses it now:
   the H2/H5 walk's files cited it at commit 841830f5dcb, not on this tree (HISTORY: lib/A/Prog/H2CawBase.v:319-320,
   :412; H5CrtDefs.v:170-174; H5CrtNull.v:13-150; H5RttDefs.v:165-167). ck_Ek now carries room_live_cf S' and no
   margin argument (room ruling (B)), so those citations' `ck_Ek B ARc kr E` becomes `ck_Ek B ARc E`.
   NAMED GAPS:
   - C-RO (read-only objects a runtime call reads after a call), MEASURED (the kit owner, both images, same addresses
     and shadow): check_reject_clean's `static const struct pj empty` (A 0x20fa0, 56 bytes, read by bcmp, :540-550) IS
     inside one as_zero_shadow range, so in_zs holds for it. check_round_trip's "modifiedAt" (0x210a0, 11 bytes) and
     "2026-10-25T00:00:00Z" (0x21360, 21 bytes), read by strlen / memcpy / strcmp (:647-677), are NOT: their last
     granules' shadow is 03 / 05. So in_zs / kept_at's read-only case must NEVER be stated for these two over the whole
     object. Route (a) is now the kit's kept_img (PRH_Base.v, 6dbe0e718cd: 64-byte image margins, read-only, not
     owned, not errno, and each granule a whole zero-shadow granule or one with a const-shadow cell of value 0 or above
     the byte's offset, AR_laws_x field 16 alx_const_cells keeping those cells, journal d15706bda36):
     tcheck_round_trip_specX takes kept_img for both strings, so it supplies pj_set's and pj_string's kept_at (its
     third case, kept_img). The
     two addresses are the text's arguments a_mod_at / a_stamp (the instance passes the image's .str.10 / .str.30; no
     listing name exists for them yet - a generated PrhImg field would replace the arguments by rename). IMAGE B is
     PENDING: its const-shadow cells wait on the image-B memnorm owner's Tfib_const_shadow regeneration. `empty` needs no premise here:
     only check_reject_clean reads it, and in_zs holds for it (an image fact of that walk).
   - Fake frames (closed by measurement): parse_noting's *doc, round_trip_text's *copy (check_round_trip's local at
     frame + 224) and every tree root handed to pj_write / tx_value / same are stated INSIDE a fake frame of frames S;
     the use-after-return flag is 1 at target entry on both images (A 0xaa8c0, B 0xab180) and every
     __asan_stack_malloc_N call returned a fake frame (716 of 716 on in/v/small.hdr1.bin, 167 of 167 on in/small1.bin,
     each image; the kit owner's qemu run, 00:15Z). parse_noting's *ran_out is NOT: it is check_no_overread's int on
     its real stack (measured), stated in the caller-window form (fwin, fpostWF).
   - Text homes are the callees' own: a text pj_parse reads is in PRH_FnReader.v prhReader_home (kept_at, or a live
     allocator block whose base is not a hidden head: the LLVMFuzzerTestOneInput input and the fuzz_copy buffers);
     the data ex_value reads is in PRH_FnEx.v prhex_inblk.
   - Rooms compose by construction: each LIVE_<fn> is the sum of its callees' own named rooms (PRH_FnPj.v
     LIVE_pj_parse / LIVE_pj_set / LIVE_pj_string, PRH_FnWriter.v LIVE_pj_write, PRH_FnTx.v LIVE_tx) at the states they
     are called, and each request bound is the callees' own (RQ_pj_parse = prh_maxreq of pj_parse's trace, the largest
     single request in user bytes; prhWriter_WMAX; the tx cap), with cf_head added at each use site.
   - allocator traces: prh_univ_closure (PRH_Base.v, the kit owner's ruling) on the six texts that reach the allocator,
     with prh_ctx CTX0 F_<fn> (raZ regs :: spine ch) on the four frame-pointer ones (check_no_overread,
     check_reject_clean_starved, round_trip_text, check_round_trip: pi_fp, measured on both images); dropped
     prh_malloc_univ, ck_realloc_univ, prhPj_free_univ, prh_free_univ (own, pj_write's, round_trip_text's),
     prh_univ_fp and the literal malloc traces, prh_free_univ_fp, ck_tx_univ, the ctx_ext premise and the CTX
     membership: the closure implies each (its literal clause at every site with an empty chain - check_as_written
     keeps rc in s0 - and at an entry near the stack top; its frame-pointer clause at prh_ctx for the four, and
     prh_ctx_call for their callees). Kept in these texts: none; ck_realloc_univ stays defined (no text takes it); the H2/H5
     walk cited it (841830f5dcb, not on this tree: H5CrtDefs.v:143, H5RttDefs.v:125), ck_tx_univ is deleted (uncited). NOT covered by the
     closure, named here and carried by no text of this file: tx_put's prhtx_trace chain part (C-TXTRACE, below; its
     two short traces are the closure's). C-RDWORD is CLOSED by the closure's clause 4b: parse_string's /
     parse_items' free traces read pj_parse's frame - [pc0; r; ra] for ra a return site of pj_parse's parse_value
     call, and on image B [pc0; r; w] for w the cursor end t0 + len or the never-written word at pj_parse's sp + 0 -
     and the universe is the IMAGE's (the S1 owner's P'' answer): its wild arm holds those traces at EVERY word, so no
     text states a membership of either word (parse_noting's two run-word premises are removed with DW). The room
     those wild traces spend is the open COUNT thread (PRH_Base.prh_univ_closure's note; owned by the S1 owner).
  - C-TXTRACE (named gap, tx_put's realloc trace through round_trip_text's record): the Tx part's tx_put takes
    PRH_FnTx.v prhtx_trace at the record on round_trip_text's real stack. ON THE FIXED PINS (the kit owner's census) the
    record is at t = s1 + 0x18 (s1 the `andi sp, sp, -32` sp) and round_trip_text's fake-frame pointer spill moved from
    s1 + 8 to s1 + 0x10, so ra = the word at t - 8 = s1 + 0x10 is that fake-frame pointer again (on the old pins:
    t = s1 + 16, spill at s1 + 8, A 0x84698 / B 0x84bcc), and nfp = the word at t - 16 = s1 + 8 is stack residue. So the
    realloc trace is cf_pc_realloc_ra0 :: pi_ret_tx_realloc :: <the fake-frame ADDRESS> :: ..., a run-time value that
    no entry premise of these texts names. The two short traces ([cf_pc_realloc_ra0] and the pc0-filtered
    prh_trace cf_pc_realloc_ra0 pi_ret_tx_realloc []) are the closure's; the chain part is in the universe through
    the site's wild prefix (A' [0x53c74; 0x84db0], B' [0x53d60; 0x8529c]). C-TXTRACE IS DISCHARGED, NOT OPEN
    (2026-10-30): prhtx_trace is now the STATE-FREE form `inU (as_universe B) (unwind_of_chain cf_pc_realloc_ra0
    ((t, pi_ret_tx_realloc, t) :: ch))` (PRH_FnTx.v:203-209), and clause 4b admits that chain for ANY w and any
    further words, because `inU = length <= 30 /\ (fixed \/ wild_shape)` with `wild_shape = exists p sfx, In p W /\
    t = p ++ sfx`: the fake-frame address and everything after it are the free suffix, and the length side is
    unwind_of_chain_length <= 30. It is the SAME fact as the cursor frees' inU and as round_trip_text's T - one
    mechanism, three consumers - with the S1 owner's tx_trace_inU_A / _B and their negative control as the Qed
    evidence. The tx rows are NOT conditional on the room count: their room premise is their own, guarded by f0 = 0.
   - parse_noting: the brief says it has no plain contract; lib/Prog/parse_noting_c.v exists (plain image, with no
     ran-out arm: under room_run nothing runs out). This text is stated from the source new:499-507 with that file's
     functional content and the ran-out arm added.
   - Fake-stack frames: check_no_overread and check_round_trip take __asan_stack_malloc_3 and set_shadow_f5,
     check_reject_clean_starved and round_trip_text __asan_stack_malloc_1; their subtrees add parse_value's and
     tx_string / put_string's class-0 frames and ex_value's class-1 frames (DOC_D deep at most). Every text whose
     subtree takes frames bounds the frames live at entry by ck_FRAMES_CAP - FR_<fn>, FR_<fn> the frames its subtree
     may hold at once, so a caller's bound implies its callees' (check_no_overread -> parse_noting,
     check_round_trip -> round_trip_text).
   Statements only.
   THE MODEL-RUN POSITION, TWO FAMILIES (PRH_Base.prh_run_at's note, the one home of the rule; the kit owner's ruling
   (A), 2026-10-29). POST-IMPLICATION, no entry position and no entry run premise, the post's arms stating `forall sm
   x os i H0 hist, iface_room_pos .. i .. S -> prh_run_at .. i E -> exists hist', iface_room_pos .. (i + length E)
   .. S'` with E from the outcomes the post binds: tparse_noting_specX (E = the reading's parse_evs under its ok),
   tcheck_no_overread_specX (E = ck_cno_evs of the triple its post binds; the driver-contract owner's late-trip design),
   tpadded_specX and tcheck_as_written_specX (E keyed on their one allocation's own grant). These call only
   post-implication texts (pj_parse, pj_free, the leaves). Their room counts are position-free entry premises
   (PresetRun.pkR along the all-granted list) with the exact live-set post. ENTRY-KEYED, the position
   (PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S, lib/Spec/PresetRoomPos.v, the one home) and
   the text's own list (prh_run_at) at entry, the exact advance in the post: tround_trip_text_specX,
   tcheck_round_trip_specX, tcheck_reject_clean_starved_specX; they may call both families. The bare pair
   `exists rp_i' rp_hist', (rp_i <= rp_i')%nat /\ iface_room_pos .. rp_i' .. rp_hist' S'` is FALSE and no text here
   posts it. (Binder names are rp_* because several texts already bind x and i.)
   THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS; the kit owner's ruling ~18:5xZ): the four
   post-implication texts here also state, under the same run quantifier with the CONSUMER window
   PRH_Base.prh_cons_from, that their allocations GRANTED - padded res <> 0, check_as_written r = 0, parse_noting's
   reading the all-granted one (with no injected failure in its window), and check_no_overread's copies own' = 0,
   which retires the named condition CNO-COPY. check_no_overread's three readings are P1 events (hcons false,
   the model refuses there for real), so they keep their refusals keyed on the triple the post binds.
   *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnTx PRH_FnWriter PRH_FnReader PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
(* the re-hiding move's SRr' (YA0nH) and preset's zone (YGcfRehidePost.RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the pure models these texts state over (image-free, allocator-free) ---- *)

(* the grammar's reading of a text, at the plain strtod model (PjGrammar.v:330-332 at ReaderRes.jr_strtod) *)
Definition ck_read (x : list Z) : option PjTree.jv := PjGrammar.json_read ReaderRes.jr_strtod x.
Definition ck_ncalls (x : list Z) : Z := Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod x).

(* PJ_ALLOC_BOUND (fuzz_preset.c:59-60): 256 n + JSON_DEPTH_MAX * 8 * PJ_SLOT + 4096, PJ_SLOT = 56 + 8 *)
Definition PJ_ALLOC_BOUND (n : Z) : Z := 256 * n + 32 * 8 * 64 + 4096.

(* fuzz_pick (fuzz.h:65-72; plain check_reject_clean_starved_c.v:33-39) *)
Fixpoint ck_djb2 (h : Z) (x : list Z) : Z :=
  match x with
  | [] => h
  | c :: r => ck_djb2 ((33 * h + c) mod 2 ^ 64) r
  end.
Definition ck_pick (x : list Z) (n : Z) : Z := if n =? 0 then 0 else ck_djb2 5381 x mod n.

(* the harness's allocations counted by g_count in check_reject_clean_starved (plain check_reject_clean_starved_c.v
   :45-48): the starved reading fails at its pick-th call; each injected write fails at its pick-th call *)
Definition ck_crcs_growth (x : list Z) (took doc : Z) (t : PjTree.jv) : Z :=
  (if took =? 0 then 0 else ck_pick x took + 1) +
  (if doc =? 0 then 0
   else PjWriteHyp.wcalls t true + ck_pick x (PjWriteHyp.wcalls t true) + 1 +
        PjWriteHyp.wcalls t false + ck_pick x (PjWriteHyp.wcalls t false) + 1).
(* its bound when an allocator refusal may cut a reading or a write short: a cut write makes at most as many
   allocations as a whole one, and the injected write at most as many as the first write made *)
Definition ck_crcs_max (x : list Z) (took doc : Z) (t : PjTree.jv) : Z :=
  (if took =? 0 then 0 else ck_pick x took + 1) +
  (if doc =? 0 then 0 else 2 * PjWriteHyp.wcalls t true + 2 * PjWriteHyp.wcalls t false).

(* the tx_put sizes of rendered() (fuzz_preset.c:444-453; plain round_trip_text_c.v:37) and the rendered text's length *)
Definition ck_rtt_ns (t : PjTree.jv) (p : bool) : list Z := [0] ++ TxModel.tv_calls t p 0 ++ (if p then [1] else []).
Definition ck_tx_len (t : PjTree.jv) (p : bool) : Z := TxModel.zsum (ck_rtt_ns t p).

(* ---- round_trip_text's RUN EVENTS (the position sweep; the rtt102 walk's measurement, read against the #102 source
   fuzz_preset.c:669-711 and the model): pj_write's, rendered()'s tx puts' (the raw realloc, no head), parse_noting's
   reading of the text, free (want), fuzz_free (text), and, when copy is NULL, pj_free (&back) - in THAT order: the
   source frees want AFTER parse_noting (:691-693). It is the model's own list, PresetReqAt.rt_text (writer w_evs,
   rendered r_evs, parse_evs of the text, r_free, w_free) plus the HBulk of back, so check_round_trip's supply is the
   model's round_trip unfolded (ck_rtt_evs_supply) and the per-callee segments are supplied by lib/A/PRH_Supply.v
   (pj_write's list = w_evs, rendered's prhtx_evs 0 0 (ck_rtt_ns t p) = r_evs). pj_free (&back)'s HBulk lists back's
   blocks in pj_free's POST-ORDER, PresetReqAt.fo t (the record model, P8 commit 715ef46e03c; before 16:3xZ
   this read rd_blocks (rt_tr ..), the live list, which the record refuted as pj_free's order). ---- *)
Definition ck_rtt_evs (sm : list Z -> Z * Z) (t : PjTree.jv) (p : bool) (copy : Z) : list PresetReqAt.hev :=
  PresetReqAt.rt_text sm t p ++
  (if copy =? 0 then [PresetReqAt.HBulk (PresetReqAt.fo t)] else []).

(* THE SUPPLY of round_trip_text's premise from check_round_trip's: its first call (pretty 0, copy = &copy, non-NULL)
   takes the first segment of the model's round_trip, its second (pretty 1, NULL) the next *)
Lemma ck_rtt_evs_supply : forall sm x os i t c, c <> 0 ->
  prh_run_at sm x os i (PresetReqAt.round_trip sm t) ->
  prh_run_at sm x os i (ck_rtt_evs sm t false c) /\
  prh_run_at sm x os (i + length (ck_rtt_evs sm t false c))%nat (ck_rtt_evs sm t true 0).
Proof.
  intros sm x os i t c Hc H. unfold PresetReqAt.round_trip in H. unfold ck_rtt_evs.
  rewrite (proj2 (Z.eqb_neq c 0) Hc), Z.eqb_refl, app_nil_r.
  apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in H as [H1 H2]. split; [exact H1|].
  rewrite app_assoc in H2. apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in H2 as [H2 _]. exact H2.
Qed.

(* ---- check_no_overread's RUN EVENTS (#102): the model's call_evs WITHOUT its MAXB guard and WITHOUT call_rest -
   the three padded () copies, the readings made while memory has not run out, the trees' pj_free, the copies' free
   (PresetRun.call_evs, 5ac818ab1fe6:370-387). One home: the list is the model's, cut where check_no_overread returns;
   ck_cno_evs_call is the equation, so a caller's run over call_evs splits into this text's list and call_rest by
   PRH_Base.prh_run_at_app_iff. The triple o1 o2 o0 is the readings' grants (PresetRun.okof); check_no_overread's post
   BINDS it (the driver-contract owner's late-trip design: the caller chooses its run over os ++ [(o1, o2, o0)] after the call). ---- *)
(* the three padded () copies, the head of ck_cno_evs on every arm (ck_cno_evs_copies): the run hypothesis of
   check_no_overread's outcome clause, which needs no reading's grant *)
Definition ck_cno_copies (x : list Z) : list PresetReqAt.hev :=
  [PresetReqAt.HMal (Z.of_nat (length x) + PresetReqAt.FUZZ_PAD); PresetReqAt.HMal (Z.of_nat (length x) + PresetReqAt.FUZZ_PAD);
   PresetReqAt.HMal (Z.of_nat (length x) + PresetReqAt.FUZZ_PAD)].

Definition ck_cno_evs (sm : list Z -> Z * Z) (x : list Z) (o1 o2 o0 : option nat) : list PresetReqAt.hev :=
  let n := Z.of_nat (length x) in
  let C3 := [PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD); PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD);
             PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD)] in
  let F3 := [PresetReqAt.HFr (n + PresetReqAt.FUZZ_PAD); PresetReqAt.HFr (n + PresetReqAt.FUZZ_PAD);
             PresetReqAt.HFr (n + PresetReqAt.FUZZ_PAD)] in
  if PresetRun.ranout sm x o1 then C3 ++ PresetReqAt.parse_evs sm x (PresetRun.okof o1) ++ F3
  else if PresetRun.ranout sm x o2 then
    C3 ++ PresetReqAt.parse_evs sm x (PresetRun.okof o1) ++ PresetReqAt.parse_evs sm x (PresetRun.okof o2) ++
    PresetRun.p1_tfree sm x o1 ++ F3
  else
    C3 ++ PresetReqAt.parse_evs sm x (PresetRun.okof o1) ++ PresetReqAt.parse_evs sm x (PresetRun.okof o2) ++
    PresetReqAt.parse_evs sm x (PresetRun.okof o0) ++
    PresetRun.p1_tfree sm x o1 ++ PresetRun.p1_tfree sm x o2 ++ PresetRun.p1_tfree sm x o0 ++ F3.

(* a reading ran out (the call then ends: check_no_overread returns 1 and LLVMFuzzerTestOneInput returns) *)
Definition ck_cno_ranout (sm : list Z -> Z * Z) (x : list Z) (o1 o2 o0 : option nat) : bool :=
  PresetRun.ranout sm x o1 || PresetRun.ranout sm x o2 || PresetRun.ranout sm x o0.

Lemma ck_cno_evs_call : forall sm x o1 o2 o0, (PresetReqAt.MAXB <? Z.of_nat (length x)) = false ->
  PresetRun.call_evs sm x o1 o2 o0 =
  ck_cno_evs sm x o1 o2 o0 ++ (if ck_cno_ranout sm x o1 o2 o0 then [] else PresetRun.call_rest sm x).
Proof.
  intros sm x o1 o2 o0 H. unfold PresetRun.call_evs, ck_cno_evs, ck_cno_ranout. rewrite H. cbv zeta.
  destruct (PresetRun.ranout sm x o1); cbn [orb]; [rewrite app_nil_r; reflexivity|].
  destruct (PresetRun.ranout sm x o2); cbn [orb]; [rewrite app_nil_r; reflexivity|].
  repeat rewrite <- app_assoc. reflexivity.
Qed.

(* a caller's run over ck_cno_evs .. o1 o2 o0, whatever the triple, starts with the copies (prh_run_at_app_iff then
   gives the outcome clause's run premise) *)
Lemma ck_cno_evs_copies : forall sm x o1 o2 o0, exists rest, ck_cno_evs sm x o1 o2 o0 = ck_cno_copies x ++ rest.
Proof.
  intros sm x o1 o2 o0. unfold ck_cno_evs, ck_cno_copies. cbv zeta.
  destruct (PresetRun.ranout sm x o1); [eexists; reflexivity|].
  destruct (PresetRun.ranout sm x o2); eexists; reflexivity.
Qed.

(* ---- check_reject_clean_starved's RUN EVENTS: the model's own lists (PresetReqAt.v:340-348), the starved reading
   (parse_evs under okk (pick x took), the CHOSEN failure, which makes no event) and, with a tree, the four writes
   (whole, then with the pick-th allocation failing: w_evs / w_free / w_starved). Supplied by LLVMFuzzerTestOneInput's
   walk from PresetRun.call_tail (both branches): ck_crcs_evs_supply below. ---- *)
Definition ck_crcs_evs (sm : list Z -> Z * Z) (tb : list Z) (took doc : Z) (t : PjTree.jv) : list PresetReqAt.hev :=
  PresetReqAt.starved_parse sm tb (Z.to_nat took) ++ (if doc =? 0 then [] else PresetReqAt.starved_writes tb t).

(* THE SUPPLY of check_reject_clean_starved's run premise from LLVMFuzzerTestOneInput's list (row N9's N9-SUPPLY
   census, commit 5432b023703 provenance/N9-SUPPLY/TABLE.md sec. 2, its draft statement taken
   verbatim with the module paths resolved): PresetRun.call_tail is starved_parse on a refused reading, and round_trip
   ++ starved_parse ++ starved_writes ++ [HBulk ..] on an accepted one, so crcs's list is call_tail's (after the round
   trip on the accepted branch), with took = the reading's call count (crcs's own CHOSEN failure, pick; not F1). *)
Lemma ck_crcs_evs_supply : forall sm x os i tb took,
  prh_run_at sm x os i (PresetRun.call_tail sm tb) ->
  took = Z.of_nat (PjGrammar.calls (PresetReqAt.rtr sm [] tb)) ->
  (fst (PjGrammar.jr_run sm tb []) = None -> forall t0, prh_run_at sm x os i (ck_crcs_evs sm tb took 0 t0)) /\
  (forall t doc, fst (PjGrammar.jr_run sm tb []) = Some t -> doc <> 0 ->
     prh_run_at sm x os (i + length (PresetReqAt.round_trip sm t))%nat (ck_crcs_evs sm tb took doc t)).
Proof.
  intros sm x os i tb took H Ht. unfold PresetRun.call_tail in H. unfold ck_crcs_evs. subst took. rewrite Nat2Z.id.
  split.
  - intros HN t0. rewrite HN in H. rewrite Z.eqb_refl, app_nil_r. exact H.
  - intros t doc HS Hd. rewrite HS in H. rewrite (proj2 (Z.eqb_neq doc 0) Hd).
    apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in H as [_ H].
    rewrite app_assoc in H. apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in H as [H _]. exact H.
Qed.

(* check_round_trip's rewrite (fuzz_preset.c:62-63, :638-681; plain check_round_trip_c.v:34-56) *)
Definition ck_MOD_AT : list Z := [109; 111; 100; 105; 102; 105; 101; 100; 65; 116].
Definition ck_STAMP : list Z := [50; 48; 50; 54; 45; 49; 48; 45; 50; 53; 84; 48; 48; 58; 48; 48; 58; 48; 48; 90].
Definition ck_crt_tree (t : PjTree.jv) : PjTree.jv :=
  match t with
  | PjTree.JObj ms => PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP))
  | _ => t
  end.
Definition ck_members (t : PjTree.jv) : Z :=
  match t with PjTree.JObj ms => Z.of_nat (length ms) | _ => 0 end.
(* g_count's growth over check_round_trip: two renderings and read-backs, then for an object pj_string's strdup, cset
   allocations of pj_set (0 when the member exists), the rewrite's write and read-back *)
Definition ck_crt_count (t : PjTree.jv) (cset : Z) : Z :=
  PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) +
  PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t) +
  match t with
  | PjTree.JObj _ => 1 + cset + PjWriteHyp.wcalls (ck_crt_tree t) true + Z.of_nat (PjRoundTrip.tcalls (ck_crt_tree t))
  | _ => 0
  end.

(* ---- allocator steps on each function's longest path, as model expressions (YGcfRoomKeep.v RK_*: malloc one, free one,
   realloc both). No text takes them since room is an invariant (ruling (B)); kept because the H2/H5 walk cited them
   (commit 841830f5dcb, not on this tree: lib/A/Prog/H2CawBase.v:307, H5CrtDefs.v:156-374,
   H5RttDefs.v:143-344, H5RttS1.v:14, H5RttS2.v:35, H5RttS4.v:767) ---- *)
(* a reading of x: pj_parse's own count (lib/A/PRH_FnPj.v prhPj_parse_steps), so its premise follows *)
Definition ck_rk_read (x : list Z) : nat := PRH_FnPj.prhPj_parse_steps x.
(* pj_free of blocks holding at most b bytes: pj_free's own count (PRH_FnPj.v prhPj_fsteps: 3 + 4 per 56 bytes) *)
Definition ck_fsteps_bytes (b : Z) : nat := (RK_free * (3 + 4 * Z.to_nat (b / 56)))%nat.
(* pj_free of a tree a reading of x built: its blocks hold at most the reading's peak *)
Definition ck_rk_freeread (x : list Z) : nat := ck_fsteps_bytes (hpeakR (PRH_FnPj.prhPj_ptrace x)).
(* the read-back of t's text wdoc t p, and pj_free of the tree it builds *)
Definition ck_rk_tread (t : PjTree.jv) (p : bool) : nat := ck_rk_read (WriterValue.wdoc t p).
Definition ck_rk_freet (t : PjTree.jv) (p : bool) : nat := ck_rk_freeread (WriterValue.wdoc t p).
(* a pj_write of t from g_count = c with no injected failure: pj_write's former charge (PRH_FnWriter.v:188-189,
   RK_realloc per grow of the accepting run, prhWriter_ngrow, and the free of its buffer). A run whose g_fail_at is
   reached grows no more after it, and the accepting run's grows do not depend on c, so this covers every pj_write
   call of a text whatever its counters *)
Definition ck_rk_write (c : Z) (t : PjTree.jv) (p : bool) : nat :=
  (RK_realloc * PRH_FnWriter.prhWriter_ngrow (WriterApp.w0 c SIZE_MAXZ) (WriterValue.wdpieces t p) + RK_free)%nat.
(* rendered(): at most a realloc per tx_put call (ck_rtt_ns), and free (want) *)
Definition ck_rk_tx (t : PjTree.jv) (p : bool) : nat := (RK_realloc * length (ck_rtt_ns t p) + RK_free)%nat.
(* parse_noting: its reading *)
Definition ck_rk_parse_noting (x : list Z) : nat := ck_rk_read x.
(* check_no_overread: per copy a malloc, its reading, pj_free of its tree, free of the copy *)
Definition ck_rk_check_no_overread (x : list Z) : nat :=
  (3 * (RK_malloc + ck_rk_read x + ck_rk_freeread x + RK_free))%nat.
(* check_as_written: expected()'s scratch, malloc and free *)
Definition ck_rk_check_as_written : nat := (RK_malloc + RK_free)%nat.
(* check_reject_clean_starved: the starved reading, the four writes, fuzz_free of the two whole texts *)
Definition ck_rk_check_reject_clean_starved (c : Z) (x : list Z) (t : PjTree.jv) : nat :=
  (ck_rk_read x + 2 * ck_rk_write c t true + 2 * ck_rk_write c t false + 2 * RK_free)%nat.
(* round_trip_text from g_count = c: the write, the rendering (the Tx part's former charges: tx_put RK_realloc, tx_value
   RK_realloc per call size, = ck_rtt_ns), free (want), the read-back, fuzz_free (text), pj_free (&back) *)
Definition ck_rk_round_trip_text (c : Z) (t : PjTree.jv) (p : bool) : nat :=
  (ck_rk_write c t p + ck_rk_tx t p + ck_rk_tread t p + RK_free + ck_rk_freet t p)%nat.
(* the compact copy's blocks after pj_set: the read-back's peak, the grown kids / keys (64 cap2 n), the key and the
   stamp *)
Definition ck_copy_bytes (t : PjTree.jv) : Z :=
  hpeakR (PRH_FnPj.prhPj_ptrace (WriterValue.wdoc t false)) + 64 * cap2R (ck_members t) +
  (Z.of_nat (length ck_MOD_AT) + 1) + (Z.of_nat (length ck_STAMP) + 1).
(* g_count after check_round_trip's two round_trip_text (plain check_round_trip_c.v:65-67, crt_cnt1 / crt_cnt2) *)
Definition ck_cnt1 (c : Z) (t : PjTree.jv) : Z := c + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t).
Definition ck_cnt2 (c : Z) (t : PjTree.jv) : Z := ck_cnt1 c t + PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t).
(* check_round_trip from g_count = c: the two round_trip_text, pj_string's strdup, pj_set's charge (PRH_FnPj.v
   tpj_set_specX: pj_free of the object's blocks, two grow reallocs and the key's strdup, pj_free of val), the
   rewrite's write, read-back, fuzz_free (saved) and pj_free (&back), and pj_free (&copy) of the grown copy *)
Definition ck_rk_check_round_trip (c : Z) (t : PjTree.jv) : nat :=
  (ck_rk_round_trip_text c t false + ck_rk_round_trip_text (ck_cnt1 c t) t true + RK_malloc +
   (ck_rk_freet t false + (2 * RK_realloc + RK_malloc) + ck_fsteps_bytes (Z.of_nat (length ck_STAMP) + 1)) +
   ck_rk_write (ck_cnt2 c t + 1) (ck_crt_tree t) true +
   ck_rk_tread (ck_crt_tree t) true + RK_free + ck_rk_freet (ck_crt_tree t) true +
   ck_fsteps_bytes (ck_copy_bytes t))%nat.

(* the fake-stack frames: at most ck_FRAMES_CAP live at once over a check's run (LLVMFuzzerTestOneInput's own, a
   check's own, the subtree's), far below every used class's fs_frames; FR_<fn> is the most frames a function's
   subtree holds at once: parse_value's class-0 frame at each nesting level (pj_parse), ex_value's class-1 frame at
   each level, one class-0 frame of tx_string / put_string (not nested), and each function's own *)
Definition ck_FRAMES_CAP : Z := 64.
Definition FR_pj_parse : Z := Z.of_nat DOC_D + 1.
Definition FR_ex_value : Z := Z.of_nat DOC_D + 1.
Definition FR_parse_noting : Z := FR_pj_parse.
Definition FR_check_no_overread : Z := 1 + FR_parse_noting.
Definition FR_check_as_written : Z := FR_ex_value.
Definition FR_check_reject_clean_starved : Z := 1 + FR_pj_parse.
Definition FR_round_trip_text : Z := 1 + FR_pj_parse.
Definition FR_check_round_trip : Z := 1 + FR_round_trip_text.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* strtod's model assumes round-to-nearest: the entry float state of every text whose function reaches musl strtod *)
Definition ck_frm0 : Prop := frm_zero (@YK11.fp_csr fx).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the realloc call's two traces, code-only (fuzz_realloc holds n in s0: empty chain), in the FIXED part explicitly.
   No text takes it now: prh_univ_closure implies it (prh_univ_closure_lit); kept as a name: the H2/H5 walk's
   citations (lib/A/Prog/H5CrtDefs.v:143, H5RttDefs.v:125) are at commit 841830f5dcb, not on this tree *)
Definition ck_realloc_univ : Prop :=
  In [cf_pc_realloc_ra0] (u_fix (as_universe B)) /\
  In (prh_trace cf_pc_realloc_ra0 pi_ret_realloc []) (u_fix (as_universe B)).

(* inside a fake-stack frame live at entry (frames S) *)
Definition ck_in_frame (ly : alayout) (S : astate) (a n : Z) : Prop :=
  exists cid pos, In (cid, pos) (frames S) /\
    frame_addr ly cid pos <= a /\ a + n <= frame_addr ly cid pos + fs_frame_bytes cid.

(* an out-parameter the function writes: n bytes in a caller's fake frame, writable, addressable (it implies
   pj_parse's out place, PRH_FnReader.v prhReader_at, by its frame arm) *)
Definition ck_out_ok (STK : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (a n : Z) : Prop :=
  ck_in_frame ly S a n /\ wdest_ok B STK ly S W regs mem a n.

(* a struct pj the function reads after calls: in a fake frame of frames S, addressable (it implies pj_write's
   prhWriter_in_frame, tx_value's prhtx_kept, same's / ex_value's prhex_home).
   NAMED FACT F-DEAD (why the REAL-STACK case is not admitted; the B' walker's G9, checked 2026-10-29): the only caller
   handing these texts a doc is LLVMFuzzerTestOneInput, and its fk = 0 arm (doc on the real stack) is UNREACHABLE.
   (1) The frame-area call is made: AR_const_law (alx_const: rd32 (as_uar_cell B) 1; A 0xaa8c0) takes the option
   word's beqz past the real-stack skip. (2) It returns a frame: the engine's aj_stack_malloc_at_x (YGcallSx.v:67,
   S1 commit fd7be1c86ca2) under count_cid 1 (frames S) < fs_frames 1 - at the entry frames S = [], so
   count_cid 1 [] = 0 < 8192 - gives a0 = frame_addr lyc 1 pos with (1, pos) in frames S2. (3) The frame is not 0:
   AR_frames_law_x (alx_frames) gives in_app (frame_addr lyc 1 pos) (fs_frame_bytes 1), and in_app starts with
   4096 <= lo (YG0f.v:277), so the `beqz a0` to the real-stack fallback is not taken. Answered by the H6 walk (its
   binder HF4096, H6_LA.v, a file not on this tree) and a frame-class probe (gdb: 12 of 12 class-1 calls returned a frame, image A). *)
Definition ck_obj_home (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (p : Z) : Prop :=
  p mod 8 = 0 /\ ck_in_frame ly S p 56 /\ range_addressable (aview segs (w_H W) mem) SHADOW_OFF p 56.

(* a tree read by the harness: the plain representation over the ASan view, its blocks harness blocks, each block
   visible to the runtime calls that read it (the Writer part's PRH_FnWriter.v prhWriter_tree_vis = YGcfTreeVis's
   tree_vis_cf, which pj_write asks; it gives tx_value's prhtx_bvis conjunct for conjunct, with no bridge, SINCE
   2026-10-29: prhtx_bvis's ceiling was a block (x + k + 8 <= alloc_ceiling) and is now the granule
   ((x + k + 7) / 8 * 8 <= alloc_ceiling) that tree_vis_cf supplies and the image makes true - a block may end AT
   the ceiling (ARx's alx_blocks in_app bound), so the old form was false of it and this comment was off by one
   granule), the root in a fake frame *)
Definition ck_tree_ok (ly : alayout) (S : astate) (Lam : list (Z * Z)) (W : world segs) (mem : word -> option byte)
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) : Prop :=
  pj_nodeR segs (rdW W mem) (prh_lin Lam) doc t D /\ (forall bk, In bk D -> In bk Lam) /\
  PRH_FnWriter.prhWriter_tree_vis W mem D /\ ck_obj_home ly S W mem doc.

(* the allocator blocks of harness blocks (user address, user size) *)
Definition ck_hblks (D : list (Z * Z)) : list (Z * Z) := map (fun ak => (fst ak - cf_head, snd ak + cf_head)) D.

(* ---- the abort arms' evidence (PRH_Base.v fabort's E): KEPT for the H2/H5 walk's files (header, DEFERRED), though
   no text here has an abort disjunct now ---- *)
(* an allocator call made by this function refused (the class-full NULL): the refusal leaf at request n, ending in
   the abort state's allocator state (no allocator step lies between the refused call and the abort tail) *)
Definition ck_E_null (n : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  exists lyc Sc Hpc Wc regsc memc mdc Wr cr,
    malloc_cf_null_post segs B lyc Sc Hpc Wc regsc memc mdc n (PNull, S') Wr cr.
(* tx_put's realloc refused, at some request *)
Definition ck_E_txnull (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  exists n, ck_E_null n ly' S' Hp' W' regs' mem' md'.
(* a harness allocation (fuzz_malloc / fuzz_realloc, inside a callee) refused: g_ran_out = 1 and no injected failure
   pending (g_fail_at = SIZE_MAX), so the callee's failure was a refusal; g_most and g_own_ran_out are the caller's
   entry values most / own (the allocator wrappers write neither) *)
Definition ck_E_ran (most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  exists Lam' peak' cnt', prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ 1 most own.
(* an abort arm's evidence with the non-primary room of the abort state *)
Definition ck_Ek
  (E : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  room_live_cf S' /\ E ly' S' Hp' W' regs' mem' md'.

(* ---- the live rooms: the SUM of the callee texts' own named rooms at the states they are called (so each callee
   premise follows by arithmetic from the bytes already live), and the largest single requests ---- *)

(* rendered(): tx_put's request, cap = 2 (n + k + 1) (fuzz_preset.c:361-364) *)
Definition TX_req (t : PjTree.jv) (p : bool) : Z := 2 * (ck_tx_len t p + 1).

(* check_no_overread: the three copies of size + FUZZ_PAD bytes, and three readings (pj_parse's room each), whose
   trees are all live at once (plain check_no_overread_c.v:59-69, cno_room) *)
Definition LIVE_check_no_overread (x : list Z) : Z := 3 * (Z.of_nat (length x) + 16) + 3 * PRH_FnPj.LIVE_pj_parse x.
(* check_as_written: expected()'s scratch (plain check_as_written_c.v:64, rf_room (len + 1)); ex_value allocates
   nothing *)
Definition LIVE_check_as_written (size : Z) : Z := size + 1.
(* check_reject_clean_starved: the starved reading, then the writes, pretty and compact (one live at a time) *)
Definition LIVE_check_reject_clean_starved (x : list Z) (t : PjTree.jv) : Z :=
  PRH_FnPj.LIVE_pj_parse x + PRH_FnWriter.LIVE_pj_write t true + PRH_FnWriter.LIVE_pj_write t false.
Definition RQ_crcs (x : list Z) : Z := zmaxl [PRH_FnPj.RQ_pj_parse x; PRH_FnWriter.prhWriter_WMAX].
(* round_trip_text: pj_write's room, the rendering's (the Tx part's LIVE_tx, every tx_put of a run) with the text live,
   and the read-back's (pj_parse of wdoc t p) with both live *)
Definition LIVE_round_trip_text (t : PjTree.jv) (p : bool) : Z :=
  PRH_FnWriter.LIVE_pj_write t p + PRH_FnTx.LIVE_tx + PRH_FnPj.LIVE_pj_parse (WriterValue.wdoc t p).
Definition RQ_rtt (t : PjTree.jv) (p : bool) : Z :=
  zmaxl [PRH_FnWriter.prhWriter_WMAX; TX_req t p; PRH_FnPj.RQ_pj_parse (WriterValue.wdoc t p)].
(* check_round_trip: the two round_trip_text (the compact copy stays live), pj_string's room at the stamp, pj_set's at
   the copy's top object (n members; its room is largest when the slots are full, cap = n), the rewrite's pj_write and
   read-back *)
Definition LIVE_check_round_trip (t : PjTree.jv) : Z :=
  LIVE_round_trip_text t false + LIVE_round_trip_text t true +
  PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
  PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT)) +
  PRH_FnWriter.LIVE_pj_write (ck_crt_tree t) true + PRH_FnPj.LIVE_pj_parse (WriterValue.wdoc (ck_crt_tree t) true).
Definition RQ_crt (t : PjTree.jv) : Z :=
  zmaxl [RQ_rtt t false; RQ_rtt t true; 56 * cap2R (ck_members t); Z.of_nat (length ck_STAMP) + 1;
         PRH_FnPj.RQ_pj_parse (WriterValue.wdoc (ck_crt_tree t) true)].
(* the largest request one pj_write (doc, p) makes: its last buffer, newcap 0 (len + 1), the doubling from 4096 at
   :460-464 (= LIVE_pj_write's cap). NOT prhWriter_WMAX, a whole-family cap of 2 ^ 28 that no per-input g_most
   meets. Used only where a request must be bounded by g_most. *)
Definition RQW (t : PjTree.jv) (p : bool) : Z :=
  WriterSpec.newcap 0 (Z.of_nat (length (WriterValue.wdoc t p)) + 1).
(* the ledger's requests (fuzz_malloc / fuzz_realloc only) of round_trip_text and check_round_trip: the RQ_* above
   less the harness's own (TX_req, tx_put's realloc through noted) and with RQW for the writer *)
Definition RQA_rtt (t : PjTree.jv) (p : bool) : Z := zmaxl [RQW t p; PRH_FnPj.RQ_pj_parse (WriterValue.wdoc t p)].
Definition RQA_crt (t : PjTree.jv) : Z :=
  zmaxl [RQA_rtt t false; RQA_rtt t true; 56 * cap2R (ck_members t); Z.of_nat (length ck_STAMP) + 1;
         RQW (ck_crt_tree t) true; PRH_FnPj.RQ_pj_parse (WriterValue.wdoc (ck_crt_tree t) true)].

(* ---- the texts ---- *)

(* check_bounded_alloc (fuzz_preset.c:511-517; plain check_bounded_alloc_c.v:9-21): held > PJ_ALLOC_BOUND (size) is
   the abort; no call, no store, nothing changes *)
Definition tcheck_bounded_alloc_specX : Prop :=
  forall ly S Hp W regs mem md ch held size Lam peak cnt fail ran most own,
  fpre B ARx STK_check_bounded_alloc ly S Hp W regs mem md ch ->
  getr regs 10 = w64 held -> getr regs 11 = w64 size ->
  0 <= held < 2 ^ 64 -> 0 <= size <= 2 ^ 40 -> held <= PJ_ALLOC_BOUND size ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_check_bounded_alloc) regs mem md)
    (fpostm B ARx SK STK_check_bounded_alloc [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\ (room_live_cf S -> room_live_cf S') /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own)).

(* check_reject_clean (fuzz_preset.c:538-555; plain check_reject_clean_c.v:12-34): rc == 0, a doc not all zero
   (memcmp with the static `empty`, the bcmp interceptor: doc's 56 bytes are read, C-RO for `empty`) and
   fuzz_alloc_live () != live_before are the aborts; rc is an int, sign-extended in a0. Nothing changes. *)
Definition tcheck_reject_clean_specX : Prop :=
  forall ly S Hp W regs mem md ch rc doc live Lam peak cnt fail ran most own,
  fpre B ARx STK_check_reject_clean ly S Hp W regs mem md ch ->
  getr regs 10 = w64 rc -> - 2 ^ 31 <= rc < 2 ^ 31 -> rc <> 0 ->
  (* doc's window is src_rd, which no longer carries a `+ 8` (the kit owner's ruling, the walk controller's N10-PNA): doc
     is the caller's local in its fake frame, not a block, and bcmp reads exactly its 56 bytes; the old `doc + 56 + 8 <=
     alloc_ceiling` was unprovable (a doc in the last 56 bytes of a class-10 fake frame ending at the ceiling), and
     src_rd's own bound is now `doc + 56 <= alloc_ceiling`, which wdest_ok's ceiling gives (PRH_Base.v src_rd). *)
  getr regs 11 = w64 doc -> src_rd W mem doc (repeat 0 56) ->
  getr regs 12 = w64 live -> live = Ledger.lsum Lam ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_check_reject_clean) regs mem md)
    (fpostm B ARx SK STK_check_reject_clean [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\ (room_live_cf S -> room_live_cf S') /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own)).

(* parse_noting (#102's merged source, src-102/new:499-507, as plain parse_noting_c.v:22 also states; the base's :465-476 is
   the FOUR-argument form and no longer describes it):
   live = fuzz_alloc_live (); g_ran_out = 0; rc = pj_parse (text, size, doc); then, when fuzz_alloc_ran_out () (the
   flag read DIRECTLY, new:504), check_reject_clean (rc, doc, live); return rc. The reading's allocation outcomes ok
   are prh_oks from g_ran_out = 0: the one g_fail_at chooses fails and leaves g_ran_out alone, any other fails only
   by refusal, which sets it when the request is at most g_most and raises g_peak in every case (PRH_Base.v
   prh_oks / prh_refused_peak). A reading that ran out is refused (rc = -1, *doc zero, its blocks freed), which is what
   check_reject_clean asks. *doc is the caller's local in its fake frame, so the post is the caller-window form at
   window d with doc in FP. No abort arm.
   WHAT #102 REMOVED, and the measurement that goes with it: the `int *ran_out` fourth parameter. On the pins of
   record (A f0d2e8d4 / B 3b5e1a09) check_no_overread passes a3 = s1 + 0x34 / 0x30 / 0x2c after
   `andi sp, sp, -32; mv s1, sp` (A 0x81cd4 / 0x81cec / 0x81d04, B 0x81dd4 / 0x81dec / 0x81e04). That measurement is
   TRUE OF TODAY'S BINARIES AND FALSE OF THE FIXED ONES: there is no fourth argument and no such store. It is kept
   here, labelled, because the walks on the pins of record still cross those call sites. *)
Definition tparse_noting_specX (CTX0 : list (list Z)) : Prop :=
  forall most own,
  forall ly S Hp W regs mem md ch text (tb : list Z) doc Lam peak cnt fail ran,
  let len := Z.of_nat (length tb) in
  fpre B ARx STK_parse_noting ly S Hp W regs mem md ch ->
  (* the memory is normal at entry: this function's subtree reaches musl strtod (measured on BOTH rebuilt pins:
     strtod's only callers are ex_value and parse_value, and this text's subtree reaches one of them), whose row
     consumes it, and nothing below supplies it - it is seeded at main and threaded down. Same spelling and same
     reason as tex_value_specX's; see its comment for the suppliers and for the two halves of the route. *)
  YAkMemnorm.memnorm segs mem ->
  prh_univ_closure B CTX0 ->
  (* #102 (src-102/new:499 against the base's :465): parse_noting LOST its `int *ran_out` out-parameter. It now
     takes three arguments, calls check_reject_clean itself when fuzz_alloc_ran_out() (new:504-505) and returns rc.
     The old text bound `ro`, took a3 = ro, put (ro, ro + 4) in the footprint and wrote ran' there; all of that is
     gone. This is a PARAMETER REMOVAL, not a body change - a lane told only "its text changed" would re-read the
     body and find it nearly the same. The ran-out flag now reaches the caller only through the ledger. *)
  getr regs 10 = w64 text -> getr regs 11 = w64 len -> getr regs 12 = w64 doc ->
  len < 2 ^ 40 -> 0 < text -> text + len < 2 ^ 62 ->
  src_rd W mem text tb -> PRH_FnReader.prhReader_home B ly S Hp Lam text len ->
  (* (the cursor end's membership `In (text + len) _` and C-RDWORD's slot-word membership are REMOVED with the
     run-word lists: the closure's clause 4b holds pj_parse's cursor free traces at every word) *)
  Z.of_nat (PjRoundTrip.maxrun tb) < 2 ^ 30 ->
  doc mod 8 = 0 -> ck_out_ok STK_parse_noting ly S W regs mem doc 56 ->
  (* THE FLAG IS CLEAR AT ENTRY (the B' walker's measurement on the merged source; the kit owner's ruling (3)): the new
     body NO LONGER RESETS g_ran_out. The base had `fuzz_alloc_ran_out_reset (); rc = pj_parse (..)` (base:470-471);
     new:499-507 has no reset, which moved to one call per input at the entry (new:809). So the post's count FROM 0
     below is false without this premise: with ran = 1 at entry and rc = 0 the inner check_reject_clean aborts
     (new:599-600). All six call sites give it (new:531 / :533 / :535 guards, :811 -> :817, :675 before :691, :731
     guard), so the premise costs no caller anything. *)
  ran = 0 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> cnt + 2 * len + 2 < 2 ^ 64 - 1 ->
  blocks_bytes S + PRH_FnPj.LIVE_pj_parse tb <= LIVE_MAX -> PRH_FnPj.RQ_pj_parse tb + cf_head < cf_malloc_max ->
  (* THE REQUESTS ARE WITHIN g_most (the kit owner's batch order, ~19:5xZ; the form crcs and check_no_overread already
     take, PRH_FnCheck): every allocator request of the reading is at most g_most, so a refusal there sets g_ran_out
     (prh_alloc_post's RAN' = if n <=? most then 1 else ran), which is what the reading's refusal arms state *)
  PRH_FnPj.RQ_pj_parse tb <= most ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_parse_noting -> ck_frm0 ->
  room_live_cf S ->
  (* THE WILD BUDGET (the room count of P''; PRH_Base's BUDGETED TWINS and prh_wk): the only wild site in this
     subtree is the pj_parse reading's two cursor frees, so k is prh_wk F_parse_noting = 2 = pi_univ_cur = |CW|,
     and the SET is [] - the callee's CW is paid out of these fresh slots (YCbqGwild.wild_room_set). *)
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot S) ->
  (* THE ROOM COUNTS, position-free (the post-implication form's own premises, the read walk's spelling, the reading
     chain's): the peak of the secondary and the class-24 counts along the ALL-GRANTED events, from S's live set
     (a run with refusals allocates a prefix of it); a caller with the run's position derives them from P8 *)
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tb [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tb [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* THE HULL BUDGET (route (b) of the allocator hull premise; lib/Spec/PresetHullBudget.v,
     PRH_FnAlloc.v's header): the meters leave room for the reading's ALL-GRANTED events, the list the room counts
     above name; pj_parse is paid from it. A caller with no position (check_no_overread) pays it from its own, a
     caller with one from the run's count (lib/A/PresetHullPay.v hull_budget_of_room_pos) *)
  PresetHullBudget.hull_budget S (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.3); fpostFbm is already at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_parse_noting) regs mem md)
    (* PLAIN POST, not the window form (the B' walker's simplification that goes with the parameter removal): only doc
       is written and it lies in the caller's FAKE frame, so no fwin obligation reaches the three callers. *)
    (fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_parse_noting))
      STK_parse_noting [(doc, doc + 56)] regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' =>
       (* THE HULL USE: at most the entry budget's list *)
       PresetHullBudget.hull_used S S' (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) /\
       room_live_cf S' /\ exists Lam' peak' cnt' fail' ran' ok res tr,
       PjGrammar.jr_run ReaderRes.jr_strtod tb ok = (res, tr) /\
       (* THE LIVE SET after, EXACT (the read walk's spelling; PresetRun.pkR_app chains it) *)
       (* CFHEAD-16, NOT GUARDED (the kit owner's ruling D1; the head-size census): rs_live holds the INSTANCE sizes
          (user + cf_head), the model's events HEAD-sized; equal exactly when cf_head = PresetReqAt.HEAD, which the walk
          takes as its Section hypothesis PRH_Base.prh_head16 (reflexivity at CfParams_preset). *)
       Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
         (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetReqAt.parse_evs ReaderRes.jr_strtod tb ok)) /\
       (* THE POSITION (post-implication form, the header): for ANY position of a model run whose next events are this
          reading's events under the outcomes ok it bound - pj_parse's reader events, then pj_free (out) on a refusal
          (PresetReqAt.parse_evs) - the position after them. Exact; the caller chooses the run (its os) at the end. *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
            (H0 : list Z) (hist : list YG00.chunk),
            PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (PresetReqAt.parse_evs ReaderRes.jr_strtod tb ok) ->
            exists hist', PresetRoomPos.iface_room_pos sm x os (i + length ((PresetReqAt.parse_evs ReaderRes.jr_strtod tb ok)))%nat H0 hist' S') /\
       (* THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS): at a model run and position whose next events
          are the ALL-GRANTED reading's (parse_evs .. tb []), every allocation among them a CONSUMER event
          (PRH_Base.prh_cons_from: call_rest's reading, PresetRun.v:361-363, not a P1 reading of check_no_overread),
          with no injected failure in the reading's window, the reading GRANTED: g_ran_out stays 0, the instance's
          reading IS the all-granted one (its result and trace, so res = ck_read tb by the conjunct below, and its
          events), and S' is the position at the GRANTED advance. *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
            (H0 : list Z) (hist : list YG00.chunk),
            PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
            PRH_Base.prh_run_at sm x os i (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) ->
            PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.parse_evs ReaderRes.jr_strtod tb [])) ->
            (fail < cnt \/ cnt + ck_ncalls tb <= fail) ->
            ran' = 0 /\ PjGrammar.jr_run ReaderRes.jr_strtod tb [] = (res, tr) /\
            PresetReqAt.parse_evs ReaderRes.jr_strtod tb ok = PresetReqAt.parse_evs ReaderRes.jr_strtod tb [] /\
            exists hist', PresetRoomPos.iface_room_pos sm x os
              (i + length (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []))%nat H0 hist' S') /\
       prh_oks ok cnt fail (PjGrammar.calls tr) (prh_ev_reqs tr) most 0 ran' /\
       cnt' = cnt + Z.of_nat (PjGrammar.calls tr) /\ ReaderRes.fail_after cnt fail (PjGrammar.calls tr) fail' /\
       (* THE REFUSAL PEAK (#102, PRH_Base.v prh_refused_peak), the live counts read off the granted trace
          PRH_FnPj.prhPj_ptrace tb. COUNTEREXAMPLE to the hpeak term alone: tb the JSON string a (bytes 34 97 34),
          ok = [false], cnt <> fail, Lam = [], peak = 0: fuzz_malloc (2) is refused and g_peak = 2, while
          ReaderRes.hpeak [EFail 2] = 0. *)
       peak' = Z.max (Z.max peak (Ledger.lsum Lam + ReaderRes.hpeak tr))
         (prh_refused_peak ok cnt fail (PjGrammar.calls tr)
            (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds (PRH_FnPj.prhPj_ptrace tb)))) /\
       ReaderRes.hpeak tr <= 224 * len + 16384 /\
       (cnt <= fail < cnt + ck_ncalls tb -> res = None) /\
       (ran' <> 0 -> res = None) /\
       (ran' = 0 -> fail < cnt \/ cnt + ck_ncalls tb <= fail ->
          res = ck_read tb /\ Z.of_nat (PjGrammar.calls tr) = ck_ncalls tb) /\
       bytes_at W' mem' text tb /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own /\
       match res with
       | Some t =>
           getr regs' 10 = w64 0 /\
           exists D, Permutation Lam' (D ++ Lam) /\
             Permutation (map snd D) (map Z.of_nat (ReaderRes.lsz tr)) /\ Z.of_nat (length D) = ReaderRes.nlive tr /\
              (* THE TREE'S BLOCKS, UP TO PERMUTATION, over the reader's OWN list (the kit owner's final ruling ~20:0xZ:
                 the model ties the live set to the run only up to permutation, and the reader's allocation order
                 differs from tblk's pre-order, so no ordered block fact is available at any instance). A tree READ
                 FROM THE INPUT is sized by the reader (a string block by its ESCAPED INPUT
                 SPAN, src/preset_file.c:127, model jr_string:207), so its fact is rd_blocks (rtr sm ok tb), never tblk / fo
                 (the input [ "\u0041" ] gives 23 against tblk's 18); PresetReqAtNoMiss.pj_frees_blocks links it to the free
                 list pj_frees. CFHEAD-16: rd_blocks adds PresetReqAt.HEAD. *)
              (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) D)
                 (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod ok tb))) /\
              (* THE BUILT TREE'S FREE ORDER (the kit owner's batch order ~20:1xZ; the round-trip compare walk / CK consume it): ONLY THE READER'S
                 OWN TEXT knows it - pj_nodeR does not pin an array's cap to the reader's growth policy, so no consumer can
                 rebuild pj_free's order from the block structure. For every depth bound n >= depth t, pj_free's order
                 list F of doc's tree is the model's reader-side free list PresetReqAt.pj_frees (keyed on the reader's own
                 sizes; never fo / tblk here); for a read-back tree the P8 owner's pj_frees_wdoc_t (under pj_wf sm t)
                 then gives fo t. CFHEAD-16: pj_frees carries PresetReqAt.HEAD. *)
              (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
                 exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n doc D F /\
                   map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod ok tb) /\
             (forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) /\
             Permutation (ablocks B ly' S') (ablocks B ly S ++ ck_hblks D) /\
             pj_nodeR segs (rdW W' mem') (prh_lin Lam') doc t D /\
             (* CAP (PRH_Reader.pj_ncapR; pj_parse's Some arm, PRH_FnPj.tpj_parse_specX): every array / object node
                of the accepted tree has header cap = PresetReqAt.ncap of its count, the reader's growth from 0 *)
             pj_ncapR segs (rdW W' mem') doc t
       | None =>
           getr regs' 10 = w64 (-1) /\ Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
           pj_zeroR segs (rdW W' mem') doc
       end)).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tparse_noting_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. tpnP_Q IS the text's post (tpnP_Q_check fails to build if
   the two ever differ); tpnP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition tpnP_ASome (ly : alayout) (S : astate) (tb : list Z) (doc : Z) (Lam : list (Z * Z)) (ly' : alayout) (S' :
    astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) (ok : list
    bool) (tr : list PjGrammar.ev) (t : PjTree.jv) : Prop :=
  getr regs' 10 = w64 0 /\ exists D, Permutation Lam' (D ++ Lam) /\ Permutation (map snd D) (map Z.of_nat
      (ReaderRes.lsz tr)) /\ Z.of_nat (length D) = ReaderRes.nlive tr /\ (cf_head = PresetReqAt.HEAD -> Permutation
      (map (fun b => snd b + cf_head) D) (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod ok tb))) /\
      (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat -> exists F, PRH_PjOrder.pj_foR segs (rdW W'
      mem') (prh_lin Lam') n doc D F /\ map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod ok
      tb) /\ (forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) /\ Permutation (ablocks B
      ly' S') (ablocks B ly S ++ ck_hblks D) /\ pj_nodeR segs (rdW W' mem') (prh_lin Lam') doc t D /\ pj_ncapR segs
      (rdW W' mem') doc t.

Definition tpnP_ANone (ly : alayout) (S : astate) (doc : Z) (Lam : list (Z * Z)) (ly' : alayout) (S' : astate) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) : Prop :=
  getr regs' 10 = w64 (-1) /\ Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\ pj_zeroR segs
      (rdW W' mem') doc.

Definition tpnP_Q (most own : Z) (ly : alayout) (S : astate) (text : Z) (tb : list Z) (doc : Z) (Lam : list (Z * Z))
    (peak cnt fail len : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  PresetHullBudget.hull_used S S' (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) /\ room_live_cf S' /\ exists Lam'
      peak' cnt' fail' ran' ok res tr, PjGrammar.jr_run ReaderRes.jr_strtod tb ok = (res, tr) /\ Permutation
      (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf
      S)) (PresetReqAt.parse_evs ReaderRes.jr_strtod tb ok)) /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os : list
      (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
      PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (PresetReqAt.parse_evs
      ReaderRes.jr_strtod tb ok) -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length
      ((PresetReqAt.parse_evs ReaderRes.jr_strtod tb ok)))%nat H0 hist' S') /\ (forall (sm : list Z -> Z * Z) (x : list
      Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
      PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (PresetReqAt.parse_evs
      ReaderRes.jr_strtod tb []) -> PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.parse_evs ReaderRes.jr_strtod
      tb [])) -> (fail < cnt \/ cnt + ck_ncalls tb <= fail) -> ran' = 0 /\ PjGrammar.jr_run ReaderRes.jr_strtod tb [] =
      (res, tr) /\ PresetReqAt.parse_evs ReaderRes.jr_strtod tb ok = PresetReqAt.parse_evs ReaderRes.jr_strtod tb [] /\
      exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.parse_evs ReaderRes.jr_strtod tb
      []))%nat H0 hist' S') /\ prh_oks ok cnt fail (PjGrammar.calls tr) (prh_ev_reqs tr) most 0 ran' /\ cnt' = cnt +
      Z.of_nat (PjGrammar.calls tr) /\ ReaderRes.fail_after cnt fail (PjGrammar.calls tr) fail' /\ peak' = Z.max (Z.max
      peak (Ledger.lsum Lam + ReaderRes.hpeak tr)) (prh_refused_peak ok cnt fail (PjGrammar.calls tr) (map (Z.add
      (Ledger.lsum Lam)) (prh_ev_helds (PRH_FnPj.prhPj_ptrace tb)))) /\ ReaderRes.hpeak tr <= 224 * len + 16384 /\ (cnt
      <= fail < cnt + ck_ncalls tb -> res = None) /\ (ran' <> 0 -> res = None) /\ (ran' = 0 -> fail < cnt \/ cnt +
      ck_ncalls tb <= fail -> res = ck_read tb /\ Z.of_nat (PjGrammar.calls tr) = ck_ncalls tb) /\ bytes_at W' mem'
      text tb /\ prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own /\ match res with | Some t =>
      tpnP_ASome ly S tb doc Lam ly' S' W' regs' mem' Lam' ok tr t | None => tpnP_ANone ly S doc Lam ly' S' W' regs'
      mem' Lam' end.

Lemma tpnP_Q_check : forall (CTX0 : list (list Z)), tparse_noting_specX CTX0 -> tparse_noting_specX CTX0.
Proof.
  intros CTX0 H. unfold tparse_noting_specX in *.
  cbv zeta in H |- *.
  intros most own ly S Hp W regs mem md ch text tb doc Lam peak cnt fail ran HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9
      HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23 HP24 HP25 HP26.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (tpnP_Q most own ly S text tb doc
      Lam peak cnt fail (Z.of_nat (length tb))) end.
  exact (H most own ly S Hp W regs mem md ch text tb doc Lam peak cnt fail ran HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9
      HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23 HP24 HP25 HP26).
Qed.

Record tpnP_R (most own : Z) (ly : alayout) (S : astate) (text : Z) (tb : list Z) (doc : Z) (Lam : list (Z * Z)) (peak
    cnt fail len : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' :
    word -> option byte) (Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) (ok : list bool) (res : option PjTree.jv)
    (tr : list PjGrammar.ev) : Prop := {
  tpnP_hull : PresetHullBudget.hull_used S S' (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []);
  tpnP_room : room_live_cf S';
  tpnP_run : PjGrammar.jr_run ReaderRes.jr_strtod tb ok = (res, tr);
  tpnP_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
      (YGcfRoom.room_of_cf S)) (PresetReqAt.parse_evs ReaderRes.jr_strtod tb ok));
  tpnP_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
      (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at
      sm x os i (PresetReqAt.parse_evs ReaderRes.jr_strtod tb ok) -> exists hist', PresetRoomPos.iface_room_pos sm x os
      (i + length ((PresetReqAt.parse_evs ReaderRes.jr_strtod tb ok)))%nat H0 hist' S');
  tpnP_outcome : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
      nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
      PRH_Base.prh_run_at sm x os i (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) -> PRH_Base.prh_cons_from sm x os
      i (length (PresetReqAt.parse_evs ReaderRes.jr_strtod tb [])) -> (fail < cnt \/ cnt + ck_ncalls tb <= fail) ->
      ran' = 0 /\ PjGrammar.jr_run ReaderRes.jr_strtod tb [] = (res, tr) /\ PresetReqAt.parse_evs ReaderRes.jr_strtod
      tb ok = PresetReqAt.parse_evs ReaderRes.jr_strtod tb [] /\ exists hist', PresetRoomPos.iface_room_pos sm x os (i
      + length (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []))%nat H0 hist' S');
  tpnP_oks : prh_oks ok cnt fail (PjGrammar.calls tr) (prh_ev_reqs tr) most 0 ran';
  tpnP_cnt : cnt' = cnt + Z.of_nat (PjGrammar.calls tr);
  tpnP_fail : ReaderRes.fail_after cnt fail (PjGrammar.calls tr) fail';
  tpnP_peak : peak' = Z.max (Z.max peak (Ledger.lsum Lam + ReaderRes.hpeak tr)) (prh_refused_peak ok cnt fail
      (PjGrammar.calls tr) (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds (PRH_FnPj.prhPj_ptrace tb))));
  tpnP_hpeak : ReaderRes.hpeak tr <= 224 * len + 16384;
  tpnP_window_none : (cnt <= fail < cnt + ck_ncalls tb -> res = None);
  tpnP_ranout_none : (ran' <> 0 -> res = None);
  tpnP_granted : (ran' = 0 -> fail < cnt \/ cnt + ck_ncalls tb <= fail -> res = ck_read tb /\ Z.of_nat (PjGrammar.calls
      tr) = ck_ncalls tb);
  tpnP_bytes : bytes_at W' mem' text tb;
  tpnP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own;
  tpnP_arm : match res with | Some t => tpnP_ASome ly S tb doc Lam ly' S' W' regs' mem' Lam' ok tr t | None =>
      tpnP_ANone ly S doc Lam ly' S' W' regs' mem' Lam' end }.

Lemma tpnP_R_of : forall (most own : Z) (ly : alayout) (S : astate) (text : Z) (tb : list Z) (doc : Z) (Lam : list (Z *
    Z)) (peak cnt fail len : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model),
  tpnP_Q most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' md' ->
  exists Lam' peak' cnt' fail' ran' ok res tr, tpnP_R most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W'
      regs' mem' Lam' peak' cnt' fail' ran' ok res tr.
Proof.
  intros most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' md' H. destruct H as (H0 & H1 & Lam'
      & peak' & cnt' & fail' & ran' & ok & res & tr & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 &
      H14 & H15 & H16).
  exists Lam', peak', cnt', fail', ran', ok, res, tr.
  exact {| tpnP_hull := H0; tpnP_room := H1; tpnP_run := H2; tpnP_live := H3; tpnP_pos := H4; tpnP_outcome := H5;
      tpnP_oks := H6; tpnP_cnt := H7; tpnP_fail := H8; tpnP_peak := H9; tpnP_hpeak := H10; tpnP_window_none := H11;
      tpnP_ranout_none := H12; tpnP_granted := H13; tpnP_bytes := H14; tpnP_ledger := H15; tpnP_arm := H16 |}.
Qed.

Lemma tpnP_Q_of_R : forall (most own : Z) (ly : alayout) (S : astate) (text : Z) (tb : list Z) (doc : Z) (Lam : list (Z
    * Z)) (peak cnt fail len : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) (Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) (ok : list bool) (res
    : option PjTree.jv) (tr : list PjGrammar.ev),
  tpnP_R most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' Lam' peak' cnt' fail' ran' ok res tr
      ->
  tpnP_Q most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' md'.
Proof.
  intros most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' md' Lam' peak' cnt' fail' ran' ok res
      tr HR.
  refine (conj (tpnP_hull HR) (conj (tpnP_room HR) _)).
  exists Lam', peak', cnt', fail', ran', ok, res, tr.
  exact (conj (tpnP_run HR) (conj (tpnP_live HR) (conj (tpnP_pos HR) (conj (tpnP_outcome HR) (conj (tpnP_oks HR) (conj
      (tpnP_cnt HR) (conj (tpnP_fail HR) (conj (tpnP_peak HR) (conj (tpnP_hpeak HR) (conj (tpnP_window_none HR) (conj
      (tpnP_ranout_none HR) (conj (tpnP_granted HR) (conj (tpnP_bytes HR) (conj (tpnP_ledger HR) (tpnP_arm
      HR))))))))))))))).
Qed.

(* the CONSEQUENTS of tpnP_R's guarded conjuncts, NAMED: each conjunct of an implication's conclusion, read from
   the record through one lemma (a consumer that applies the guard and destructs its conclusion is not broken by the
   next conjunct appended there) *)

Lemma tpnP_outcome_ran : forall (most own : Z) (ly : alayout) (S : astate) (text : Z) (tb : list Z) (doc : Z) (Lam :
    list (Z * Z)) (peak cnt fail len : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap
    5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) (ok : list bool) (res :
    option PjTree.jv) (tr : list PjGrammar.ev),
  tpnP_R most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' Lam' peak' cnt' fail' ran' ok res tr
      ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) -> PRH_Base.prh_cons_from sm x os i (length
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tb [])) -> (fail < cnt \/ cnt + ck_ncalls tb <= fail) ->
  ran' = 0.
Proof.
  intros most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' Lam' peak' cnt' fail' ran' ok res tr
      HR sm x os i H0 hist HP0 HP1 HP2 HP3.
  pose proof (tpnP_outcome HR) as G.
  exact (proj1 (G sm x os i H0 hist HP0 HP1 HP2 HP3)).
Qed.

Lemma tpnP_outcome_run : forall (most own : Z) (ly : alayout) (S : astate) (text : Z) (tb : list Z) (doc : Z) (Lam :
    list (Z * Z)) (peak cnt fail len : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap
    5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) (ok : list bool) (res :
    option PjTree.jv) (tr : list PjGrammar.ev),
  tpnP_R most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' Lam' peak' cnt' fail' ran' ok res tr
      ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) -> PRH_Base.prh_cons_from sm x os i (length
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tb [])) -> (fail < cnt \/ cnt + ck_ncalls tb <= fail) ->
  PjGrammar.jr_run ReaderRes.jr_strtod tb [] = (res, tr).
Proof.
  intros most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' Lam' peak' cnt' fail' ran' ok res tr
      HR sm x os i H0 hist HP0 HP1 HP2 HP3.
  pose proof (tpnP_outcome HR) as G.
  exact (proj1 (proj2 (G sm x os i H0 hist HP0 HP1 HP2 HP3))).
Qed.

Lemma tpnP_outcome_evs : forall (most own : Z) (ly : alayout) (S : astate) (text : Z) (tb : list Z) (doc : Z) (Lam :
    list (Z * Z)) (peak cnt fail len : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap
    5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) (ok : list bool) (res :
    option PjTree.jv) (tr : list PjGrammar.ev),
  tpnP_R most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' Lam' peak' cnt' fail' ran' ok res tr
      ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) -> PRH_Base.prh_cons_from sm x os i (length
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tb [])) -> (fail < cnt \/ cnt + ck_ncalls tb <= fail) ->
  PresetReqAt.parse_evs ReaderRes.jr_strtod tb ok = PresetReqAt.parse_evs ReaderRes.jr_strtod tb [].
Proof.
  intros most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' Lam' peak' cnt' fail' ran' ok res tr
      HR sm x os i H0 hist HP0 HP1 HP2 HP3.
  pose proof (tpnP_outcome HR) as G.
  exact (proj1 (proj2 (proj2 (G sm x os i H0 hist HP0 HP1 HP2 HP3)))).
Qed.

Lemma tpnP_outcome_pos : forall (most own : Z) (ly : alayout) (S : astate) (text : Z) (tb : list Z) (doc : Z) (Lam :
    list (Z * Z)) (peak cnt fail len : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap
    5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) (ok : list bool) (res :
    option PjTree.jv) (tr : list PjGrammar.ev),
  tpnP_R most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' Lam' peak' cnt' fail' ran' ok res tr
      ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) -> PRH_Base.prh_cons_from sm x os i (length
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tb [])) -> (fail < cnt \/ cnt + ck_ncalls tb <= fail) ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []))%nat
      H0 hist' S'.
Proof.
  intros most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' Lam' peak' cnt' fail' ran' ok res tr
      HR sm x os i H0 hist HP0 HP1 HP2 HP3.
  pose proof (tpnP_outcome HR) as G.
  exact (proj2 (proj2 (proj2 (G sm x os i H0 hist HP0 HP1 HP2 HP3)))).
Qed.

Lemma tpnP_granted_read : forall (most own : Z) (ly : alayout) (S : astate) (text : Z) (tb : list Z) (doc : Z) (Lam :
    list (Z * Z)) (peak cnt fail len : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap
    5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) (ok : list bool) (res :
    option PjTree.jv) (tr : list PjGrammar.ev),
  tpnP_R most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' Lam' peak' cnt' fail' ran' ok res tr
      ->
  ran' = 0 -> fail < cnt \/ cnt + ck_ncalls tb <= fail ->
  res = ck_read tb.
Proof.
  intros most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' Lam' peak' cnt' fail' ran' ok res tr
      HR HP0 HP1.
  pose proof (tpnP_granted HR) as G.
  exact (proj1 (G HP0 HP1)).
Qed.

Lemma tpnP_granted_calls : forall (most own : Z) (ly : alayout) (S : astate) (text : Z) (tb : list Z) (doc : Z) (Lam :
    list (Z * Z)) (peak cnt fail len : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap
    5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) (ok : list bool) (res :
    option PjTree.jv) (tr : list PjGrammar.ev),
  tpnP_R most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' Lam' peak' cnt' fail' ran' ok res tr
      ->
  ran' = 0 -> fail < cnt \/ cnt + ck_ncalls tb <= fail ->
  Z.of_nat (PjGrammar.calls tr) = ck_ncalls tb.
Proof.
  intros most own ly S text tb doc Lam peak cnt fail len ly' S' Hp' W' regs' mem' Lam' peak' cnt' fail' ran' ok res tr
      HR HP0 HP1.
  pose proof (tpnP_granted HR) as G.
  exact (proj2 (G HP0 HP1)).
Qed.

Record tpnP_RSome (ly : alayout) (S : astate) (tb : list Z) (doc : Z) (Lam : list (Z * Z)) (ly' : alayout) (S' :
    astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) (ok : list
    bool) (tr : list PjGrammar.ev) (t : PjTree.jv) (D : list (Z * Z)) : Prop := {
  tpnPs_ret : getr regs' 10 = w64 0;
  tpnPs_lam : Permutation Lam' (D ++ Lam);
  tpnPs_sizes : Permutation (map snd D) (map Z.of_nat (ReaderRes.lsz tr));
  tpnPs_nlive : Z.of_nat (length D) = ReaderRes.nlive tr;
  tpnPs_blocks : (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) D) (PresetReqAt.rd_blocks
      (PresetReqAt.rtr ReaderRes.jr_strtod ok tb)));
  tpnPs_freeord : (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat -> exists F, PRH_PjOrder.pj_foR
      segs (rdW W' mem') (prh_lin Lam') n doc D F /\ map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees
      ReaderRes.jr_strtod ok tb);
  tpnPs_fresh : (forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S));
  tpnPs_ablocks : Permutation (ablocks B ly' S') (ablocks B ly S ++ ck_hblks D);
  tpnPs_node : pj_nodeR segs (rdW W' mem') (prh_lin Lam') doc t D;
  tpnPs_ncap : pj_ncapR segs (rdW W' mem') doc t }.

Lemma tpnP_RSome_of : forall (ly : alayout) (S : astate) (tb : list Z) (doc : Z) (Lam : list (Z * Z)) (ly' : alayout)
    (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) (ok :
    list bool) (tr : list PjGrammar.ev) (t : PjTree.jv),
  tpnP_ASome ly S tb doc Lam ly' S' W' regs' mem' Lam' ok tr t ->
  exists D, tpnP_RSome ly S tb doc Lam ly' S' W' regs' mem' Lam' ok tr t D.
Proof.
  intros ly S tb doc Lam ly' S' W' regs' mem' Lam' ok tr t H. destruct H as (H0 & D & H1 & H2 & H3 & H4 & H5 & H6 & H7
      & H8 & H9).
  exists D.
  exact {| tpnPs_ret := H0; tpnPs_lam := H1; tpnPs_sizes := H2; tpnPs_nlive := H3; tpnPs_blocks := H4; tpnPs_freeord :=
      H5; tpnPs_fresh := H6; tpnPs_ablocks := H7; tpnPs_node := H8; tpnPs_ncap := H9 |}.
Qed.

Lemma tpnP_ASome_of_R : forall (ly : alayout) (S : astate) (tb : list Z) (doc : Z) (Lam : list (Z * Z)) (ly' : alayout)
    (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) (ok :
    list bool) (tr : list PjGrammar.ev) (t : PjTree.jv) (D : list (Z * Z)),
  tpnP_RSome ly S tb doc Lam ly' S' W' regs' mem' Lam' ok tr t D ->
  tpnP_ASome ly S tb doc Lam ly' S' W' regs' mem' Lam' ok tr t.
Proof.
  intros ly S tb doc Lam ly' S' W' regs' mem' Lam' ok tr t D HR.
  refine (conj (tpnPs_ret HR) _).
  exists D.
  exact (conj (tpnPs_lam HR) (conj (tpnPs_sizes HR) (conj (tpnPs_nlive HR) (conj (tpnPs_blocks HR) (conj (tpnPs_freeord
      HR) (conj (tpnPs_fresh HR) (conj (tpnPs_ablocks HR) (conj (tpnPs_node HR) (tpnPs_ncap HR))))))))).
Qed.

Record tpnP_RNone (ly : alayout) (S : astate) (doc : Z) (Lam : list (Z * Z)) (ly' : alayout) (S' : astate) (W' : world
    segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) : Prop := {
  tpnPn_ret : getr regs' 10 = w64 (-1);
  tpnPn_lam : Permutation Lam' Lam;
  tpnPn_ablocks : Permutation (ablocks B ly' S') (ablocks B ly S);
  tpnPn_zero : pj_zeroR segs (rdW W' mem') doc }.

Lemma tpnP_RNone_of : forall (ly : alayout) (S : astate) (doc : Z) (Lam : list (Z * Z)) (ly' : alayout) (S' : astate)
    (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)),
  tpnP_ANone ly S doc Lam ly' S' W' regs' mem' Lam' ->
  tpnP_RNone ly S doc Lam ly' S' W' regs' mem' Lam'.
Proof.
  intros ly S doc Lam ly' S' W' regs' mem' Lam' H. destruct H as (H0 & H1 & H2 & H3).
  exact {| tpnPn_ret := H0; tpnPn_lam := H1; tpnPn_ablocks := H2; tpnPn_zero := H3 |}.
Qed.

Lemma tpnP_ANone_of_R : forall (ly : alayout) (S : astate) (doc : Z) (Lam : list (Z * Z)) (ly' : alayout) (S' : astate)
    (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)),
  tpnP_RNone ly S doc Lam ly' S' W' regs' mem' Lam' ->
  tpnP_ANone ly S doc Lam ly' S' W' regs' mem' Lam'.
Proof.
  intros ly S doc Lam ly' S' W' regs' mem' Lam' HR.
  exact (conj (tpnPn_ret HR) (conj (tpnPn_lam HR) (conj (tpnPn_ablocks HR) (tpnPn_zero HR)))).
Qed.

Local Unset Implicit Arguments.

(* check_no_overread (fuzz_preset.c:478-509; plain check_no_overread_c.v:80-106): three padded copies of the input
   (fuzz_copy (data, size, 0, FUZZ_PAD, fill), fuzz.h:21-37: __wrap_malloc (size + 16), memcpy, memset), three
   parse_noting into its own frame (frame_alloc_3), the compares when none ran out, three pj_free, three free, the
   frame released (set_shadow_f5). g_fail_at = SIZE_MAX, so no injected failure; readings may run out (g_ran_out),
   which the harness tolerates, so g_count grows by at most three readings' calls. DEFERRED (fixed harness #102): no
   abort arm for a copy's malloc refused (fuzz.h:27-28; header). *)
Definition tcheck_no_overread_specX (CTX0 : list (list Z)) : Prop :=
  forall ly S Hp W regs mem md ch data (x : list Z) Lam peak cnt ran most,
  let size := Z.of_nat (length x) in
  fpre B ARx STK_check_no_overread ly S Hp W regs mem md ch ->
  (* the memory is normal at entry: this function's subtree reaches musl strtod (measured on BOTH rebuilt pins:
     strtod's only callers are ex_value and parse_value, and this text's subtree reaches one of them), whose row
     consumes it, and nothing below supplies it - it is seeded at main and threaded down. Same spelling and same
     reason as tex_value_specX's; see its comment for the suppliers and for the two halves of the route. *)
  YAkMemnorm.memnorm segs mem ->
  prh_univ_closure B CTX0 -> prh_ctx CTX0 F_check_no_overread (raZ regs :: spine ch) ->
  getr regs 10 = w64 data -> getr regs 11 = w64 size ->
  size <= 3 * 2 ^ 20 ->
  src_rd W mem data x -> (0 < size -> PRH_FnReader.prhReader_home B ly S Hp Lam data size) ->
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 -> cnt < 2 ^ 62 - 2 ^ 30 ->
  (* THE FLAGS ARE CLEAR AT ENTRY (the kit owner's ruling on the third #102 defect, 2026-10-29): g_own_ran_out = 0 and
     g_ran_out = 0, so out_of_memory() is 0 at entry and any 1 at the return comes from THIS call. The only caller, LLVMFuzzerTestOneInput, zeroes g_own_ran_out and resets
     g_ran_out at new:808-809, just before the call at new:811. *)
  ran = 0 ->
  (* EVERY ALLOCATOR REQUEST OF THIS SUBTREE IS WITHIN g_most. A refusal of a request n > g_most sets NO flag
     (merged alloc.c:76-77), so out_of_memory() stays 0 and the property aborts become reachable on a reading or a
     write that was refused. The bound closes that. Its discharge is the P8 owner's lib/Spec/PjReqBound.v (every
     reader request <= PJ_ALLOC_BOUND (|x|)) at g_most = PJ_ALLOC_BOUND (size), set at new:810, not a premise
     restated per caller. The harness itself does not treat a request above the bound as impossible:
     check_bounded_alloc (new:565) tests for it. Only the ledger's requests count (fuzz_malloc / fuzz_realloc):
     the harness's own (noted (malloc ..), tx_put's realloc) are outside alloc.c and set g_own_ran_out instead. *)
  PRH_FnPj.RQ_pj_parse x <= most ->
  blocks_bytes S + LIVE_check_no_overread x <= LIVE_MAX ->
  size + 16 < cf_malloc_max -> PRH_FnPj.RQ_pj_parse x + cf_head < cf_malloc_max ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_no_overread ->
  room_live_cf S -> ck_frm0 ->
  (* THE WILD BUDGET (as parse_noting's): three parse_noting calls (merged fuzz_preset.c:531 / :533 / :535), each
     of 2, so k is prh_wk F_check_no_overread = 6. Its own mallocs and frees are fixed-trace sites (its fp is s0). *)
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_no_overread) (st_depot S) ->
  (* THE ROOM COUNTS, position-free (the post-implication form's own premises, the read walk's spelling, the reading
     chain's): the peak of the secondary and the class-24 counts along the ALL-GRANTED events, from S's live set
     (a run with refusals allocates a prefix of it); a caller with the run's position derives them from P8 *)
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (ck_cno_evs ReaderRes.jr_strtod x None None None)) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (ck_cno_evs ReaderRes.jr_strtod x None None None)) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* THE HULL BUDGET (route (b) of the allocator hull premise; lib/Spec/PresetHullBudget.v,
     PRH_FnAlloc.v's header): the meters leave room for the call's ALL-GRANTED events, the list the room counts
     above name; the copies, the three parse_noting, the pj_free and free calls are paid from it. Its only caller
     (LLVMFuzzerTestOneInput) has the run position and pays it from the run's count (lib/A/PresetHullPay.v
     hull_budget_of_room_pos), so the post states no use *)
  PresetHullBudget.hull_budget S (ck_cno_evs ReaderRes.jr_strtod x None None None) ->
  (* #102 (src-102/new:524 against the base's :478): check_no_overread RETURNS int, "1 when memory ran out, and the
     call ends" (new:523): r = out_of_memory () at new:537, and the frees after it change no flag. So r = 1 exactly
     when g_own_ran_out (a padded copy's NULL, new:512) or g_ran_out is 1 at the return, and r = 0 leaves both 0.
     The three copies come from the new `padded` (out of line on B, inlined on A) rather than fuzz_copy. *)
  (* UNIV-END, CLOSED (it asked the universe for the cursor end of a FRESH buffer this call allocates itself, its
     three padded () copies, src-102/new:531-535): the closure's clause 4b holds the cursor free's trace at every
     word, so pj_parse's text takes no membership of the end and nothing is owed here. *)
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.4); fpostFbm is already at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_check_no_overread) regs mem md)
    (fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_check_no_overread))
      STK_check_no_overread [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\ exists Lam' peak' cnt' ran' own',
       Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
       peak <= peak' /\ cnt <= cnt' <= cnt + 3 * ck_ncalls x /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
       bytes_at W' mem' data x /\
       exists r, getr regs' 10 = w64 r /\
         ((r = 1 /\ (own' = 1 \/ ran' = 1)) \/ (r = 0 /\ own' = 0 /\ ran' = 0)) /\
         (* THE COPIES' OUTCOME, DERIVED (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS; it RETIRES the named
            condition CNO-COPY, which the caller used to discharge): at a model run and position whose next events
            are the three copies (ck_cno_copies; ck_cno_evs_copies gives it from any triple's list), each a CONSUMER
            event (PresetRun.call_cons flags the copies true), no padded () copy was refused, own' = 0. The copies are
            raw mallocs (no alloc.c, so no injected failure) at consumer positions, where P8 and the engine's grant
            exclude the NULL (padded's own outcome clause on image B; the inlined malloc on image A). *)
         (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
            (H0 : list Z) (hist : list YG00.chunk),
            PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at sm x0 os i (ck_cno_copies x) ->
            PRH_Base.prh_cons_from sm x0 os i (length (ck_cno_copies x)) -> own' = 0) /\
         (* THE TRIPLE AND THE POSITION (post-implication form; the driver-contract owner's late-trip design): the post BINDS the three
            readings' grants o1 o2 o0 (each the reading's first refused allocation, None if none), the return value is
            whether one RAN OUT, and for ANY position of a model run whose next events are ck_cno_evs .. o1 o2 o0 the
            position after them - exact. The readings are P1 events (hcons false): the model refuses there for real,
            so their refusals stay keyed on the bound triple and no outcome clause excludes them. Stated when no copy
            was refused (own' = 0), which the clause above derives at every consumer run; a refused copy has no model
            events (PresetRun 5ac818ab1fe6 makes the three copies as GRANTED HMal). *)
         (own' = 0 -> exists o1 o2 o0 : option nat,
            r = (if ck_cno_ranout ReaderRes.jr_strtod x o1 o2 o0 then 1 else 0) /\
            (* THE LIVE SET after, EXACT (the read walk's spelling; PresetRun.pkR_app chains it) *)
            (* CFHEAD-16, NOT GUARDED (the kit owner's ruling D1; the head-size census): rs_live holds the INSTANCE sizes
               (user + cf_head), the model's events HEAD-sized; equal exactly when cf_head = PresetReqAt.HEAD, which the walk
               takes as its Section hypothesis PRH_Base.prh_head16 (reflexivity at CfParams_preset). *)
            Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
              (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (ck_cno_evs ReaderRes.jr_strtod x o1 o2 o0)) /\
            (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
            (H0 : list Z) (hist : list YG00.chunk),
            PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at sm x0 os i (ck_cno_evs ReaderRes.jr_strtod x o1 o2 o0) ->
            exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length (ck_cno_evs ReaderRes.jr_strtod x o1 o2 o0))%nat H0 hist' S')))).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tcheck_no_overread_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. tcnP_Q IS the text's post (tcnP_Q_check fails to build if
   the two ever differ); tcnP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition tcnP_A1 (ran' own' r : Z) : Prop :=
  r = 1 /\ (own' = 1 \/ ran' = 1).

Definition tcnP_A2 (ran' own' r : Z) : Prop :=
  r = 0 /\ own' = 0 /\ ran' = 0.

Definition tcnP_Q (ly : alayout) (S : astate) (data : Z) (x : list Z) (Lam : list (Z * Z)) (peak cnt most : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  room_live_cf S' /\ exists Lam' peak' cnt' ran' own', Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks
      B ly S) /\ peak <= peak' /\ cnt <= cnt' <= cnt + 3 * ck_ncalls x /\ prh_ledger B ly' S' Hp' W' mem' Lam' peak'
      cnt' SIZE_MAXZ ran' most own' /\ bytes_at W' mem' data x /\ exists r, getr regs' 10 = w64 r /\ (tcnP_A1 ran' own'
      r \/ tcnP_A2 ran' own' r) /\ (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat *
      option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x0 os i H0 hist S
      -> PRH_Base.prh_run_at sm x0 os i (ck_cno_copies x) -> PRH_Base.prh_cons_from sm x0 os i (length (ck_cno_copies
      x)) -> own' = 0) /\ (own' = 0 -> exists o1 o2 o0 : option nat, r = (if ck_cno_ranout ReaderRes.jr_strtod x o1 o2
      o0 then 1 else 0) /\ Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from
      (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (ck_cno_evs ReaderRes.jr_strtod x o1 o2 o0)) /\ (forall (sm : list Z
      -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list
      YG00.chunk), PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at sm x0 os i (ck_cno_evs
      ReaderRes.jr_strtod x o1 o2 o0) -> exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length (ck_cno_evs
      ReaderRes.jr_strtod x o1 o2 o0))%nat H0 hist' S')).

Lemma tcnP_Q_check : forall (CTX0 : list (list Z)), tcheck_no_overread_specX CTX0 -> tcheck_no_overread_specX CTX0.
Proof.
  intros CTX0 H. unfold tcheck_no_overread_specX in *.
  cbv zeta in H |- *.
  intros ly S Hp W regs mem md ch data x Lam peak cnt ran most HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12
      HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (tcnP_Q ly S data x Lam peak cnt
      most) end.
  exact (H ly S Hp W regs mem md ch data x Lam peak cnt ran most HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12
      HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22).
Qed.

Record tcnP_R (ly : alayout) (S : astate) (data : Z) (x : list Z) (Lam : list (Z * Z)) (peak cnt most : Z) (ly' :
    alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (Lam' :
    list (Z * Z)) (peak' cnt' ran' own' r : Z) : Prop := {
  tcnP_room : room_live_cf S';
  tcnP_lam : Permutation Lam' Lam;
  tcnP_ablocks : Permutation (ablocks B ly' S') (ablocks B ly S);
  tcnP_peak_le : peak <= peak';
  tcnP_cnt_le : cnt <= cnt' <= cnt + 3 * ck_ncalls x;
  tcnP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own';
  tcnP_bytes : bytes_at W' mem' data x;
  tcnP_ret : getr regs' 10 = w64 r;
  tcnP_arm : (tcnP_A1 ran' own' r \/ tcnP_A2 ran' own' r);
  tcnP_outcome : (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i :
      nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
      PRH_Base.prh_run_at sm x0 os i (ck_cno_copies x) -> PRH_Base.prh_cons_from sm x0 os i (length (ck_cno_copies x))
      -> own' = 0);
  tcnP_reading : (own' = 0 -> exists o1 o2 o0 : option nat, r = (if ck_cno_ranout ReaderRes.jr_strtod x o1 o2 o0 then 1
      else 0) /\ Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
      (YGcfRoom.room_of_cf S)) (ck_cno_evs ReaderRes.jr_strtod x o1 o2 o0)) /\ (forall (sm : list Z -> Z * Z) (x0 :
      list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
      PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at sm x0 os i (ck_cno_evs
      ReaderRes.jr_strtod x o1 o2 o0) -> exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length (ck_cno_evs
      ReaderRes.jr_strtod x o1 o2 o0))%nat H0 hist' S')) }.

Lemma tcnP_R_of : forall (ly : alayout) (S : astate) (data : Z) (x : list Z) (Lam : list (Z * Z)) (peak cnt most : Z)
    (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte)
    (md' : Model),
  tcnP_Q ly S data x Lam peak cnt most ly' S' Hp' W' regs' mem' md' ->
  exists Lam' peak' cnt' ran' own' r, tcnP_R ly S data x Lam peak cnt most ly' S' Hp' W' regs' mem' Lam' peak' cnt'
      ran' own' r.
Proof.
  intros ly S data x Lam peak cnt most ly' S' Hp' W' regs' mem' md' H. destruct H as (H0 & Lam' & peak' & cnt' & ran' &
      own' & H1 & H2 & H3 & H4 & H5 & H6 & r & H7 & H8 & H9 & H10).
  exists Lam', peak', cnt', ran', own', r.
  exact {| tcnP_room := H0; tcnP_lam := H1; tcnP_ablocks := H2; tcnP_peak_le := H3; tcnP_cnt_le := H4; tcnP_ledger :=
      H5; tcnP_bytes := H6; tcnP_ret := H7; tcnP_arm := H8; tcnP_outcome := H9; tcnP_reading := H10 |}.
Qed.

Lemma tcnP_Q_of_R : forall (ly : alayout) (S : astate) (data : Z) (x : list Z) (Lam : list (Z * Z)) (peak cnt most : Z)
    (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte)
    (md' : Model) (Lam' : list (Z * Z)) (peak' cnt' ran' own' r : Z),
  tcnP_R ly S data x Lam peak cnt most ly' S' Hp' W' regs' mem' Lam' peak' cnt' ran' own' r ->
  tcnP_Q ly S data x Lam peak cnt most ly' S' Hp' W' regs' mem' md'.
Proof.
  intros ly S data x Lam peak cnt most ly' S' Hp' W' regs' mem' md' Lam' peak' cnt' ran' own' r HR.
  refine (conj (tcnP_room HR) _).
  exists Lam', peak', cnt', ran', own'.
  refine (conj (tcnP_lam HR) (conj (tcnP_ablocks HR) (conj (tcnP_peak_le HR) (conj (tcnP_cnt_le HR) (conj (tcnP_ledger
      HR) (conj (tcnP_bytes HR) _)))))).
  exists r.
  exact (conj (tcnP_ret HR) (conj (tcnP_arm HR) (conj (tcnP_outcome HR) (tcnP_reading HR)))).
Qed.

Record tcnP_R1 (ran' own' r : Z) : Prop := {
  tcnP1_r1 : r = 1;
  tcnP1_flag : (own' = 1 \/ ran' = 1) }.

Lemma tcnP_R1_of : forall (ran' own' r : Z),
  tcnP_A1 ran' own' r ->
  tcnP_R1 ran' own' r.
Proof.
  intros ran' own' r H. destruct H as (H0 & H1).
  exact {| tcnP1_r1 := H0; tcnP1_flag := H1 |}.
Qed.

Lemma tcnP_A1_of_R : forall (ran' own' r : Z),
  tcnP_R1 ran' own' r ->
  tcnP_A1 ran' own' r.
Proof.
  intros ran' own' r HR.
  exact (conj (tcnP1_r1 HR) (tcnP1_flag HR)).
Qed.

Record tcnP_R2 (ran' own' r : Z) : Prop := {
  tcnP2_r0 : r = 0;
  tcnP2_own0 : own' = 0;
  tcnP2_ran0 : ran' = 0 }.

Lemma tcnP_R2_of : forall (ran' own' r : Z),
  tcnP_A2 ran' own' r ->
  tcnP_R2 ran' own' r.
Proof.
  intros ran' own' r H. destruct H as (H0 & H1 & H2).
  exact {| tcnP2_r0 := H0; tcnP2_own0 := H1; tcnP2_ran0 := H2 |}.
Qed.

Lemma tcnP_A2_of_R : forall (ran' own' r : Z),
  tcnP_R2 ran' own' r ->
  tcnP_A2 ran' own' r.
Proof.
  intros ran' own' r HR.
  exact (conj (tcnP2_r0 HR) (conj (tcnP2_own0 HR) (tcnP2_ran0 HR))).
Qed.

Local Unset Implicit Arguments.

(* check_as_written (fuzz_preset.c:519-536 with expected() :333-349 inlined; plain check_as_written_c.v:52-74):
   want = expected (data, size, rc == 0 ? doc : NULL): a scratch of size + 1 bytes (__wrap_malloc), ex_value, ex_ws,
   free. The aborts: the scratch NULL, (rc == 0) != (want >= 0), and rc == 0 with want != 0. rc and the tree are as
   pj_parse's post leaves them: accepted with the grammar's tree, or refused by the grammar; a reading that ran out
   (g_ran_out = 1) on a text the grammar reads is outside the pre. No harness allocation, so the ledger is unchanged.
   DEFERRED (fixed harness #102): no abort arm for the scratch's malloc refused (:339-340), and the pre NARROWED to
   exclude the reading that ran out on a text the grammar reads (:528-529; header, DEFERRED, :64-67). *)
Definition tcheck_as_written_specX (CTX0 : list (list Z)) : Prop :=
  forall ly S Hp W regs mem md ch data (x : list Z) rc doc t D Lam peak cnt fail ran most,
  let size := Z.of_nat (length x) in
  fpre B ARx STK_check_as_written ly S Hp W regs mem md ch ->
  (* the memory is normal at entry: this function's subtree reaches musl strtod (measured on BOTH rebuilt pins:
     strtod's only callers are ex_value and parse_value, and this text's subtree reaches one of them), whose row
     consumes it, and nothing below supplies it - it is seeded at main and threaded down. Same spelling and same
     reason as tex_value_specX's; see its comment for the suppliers and for the two halves of the route. *)
  YAkMemnorm.memnorm segs mem ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 data -> getr regs 11 = w64 size -> getr regs 12 = w64 rc -> getr regs 13 = w64 doc ->
  - 2 ^ 31 <= rc < 2 ^ 31 -> 0 <= doc < 2 ^ 64 ->
  size <= 3 * 2 ^ 20 -> 0 < data -> data + size < 2 ^ 62 ->
  src_rd W mem data x -> (0 < size -> PRH_FnEx.prhex_inblk B ly S Hp data size) ->
  (rc = 0 /\ ck_read x = Some t \/ rc <> 0 /\ ck_read x = None) ->
  (rc = 0 -> ck_tree_ok ly S Lam W mem doc t D) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most 0 ->
  (* THE FLAGS ARE CLEAR AT ENTRY (the kit owner's ruling on the third #102 defect, 2026-10-29): g_own_ran_out = 0 and
     g_ran_out = 0, so out_of_memory() is 0 at entry and any 1 at the return comes from THIS call. Its only call is new:820, `out_of_memory () || check_as_written (..)`, so it runs only
     when out_of_memory () is 0. No request bound: it makes no ledger request (its scratch is noted (malloc ..)). *)
  ran = 0 ->
  blocks_bytes S + LIVE_check_as_written size <= LIVE_MAX -> size + 1 < cf_malloc_max ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_as_written ->
  room_live_cf S ->
  (* THE ROOM COUNTS (the kit owner's ruling, on the slice walker's measurement; the slice walker carried them as CAW_CNT):
     the scratch's malloc (YGcfRoomLive.RL_malloc_step, 2094cd3ced43:1420, needs rl_sec_ok and rl_b24_ok) and its
     free (RL_free_step :1429, needs rl_b24_ok) keep the post's room_live_cf S' only with these, and room_live_cf S
     alone does not give them (a class-24 malloc may map a NEW batch). The post-implication rewrite dropped the entry
     position that supplied them; the caller derives both from its own position by Spec.PresetRoomCounts'
     counts_of_room_pos. tpadded_specX's wording, so the two swap by conversion. *)
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* THE HULL BUDGET (route (b) of the allocator hull premise; lib/Spec/PresetHullBudget.v): room for
     expected ()'s scratch pair, the raw malloc (size + 1) and its free. Its only caller (LLVMFuzzerTestOneInput,
     new:820) has the run position and pays it from the run's count (lib/A/PresetHullPay.v
     hull_budget_of_room_pos), so the post states no use *)
  PresetHullBudget.hull_budget S [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)] ->
  (* HPOS (the unit owner's ruling D2, 21:54Z, option (a); the shape of the slice walker's
     the internal file CAW-STANDIN-TABLE.md, its HPOS row and closing paragraph): THE RUN POSITION AT ENTRY, whose next event is
     expected ()'s scratch malloc, in a run of at most 4 calls. It is NOT a consequence of the other premises (none
     names a run position). The hull at this call's allocator calls comes from THE HULL BUDGET above, not from it
     (caw_pre_hull with PresetHullPay.hull_ok_of_budget, Caw102A_WA0.v:452-456 / :478-482). The caller supplies it:
     the driver walk of LLVMFuzzerTestOneInput at its check_as_written call (Ent102L3A.v:435 / Ent102L3B.v:446) through
     Ent102OfPost.tcheck_as_written_grantX_of_post (Ent102OfPost.v:650-656), from Ent102GrantA.tcheck_as_written_grantX's
     run, position and `(length rp_os <= 4)%nat` (Ent102GrantA.v:171, :181-184); caw_pre (Caw102A_Base / Caw102B) carries
     it as a conjunct. The text is proved at drv3_check_as_written_A / _B (Ent102DrvTopA3.v:625 / Ent102DrvTopB3.v:479). *)
  (exists (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat)
     (rp_H0 : list Z) (rp_hist : list YG00.chunk),
     (length rp_os <= 4)%nat /\ PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S /\
     PRH_Base.prh_run_at rp_sm rp_x rp_os rp_i [PresetReqAt.HMal (size + 1)]) ->
  ck_frm0 ->
  (* #102 (merged fuzz_preset.c, src-102/new, sha256 c7b4007bba7bab3e, verified against src-102/SHA256SUMS; its :570
     against the base's :519): check_as_written RETURNS int and has a NEW EARLY-RETURN ARM. The harness's own comment
     is "1 when memory ran out, and the call ends": `if (out_of_memory()) return 1;` (new:574) is taken AFTER
     expected(...) has run, so neither abort check runs on that arm; otherwise both run and it returns 0 (new:589).
     The OLD post was the void form with ONE arm and no return conjunct: it is FALSE on the new binary, not merely
     incomplete, because a text's arms are a PARTITION.
     THE CONDITION, now that g_own_ran_out has its generated row (Batch 1): r = out_of_memory () at new:574, and the
     ledger is unchanged (ran stays 0), so r = 1 exactly when expected ()'s scratch was refused (noted, own' = 1). *)
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.5); fpostFm is already at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_check_as_written) regs mem md)
    (fpostFm B ARx SK STK_check_as_written [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
       exists own', prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own' /\
       bytes_at W' mem' data x /\
       exists r, getr regs' 10 = w64 r /\
        (* THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS): at a model run and position whose next events
           are expected ()'s scratch pair, its malloc a CONSUMER event (call_rest), the scratch was GRANTED: r = 0, and
           S' is the position after the pair. A raw __wrap_malloc: no injected failure. *)
        (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
           (H0 : list Z) (hist : list YG00.chunk),
           PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
           PRH_Base.prh_run_at sm x0 os i [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)] ->
           PRH_Base.prh_cons_from sm x0 os i (length [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)]) ->
           r = 0 /\ exists hist', PresetRoomPos.iface_room_pos sm x0 os
             (i + length [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)])%nat H0 hist' S') /\
        (* THE POSITION, KEYED ON THE SCRATCH'S OWN GRANT (the kit owner's fifth order: the list it states is the one
           its own outcome made, not an all-granted list): r = 1, the scratch REFUSED (noted, own' = 1), made no
           event; r = 0 made expected ()'s scratch pair, malloc (size + 1) then free - the model's [HMal (n + 1);
           HFr (n + 1)] of PresetRun.call_rest (PresetRun.v:363: a raw __wrap_malloc, no head). *)
        ((r = 1 /\ own' = 1 /\ (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
           (H0 : list Z) (hist : list YG00.chunk),
           PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at sm x0 os i (@nil PresetReqAt.hev) ->
           exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S')) \/
         (r = 0 /\ own' = 0 /\
          (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at sm x0 os i [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)] ->
          exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)])%nat H0 hist' S') /\
           (rc = 0 -> pj_nodeR segs (rdW W' mem') (prh_lin Lam) doc t D))))).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tcheck_as_written_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. tcaP_Q IS the text's post (tcaP_Q_check fails to build if
   the two ever differ); tcaP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition tcaP_A1 (S S' : astate) (own' r : Z) : Prop :=
  r = 1 /\ own' = 1 /\ (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat))
      (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
      PRH_Base.prh_run_at sm x0 os i (@nil PresetReqAt.hev) -> exists hist', PresetRoomPos.iface_room_pos sm x0 os (i +
      length (@nil PresetReqAt.hev))%nat H0 hist' S').

Definition tcaP_A2 (S : astate) (rc doc : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (size : Z) (S' : astate) (W' :
    world segs) (mem' : word -> option byte) (own' r : Z) : Prop :=
  r = 0 /\ own' = 0 /\ (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat))
      (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
      PRH_Base.prh_run_at sm x0 os i [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)] -> exists hist',
      PresetRoomPos.iface_room_pos sm x0 os (i + length [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)])%nat
      H0 hist' S') /\ (rc = 0 -> pj_nodeR segs (rdW W' mem') (prh_lin Lam) doc t D).

Definition tcaP_Q (ly : alayout) (S : astate) (Hp : list Z) (data : Z) (x : list Z) (rc doc : Z) (t : PjTree.jv) (D Lam
    : list (Z * Z)) (peak cnt fail ran most size : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  room_live_cf S' /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\ exists own', prh_ledger B ly' S' Hp' W' mem' Lam
      peak cnt fail ran most own' /\ bytes_at W' mem' data x /\ exists r, getr regs' 10 = w64 r /\ (forall (sm : list Z
      -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list
      YG00.chunk), PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at sm x0 os i
      [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)] -> PRH_Base.prh_cons_from sm x0 os i (length
      [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)]) -> r = 0 /\ exists hist', PresetRoomPos.iface_room_pos
      sm x0 os (i + length [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)])%nat H0 hist' S') /\ (tcaP_A1 S S'
      own' r \/ tcaP_A2 S rc doc t D Lam size S' W' mem' own' r).

Lemma tcaP_Q_check : forall (CTX0 : list (list Z)), tcheck_as_written_specX CTX0 -> tcheck_as_written_specX CTX0.
Proof.
  intros CTX0 H. unfold tcheck_as_written_specX in *.
  cbv zeta in H |- *.
  intros ly S Hp W regs mem md ch data x rc_ doc t D Lam peak cnt fail ran most HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9
      HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23 HP24 HP25 HP26.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (tcaP_Q ly S Hp data x rc_ doc t D
      Lam peak cnt fail ran most (Z.of_nat (length x))) end.
  exact (H ly S Hp W regs mem md ch data x rc_ doc t D Lam peak cnt fail ran most HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8
      HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23 HP24 HP25 HP26).
Qed.

Record tcaP_R (ly : alayout) (S : astate) (Hp : list Z) (data : Z) (x : list Z) (rc doc : Z) (t : PjTree.jv) (D Lam :
    list (Z * Z)) (peak cnt fail ran most size : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (own' r : Z) : Prop := {
  tcaP_room : room_live_cf S';
  tcaP_hp : Hp' = Hp;
  tcaP_ablocks : ablocks B ly' S' = ablocks B ly S;
  tcaP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own';
  tcaP_bytes : bytes_at W' mem' data x;
  tcaP_ret : getr regs' 10 = w64 r;
  tcaP_outcome : (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i :
      nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
      PRH_Base.prh_run_at sm x0 os i [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)] ->
      PRH_Base.prh_cons_from sm x0 os i (length [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)]) -> r = 0 /\
      exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length [PresetReqAt.HMal (size + 1); PresetReqAt.HFr
      (size + 1)])%nat H0 hist' S');
  tcaP_arm : (tcaP_A1 S S' own' r \/ tcaP_A2 S rc doc t D Lam size S' W' mem' own' r) }.

Lemma tcaP_R_of : forall (ly : alayout) (S : astate) (Hp : list Z) (data : Z) (x : list Z) (rc doc : Z) (t : PjTree.jv)
    (D Lam : list (Z * Z)) (peak cnt fail ran most size : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world
    segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  tcaP_Q ly S Hp data x rc doc t D Lam peak cnt fail ran most size ly' S' Hp' W' regs' mem' md' ->
  exists own' r, tcaP_R ly S Hp data x rc doc t D Lam peak cnt fail ran most size ly' S' Hp' W' regs' mem' own' r.
Proof.
  intros ly S Hp data x rc_ doc t D Lam peak cnt fail ran most size ly' S' Hp' W' regs' mem' md' H. destruct H as (H0 &
      H1 & H2 & own' & H3 & H4 & r & H5 & H6 & H7).
  exists own', r.
  exact {| tcaP_room := H0; tcaP_hp := H1; tcaP_ablocks := H2; tcaP_ledger := H3; tcaP_bytes := H4; tcaP_ret := H5;
      tcaP_outcome := H6; tcaP_arm := H7 |}.
Qed.

Lemma tcaP_Q_of_R : forall (ly : alayout) (S : astate) (Hp : list Z) (data : Z) (x : list Z) (rc doc : Z) (t :
    PjTree.jv) (D Lam : list (Z * Z)) (peak cnt fail ran most size : Z) (ly' : alayout) (S' : astate) (Hp' : list Z)
    (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (own' r : Z),
  tcaP_R ly S Hp data x rc doc t D Lam peak cnt fail ran most size ly' S' Hp' W' regs' mem' own' r ->
  tcaP_Q ly S Hp data x rc doc t D Lam peak cnt fail ran most size ly' S' Hp' W' regs' mem' md'.
Proof.
  intros ly S Hp data x rc_ doc t D Lam peak cnt fail ran most size ly' S' Hp' W' regs' mem' md' own' r HR.
  refine (conj (tcaP_room HR) (conj (tcaP_hp HR) (conj (tcaP_ablocks HR) _))).
  exists own'.
  refine (conj (tcaP_ledger HR) (conj (tcaP_bytes HR) _)).
  exists r.
  exact (conj (tcaP_ret HR) (conj (tcaP_outcome HR) (tcaP_arm HR))).
Qed.

(* the CONSEQUENTS of tcaP_R's guarded conjuncts, NAMED: each conjunct of an implication's conclusion, read from
   the record through one lemma (a consumer that applies the guard and destructs its conclusion is not broken by the
   next conjunct appended there) *)

Lemma tcaP_outcome_ok : forall (ly : alayout) (S : astate) (Hp : list Z) (data : Z) (x : list Z) (rc doc : Z) (t :
    PjTree.jv) (D Lam : list (Z * Z)) (peak cnt fail ran most size : Z) (ly' : alayout) (S' : astate) (Hp' : list Z)
    (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (own' r : Z),
  tcaP_R ly S Hp data x rc doc t D Lam peak cnt fail ran most size ly' S' Hp' W' regs' mem' own' r ->
  forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list
      Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at sm x0 os i
      [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)] -> PRH_Base.prh_cons_from sm x0 os i (length
      [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)]) ->
  r = 0.
Proof.
  intros ly S Hp data x rc_ doc t D Lam peak cnt fail ran most size ly' S' Hp' W' regs' mem' own' r HR sm x0 os i H0
      hist HP0 HP1 HP2.
  pose proof (tcaP_outcome HR) as G.
  exact (proj1 (G sm x0 os i H0 hist HP0 HP1 HP2)).
Qed.

Lemma tcaP_outcome_pos : forall (ly : alayout) (S : astate) (Hp : list Z) (data : Z) (x : list Z) (rc doc : Z) (t :
    PjTree.jv) (D Lam : list (Z * Z)) (peak cnt fail ran most size : Z) (ly' : alayout) (S' : astate) (Hp' : list Z)
    (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (own' r : Z),
  tcaP_R ly S Hp data x rc doc t D Lam peak cnt fail ran most size ly' S' Hp' W' regs' mem' own' r ->
  forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list
      Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at sm x0 os i
      [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)] -> PRH_Base.prh_cons_from sm x0 os i (length
      [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)]) ->
  exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size +
      1)])%nat H0 hist' S'.
Proof.
  intros ly S Hp data x rc_ doc t D Lam peak cnt fail ran most size ly' S' Hp' W' regs' mem' own' r HR sm x0 os i H0
      hist HP0 HP1 HP2.
  pose proof (tcaP_outcome HR) as G.
  exact (proj2 (G sm x0 os i H0 hist HP0 HP1 HP2)).
Qed.

Record tcaP_R1 (S S' : astate) (own' r : Z) : Prop := {
  tcaP1_r1 : r = 1;
  tcaP1_own1 : own' = 1;
  tcaP1_pos : (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
      (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at
      sm x0 os i (@nil PresetReqAt.hev) -> exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length (@nil
      PresetReqAt.hev))%nat H0 hist' S') }.

Lemma tcaP_R1_of : forall (S S' : astate) (own' r : Z),
  tcaP_A1 S S' own' r ->
  tcaP_R1 S S' own' r.
Proof.
  intros S S' own' r H. destruct H as (H0 & H1 & H2).
  exact {| tcaP1_r1 := H0; tcaP1_own1 := H1; tcaP1_pos := H2 |}.
Qed.

Lemma tcaP_A1_of_R : forall (S S' : astate) (own' r : Z),
  tcaP_R1 S S' own' r ->
  tcaP_A1 S S' own' r.
Proof.
  intros S S' own' r HR.
  exact (conj (tcaP1_r1 HR) (conj (tcaP1_own1 HR) (tcaP1_pos HR))).
Qed.

Record tcaP_R2 (S : astate) (rc doc : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (size : Z) (S' : astate) (W' : world
    segs) (mem' : word -> option byte) (own' r : Z) : Prop := {
  tcaP2_r0 : r = 0;
  tcaP2_own0 : own' = 0;
  tcaP2_pos : (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
      (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at
      sm x0 os i [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)] -> exists hist',
      PresetRoomPos.iface_room_pos sm x0 os (i + length [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)])%nat
      H0 hist' S');
  tcaP2_node : (rc = 0 -> pj_nodeR segs (rdW W' mem') (prh_lin Lam) doc t D) }.

Lemma tcaP_R2_of : forall (S : astate) (rc doc : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (size : Z) (S' : astate) (W'
    : world segs) (mem' : word -> option byte) (own' r : Z),
  tcaP_A2 S rc doc t D Lam size S' W' mem' own' r ->
  tcaP_R2 S rc doc t D Lam size S' W' mem' own' r.
Proof.
  intros S rc_ doc t D Lam size S' W' mem' own' r H. destruct H as (H0 & H1 & H2 & H3).
  exact {| tcaP2_r0 := H0; tcaP2_own0 := H1; tcaP2_pos := H2; tcaP2_node := H3 |}.
Qed.

Lemma tcaP_A2_of_R : forall (S : astate) (rc doc : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (size : Z) (S' : astate)
    (W' : world segs) (mem' : word -> option byte) (own' r : Z),
  tcaP_R2 S rc doc t D Lam size S' W' mem' own' r ->
  tcaP_A2 S rc doc t D Lam size S' W' mem' own' r.
Proof.
  intros S rc_ doc t D Lam size S' W' mem' own' r HR.
  exact (conj (tcaP2_r0 HR) (conj (tcaP2_own0 HR) (conj (tcaP2_pos HR) (tcaP2_node HR)))).
Qed.

Local Unset Implicit Arguments.

(* fuzz_pick (fuzz.h:65-72; UNCHANGED by #102 per the internal file CHANGED-FUNCTIONS.md, the source read is
   omx-clap-core fuzz/fuzz.h sha256 ff3c1739a7edfb96): h = 5381, then h = h * 33 + p[i] over the len bytes
   (size_t, so mod 2 ^ 64), and the return `n ? h % n : 0` - which is ck_pick x n above. A LEAF: frame 16, no fake
   frame, no call but the ASan report of its one byte load (an abort path; src_rd's bytes are addressable) and a
   UBSan trap (`unimp` at B 0x84e48: UBSan's POINTER-OVERFLOW check of the byte address, the B' walker's reading at B';
   `0 < p` and `p + len < 2 ^ 62` make it unreachable - not a division-by-zero guard, as this comment said before
   2026-10-29 16:00Z). It writes nothing and allocates
   nothing, so the ledger, the blocks and the input bytes are kept and the post is its value alone.
   IMAGE B ONLY, AS A MEASURED FACT. On image A (asan, pin 1be0f53d, twin bff8519b) fuzz_pick has NO SYMBOL: it is
   inlined into its one caller, check_reject_clean_starved (A 0x8254c-0x825b8, the kit owner's reading). On image B
   (asan-ubsan, pin d663f82d, twin c90d4fa5) it is out of line at 0x84da4, 168 bytes, 42 instructions. Evidence: the
   .symtab of the two unstripped twins (reports/preset-harness/bound-fix/9e1283d1/unstripped/fuzz_preset), from which
   provenance/gen_prh_img.py gives pi_inl F_fuzz_pick = true on A and false on B; fuzz_pick is in the generator's OPT
   list (a function some image inlines), not FNS (the generator exits when an FNS function has no symbol). So on A
   this text has no function to describe and no walk takes it; a walk on A steps through the inlined body inside
   check_reject_clean_starved's own text. This is not an oversight in A's text set.
   ONE CALLER on B (the slice walker's measurement): check_reject_clean_starved, `jal fuzz_pick` at B 0x8250c, the
   compact injected write's pick (new:653 = base:594, source unchanged). Its value is ck_pick, already inside
   ck_crcs_growth / ck_crcs_max, so the caller's post needs no new arm. *)
Definition tfuzz_pick_specX : Prop :=
  forall ly S Hp W regs mem md ch p (x : list Z) n Lam peak cnt fail ran most own,
  let len := Z.of_nat (length x) in
  fpre B ARx STK_fuzz_pick ly S Hp W regs mem md ch ->
  getr regs 10 = w64 p -> getr regs 11 = w64 len -> getr regs 12 = w64 n ->
  0 <= n < 2 ^ 64 -> len <= 3 * 2 ^ 20 -> 0 < p -> p + len < 2 ^ 62 ->
  src_rd W mem p x ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_pick) regs mem md)
    (fpostm B ARx SK STK_fuzz_pick [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       getr regs' 10 = w64 (ck_pick x n) /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       (room_live_cf S -> room_live_cf S') /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       bytes_at W' mem' p x)).

(* padded (merged fuzz_preset.c:509-521; the B' walker's draft, the internal file REWALK-102-PLAN.md D4): b = noted (malloc (size +
   FUZZ_PAD)) through the RAW malloc wrapper (B 0x830d0 `jal 0x53824`; lib/B/Listing_prog.v 8bcc2c9e7809:1680 is
   PCall AS___wrap_malloc), the one fuzz_malloc itself calls (alloc.c:86) - NOT fuzz_malloc. So the block has no head,
   is in neither Lam nor Hp, and alloc.c's statics are untouched on BOTH arms (refused() runs only inside fuzz_malloc):
   the ledger's alloc.c cells and g_most are unchanged. If b <> 0: __asan_memcpy (b, data, size) when
   size <> 0, then __asan_memset (b + size, fill, FUZZ_PAD = 16), which stores fill's low byte. On NULL, noted sets
   g_own_ran_out := 1 (B 0x83114), its one flag write. It returns b.
   IMAGE B ONLY, AS A MEASURED FACT: on image A (pin 1be0f53d, twin bff8519b) padded has NO SYMBOL; it is inlined into
   check_no_overread (1552 bytes on A against 1248 on B; A's three malloc calls 0x81a90 / 0x81ad4 / 0x81b28). Evidence:
   the twins' .symtab (bound-fix/9e1283d1/unstripped/fuzz_preset), from which provenance/gen_prh_img.py gives
   pi_inl F_padded = true on A and false on B; padded is in the generator's OPT list, not FNS. On B it is out of line at
   0x830a8, 148 bytes, 37 instructions; its three callers are check_no_overread's B 0x81b8c / 0x81ba0 / 0x81bb4.
   The UBSan trap at B 0x83138 (b + size wrapping) is refuted from size + FUZZ_PAD < cf_malloc_max through the
   wrapper's post (the block lies below alloc_ceiling).
   THE RUN POSITION: the raw malloc is a run event, HMal (size + FUZZ_PAD) with no head (PresetReqAt.v:30-31), so the
   post keys the advance on it, as the four allocator texts do; a NULL keeps the position. *)
Definition tpadded_specX (CTX0 : list (list Z)) : Prop :=
  forall ly S Hp W regs mem md ch data (x : list Z) fill Lam peak cnt fail ran most own,
  let size := Z.of_nat (length x) in
  fpre B ARx STK_padded ly S Hp W regs mem md ch -> room_live_cf S ->
  prh_univ_closure B CTX0 -> prh_ctx CTX0 F_padded (raZ regs :: spine ch) ->
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* THE HULL BUDGET (route (b) of the allocator hull premise; lib/Spec/PresetHullBudget.v): room for
     the copy's raw malloc (size + FUZZ_PAD); check_no_overread pays it from its own *)
  PresetHullBudget.hull_budget S [PresetReqAt.HMal (size + 16)] ->
  getr regs 10 = w64 data -> getr regs 11 = w64 size -> getr regs 12 = w64 fill -> 0 <= fill < 2 ^ 64 ->
  size <= 3 * 2 ^ 20 -> 0 < data -> data + size < 2 ^ 62 ->
  src_rd W mem data x -> (0 < size -> PRH_FnReader.prhReader_home B ly S Hp Lam data size) ->
  size + 16 < cf_malloc_max -> blocks_bytes S + (size + 16) <= LIVE_MAX ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_padded) regs mem md)
    (fpostm B ARx SK STK_padded [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       exists res own', getr regs' 10 = w64 res /\ room_live_cf S' /\ Hp' = Hp /\
       (* THE HULL USE: at most the entry budget's event *)
       PresetHullBudget.hull_used S S' [PresetReqAt.HMal (size + 16)] /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own' /\ bytes_at W' mem' data x /\
       (* THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS): at a model run and position whose next event
          is the copy's raw malloc, a CONSUMER event (check_no_overread's copies, PresetRun.call_cons), the malloc was
          GRANTED and S' is the position after it. A raw __wrap_malloc: no injected failure. *)
       (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at sm x0 os i [PresetReqAt.HMal (size + 16)] ->
          PRH_Base.prh_cons_from sm x0 os i (length [PresetReqAt.HMal (size + 16)]) ->
          res <> 0 /\
          exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length [PresetReqAt.HMal (size + 16)])%nat H0 hist' S') /\
       ((* P0 REFUSED: NULL, g_own_ran_out := 1, errno 12, nothing else written, no event: the position kept (the
           post-implication form, PRH_FnCheck's header) *)
        (res = 0 /\ own' = 1 /\ ablocks B ly' S' = ablocks B ly S /\
         (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
         (H0 : list Z) (hist : list YG00.chunk),
         PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at sm x0 os i (@nil PresetReqAt.hev) ->
         exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S') /\
         rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\
         (exists ly1 S0 Hp1 W1 regsc memc mdc Wc cc,
            YG0dcf.malloc_cf_null_post segs B ly1 S0 Hp1 W1 regsc memc mdc (size + 16) (PNull, S') Wc cc))
        \/
        (* P1 OK: a fresh RAW block of size + 16 holding x then 16 copies of fill's low byte. ITS END IS AT MOST THE
           CEILING, not 8 below it (the B' padded walk, ruled 16:3xZ): the blocks law gives p + req_size n <=
           alloc_ceiling and in_high admits equality, so `res + size + 16 + 8 <= alloc_ceiling` was unprovable -
           counterexample p = alloc_ceiling - (size + 16) with size mod 16 = 0 meets every law. check_no_overread's
           src_rd at len = size (p + len <= alloc_ceiling, src_rd's ceiling since 2026-10-29) follows. *)
        (res <> 0 /\ own' = own /\ 4096 <= res /\ res + size + 16 <= YM05.alloc_ceiling /\
         ~ In res (map fst (ablocks B ly S)) /\
         Permutation (ablocks B ly' S') ((res, size + 16) :: ablocks B ly S) /\
         (forall a k, In (a, k) Lam -> a - cf_head <> res) /\
         bytes_at W' mem' res (x ++ repeat (fill mod 256) 16) /\
         (forall a, res <= a < res + size + 16 -> writable_at segs (rdW W' mem') a) /\
         range_addressable (aview segs (w_H W') mem') SHADOW_OFF res (size + 16) /\
         shadow_hull_vis (aview segs (w_H W') mem') res (size + 16) /\
         (* its one event, the raw malloc (size + FUZZ_PAD) - the model's copy, one of PresetRun.call_evs's three (PresetRun.v:374) *)
         (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
         (H0 : list Z) (hist : list YG00.chunk),
         PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at sm x0 os i [PresetReqAt.HMal (size + 16)] ->
         exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length [PresetReqAt.HMal (size + 16)])%nat H0 hist' S'))))).

(* fuzz_alloc_most (merged alloc.c:186-189): g_most = n. #102 ONLY: out of line on both fixed pins, 12 bytes (A 0x85e14,
   B 0x862e0; the twins' .symtab); the old pins have no such function. A LEAF: no call, no frame, ONE store - g_most, a
   prh_pst cell and the ledger's most field - and nothing else, so the state, the blocks, the ledger's other cells and
   g_own_ran_out are kept, and the post says so (the journal exempts PST cells, so a cell the post does not state would
   be lost). Its only caller is LLVMFuzzerTestOneInput at new:810 with n = PJ_ALLOC_BOUND (size). It is stated here,
   not beside the other alloc.c accessors in PRH_FnAlloc.v, because PRH_FnAlloc.v was byte-equal between the old-pin
   and the #102 lines when this text was written and the old pins' listing has no AS_fuzz_alloc_most. *)
Definition tfuzz_alloc_most_specX : Prop :=
  forall ly S Hp W regs mem md ch n Lam peak cnt fail ran most own,
  fpre B ARx STK_fuzz_alloc_most ly S Hp W regs mem md ch ->
  getr regs 10 = w64 n -> 0 <= n < 2 ^ 64 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_most) regs mem md)
    (fpostm B ARx SK STK_fuzz_alloc_most [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran n own)).

(* read_members (merged fuzz_preset.c:784-798; byte-for-byte the base's :695-709; UNCHANGED per
   the internal file CHANGED-FUNCTIONS.md, but on the old pins it was inlined into LLVMFuzzerTestOneInput and on BOTH fixed pins
   it is out of line: A 0x825f8, 632 bytes; B 0x82554, 724 bytes). Taken from the leaf-lemma author's draft
   (the draft file read_members_text.v, sha256 1ba0d0cf35a8dcb2), whose header holds the nine call sites and the discharge of
   each callee premise. It looks up, as a consumer does, the members docs/presets.md names: pj_get (doc, "params") and
   (doc, "state"); pj_get_str (doc, k) for the six keys of the static table top; pj_get_str (pj_get (doc, "plugin"),
   "id"); when params is an array, per item pj_get_str (&kids[i], "symbol") and, if that is non-NULL,
   pj_get (&kids[i], "value"); pj_get_str (state, "encoding") and, if that is non-NULL, pj_get_str (state, "bytes").
   Each result only adds to the volatile `seen`, a slot of its own frame; it returns nothing. READS ONLY: FP empty, no
   allocator call, no fake frame (frame 128, no __asan_stack_malloc), so S' = S and the run position is kept with it;
   the ledger and the tree are restated at the same values. g_most and g_own_ran_out are PST cells, which the journal
   does not keep, so the post restates them too: they are fields of the ledger, at their entry values, and the text
   asks no premise of them beyond the ledger.
   THE DRAFT'S GAPS, AS RULED (the kit owner): RM-G1 (cstr_ok of the nine literal keys, their shadow) is the WALK's, by
   the image route in the granule form with the last granule checked explicitly - no premise here, as EX-LIT-SHADOW;
   the route is PRH_Base.cstr_ok_ro with YGcallRoStr.ro_str_check per key (vm_compute);
   RM-G2 (the static `top` table, its shadow and its six pointers) is an image fact - no premise; RM-G3 (the shadow of
   a non-root node handed to a callee) waits on the kit's law for user bytes outside the hidden heads and is carried
   by the walk as ONE named premise until it lands; RM-G4 (F_read_members, AS_read_members, STK_read_members) is
   closed: all three exist on this line. *)
Definition tread_members_specX : Prop :=
  forall ly S Hp W regs mem md ch doc (t : PjTree.jv) D Lam peak cnt fail ran most own,
  fpre B ARx STK_read_members ly S Hp W regs mem md ch ->
  getr regs 10 = w64 doc ->
  pj_nodeR segs (rdW W mem) (prh_lin Lam) doc t D -> PRH_FnPj.prhPj_rslot B STK_read_members ly S W regs mem doc ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_read_members) regs mem md)
    (fpostm B ARx SK STK_read_members [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       (room_live_cf S -> room_live_cf S') /\
       pj_nodeR segs (rdW W' mem') (prh_lin Lam) doc t D)).

(* check_reject_clean_starved (merged fuzz_preset.c:614-665, signature unchanged from base:560-601; plain
   check_reject_clean_starved_c.v:95-130, now the #102 form (its :22)): with took
   readings' allocations, the reading again with the pick-th failing (fuzz_alloc_fail, an INJECTED failure), then
   check_reject_clean; with a tree, pj_write pretty and compact, each written once whole and once with its pick-th
   allocation failing, which must give no text and give its buffer back. g_fail_at is SIZE_MAX at entry and at the
   return. took <= the reading's call count, so the injected failure is reached (the plain text has took = it).
   Allocator refusal (g_ran_out) is TOLERATED, not excluded (header note): no abort arm; g_count grows by at most
   ck_crcs_max, and by exactly ck_crcs_growth when g_ran_out ends 0 (then nothing was refused). *)
Definition tcheck_reject_clean_starved_specX (CTX0 : list (list Z)) : Prop :=
  forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch data (tb : list Z) took doc t D Lam peak cnt ran most,
  let size := Z.of_nat (length tb) in
  fpre B ARx STK_check_reject_clean_starved ly S Hp W regs mem md ch ->
  (* the memory is normal at entry: this function's subtree reaches musl strtod (measured on BOTH rebuilt pins:
     strtod's only callers are ex_value and parse_value, and this text's subtree reaches one of them), whose row
     consumes it, and nothing below supplies it - it is seeded at main and threaded down. Same spelling and same
     reason as tex_value_specX's; see its comment for the suppliers and for the two halves of the route. *)
  YAkMemnorm.memnorm segs mem ->
  prh_univ_closure B CTX0 -> prh_ctx CTX0 F_check_reject_clean_starved (raZ regs :: spine ch) ->
  getr regs 10 = w64 data -> getr regs 11 = w64 size -> getr regs 12 = w64 took -> getr regs 13 = w64 doc ->
  size <= 3 * 2 ^ 20 -> 0 < data -> data + size < 2 ^ 62 ->
  src_rd W mem data tb -> PRH_FnReader.prhReader_home B ly S Hp Lam data size ->
  (* (the cursor end's membership `In (data + size) _` is REMOVED with the run-word lists: clause 4b) *)
  0 <= took <= ck_ncalls tb ->
  (doc = 0 \/
   (ck_read tb = Some t /\ ck_tree_ok ly S Lam W mem doc t D /\
    PjWriteHyp.wlen t false + 1 < 2 ^ 24 /\ PjWriteHyp.wlen t true + 1 < 2 ^ 28 /\ (PjTree.depth t <= 32)%nat)) ->
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 -> cnt < 2 ^ 62 - 2 ^ 30 ->
  (* ITS RUN EVENTS, as an entry premise (ck_crcs_evs: the model's starved reading and starved writes) *)
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (ck_crcs_evs ReaderRes.jr_strtod tb took doc t) ->
  (* THE FLAGS ARE CLEAR AT ENTRY (the kit owner's ruling on the third #102 defect, 2026-10-29): g_own_ran_out = 0 and
     g_ran_out = 0, so out_of_memory() is 0 at entry and any 1 at the return comes from THIS call. Its two calls: new:828 (rc <> 0, after out_of_memory () was 0 at new:820) and new:833
     (after check_round_trip returned 0). Without it the conjunct `ran' = 0 -> cnt' = growth` below is false: with
     g_own_ran_out = 1 at entry, K1 (new:629) returns after the starved reading (the kit owner's reading, case (a)). *)
  ran = 0 ->
  (* EVERY ALLOCATOR REQUEST OF THIS SUBTREE IS WITHIN g_most. A refusal of a request n > g_most sets NO flag
     (merged alloc.c:76-77), so out_of_memory() stays 0 and the property aborts become reachable on a reading or a
     write that was refused. The bound closes that. Its discharge is the P8 owner's lib/Spec/PjReqBound.v (every
     reader request <= PJ_ALLOC_BOUND (|x|)) at g_most = PJ_ALLOC_BOUND (size), set at new:810, not a premise
     restated per caller. The harness itself does not treat a request above the bound as impossible:
     check_bounded_alloc (new:565) tests for it. Only the ledger's requests count (fuzz_malloc / fuzz_realloc):
     the harness's own (noted (malloc ..), tx_put's realloc) are outside alloc.c and set g_own_ran_out instead. *)
  PRH_FnPj.RQ_pj_parse tb <= most ->
  (doc <> 0 -> RQW t true <= most /\ RQW t false <= most) ->
  blocks_bytes S + LIVE_check_reject_clean_starved tb t <= LIVE_MAX ->
  RQ_crcs tb + cf_head < cf_malloc_max ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_reject_clean_starved ->
  room_live_cf S -> PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 rp_hist S -> ck_frm0 ->
  (* THE RUN HAS AT MOST 4 CALLS: A17's prefix bound needs it where this text pays a post-form
     callee's hull budget from its position (lib/A/PresetHullPay.v hull_budget_of_room_pos) *)
  (length rp_os <= 4)%nat ->
  (* THE WILD BUDGET (as parse_noting's): ONE pj_parse (the starved reading, new:625, through 828 or 833, which
     exclude each other), so k is prh_wk F_check_reject_clean_starved = 2. *)
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_reject_clean_starved) (st_depot S) ->
  (* THE ROOM COUNTS of its starved reading (#102 premise-gap sweep, the room-count class): the reading's pj_parse
     (new:625) takes them (PRH_FnPj.tpj_parse_specX, the peaks along the reading's ALL-GRANTED events, for its
     parse_value 0 and its pj_free (out)), and the entry position above cannot give them: this text's run holds only
     the STARVED reading (ck_crcs_evs: parse_evs tb (okk (pick tb took))), a prefix of the all-granted events, so P8
     bounds no count past the injected failure. pj_parse's own spelling at the call (fuzz_alloc_live, fuzz_alloc_fail
     and the fake frame leave the live set as at entry), as check_no_overread and parse_noting take it.
     SUPPLIED (no longer open) by the driver-contract owner's room-count leaf lib/Spec/PresetRoomCounts.v (blob e7bf70e17551,
     commit 146ac6ef7be8; image-free, Print Assumptions closed): on the REFUSED arm
     (new:828; the position after check_no_overread's piece, the reading and the scratch pair) peak_sec_at_tail /
     peak_c24_at_tail, on the ACCEPTED arm (new:833; + round_trip sm t) peak_sec_after_rt / peak_c24_after_rt. Their
     premises: `PresetRun.call_evs sm x o1 o2 o0 = C ++ PresetRun.call_rest sm x`; the three ranout flags false;
     `iface_room_pos sm x (os ++ [(o1, o2, o0)]) (length (hruns sm x os) + length (C ++ parse_evs sm x [] ++
     [HMal (|x| + 1); HFr (|x| + 1)] (++ round_trip sm t)))%nat H0 hist S`; and on the accepted arm
     `fst (PjGrammar.jr_run sm x []) = Some t`. Their conclusions are the two premises below at x = tb (bounds 6,147 <=
     9,524 secondary, 95,331 <= 146,222 class-24). The consumer check is done from the caller's side: the
     LLVMFuzzerTestOneInput walk holds every premise (cut_caw / cut_crt's iface_room_pos, ec_ranout,
     ec_call_evs_ranout_false, ec_rd_ck_read). *)
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tb [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tb [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* THE RUN'S STRTOD MODEL IS KEYED (the unit owner's ruling HP_sm, one of six: tcheck_reject_clean_starved,
     tround_trip_text, tcheck_round_trip, PRH_FnPj's tpj_set and tpj_string, PRH_FnWriter's tpj_write): the events of
     these six are spelled over the reader (here parse_evs, whose number lengths change the trace), so their CONTENT
     fixes the run's strtod model, and each writes ReaderRes.jr_strtod where rp_sm stood - no rp_sm binder, no
     `rp_sm = ReaderRes.jr_strtod` premise. A text carries exactly the constraints its content needs, no more and no
     fewer: the eight writer / tx texts (tput, tindent, tput_string, twrite_value, ttx_put, ttx_string, ttx_line,
     ttx_value) keep rp_sm free. *)
  (* THE CALL'S ALLOCATIONS ARE CONSUMER ALLOCATIONS OF THE RUN (the kit owner's ruling 2026-10-29 ~19:3xZ: the NAMED
     entry premise of the three ENTRY-KEYED check texts). With the entry position and the run premise, P8
     (PresetCfnA.preset_no_refusal; a NULL of malloc_cf is primary-only, YG0dcf.malloc_cf_null_post) and the
     engine's granted paths (PRH_Base.prh_rpost_granted over amreal, YG0d.v:73-92) exclude a REAL refusal at
     every allocation of the call, so the post states the refusal arm DEAD. Supplied by the caller from
     PresetRun.hcons (call_cons flags every event of round_trip / call_tail true; PRH_Base.prh_cons_from_app_iff
     splits the caller's window). *)
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i (length (ck_crcs_evs ReaderRes.jr_strtod tb took doc t)) ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.6); fpostFbm is already at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_check_reject_clean_starved) regs mem md)
    (fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_check_reject_clean_starved))
      STK_check_reject_clean_starved [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\ exists Lam' peak' cnt' ran',
       Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\ peak <= peak' /\
       cnt <= cnt' <= cnt + ck_crcs_max tb took doc t /\ (ran' = ran \/ ran' = 1) /\
       (* NO REFUSAL under prh_cons_from (above): the chosen failures (the picks) leave g_ran_out alone, and a REAL
          refusal is excluded at every allocation, so g_ran_out is unchanged *)
       ran' = ran /\
       (ran' = 0 -> cnt' = cnt + ck_crcs_growth tb took doc t) /\
       (* THE EXACT ADVANCE when nothing was REFUSED (ran' = 0: the chosen failures leave g_ran_out alone and make no
          event in the model too; the requests are within g_most). After a refusal the instance frees blocks the
          model still holds, so no model position exists there: that arm states none (excluded by the driver) *)
       (ran' = 0 -> exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os
          (rp_i + length (ck_crcs_evs ReaderRes.jr_strtod tb took doc t))%nat rp_H0 hist' S') /\
       (* it makes no harness allocation, so nothing sets g_own_ran_out: it stays 0 *)
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most 0 /\
       bytes_at W' mem' data tb /\
       (doc <> 0 -> pj_nodeR segs (rdW W' mem') (prh_lin Lam') doc t D))).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tcheck_reject_clean_starved_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. tcsP_Q IS the text's post (tcsP_Q_check fails to build if
   the two ever differ); tcsP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition tcsP_Q (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z)
    (ly : alayout) (S : astate) (data : Z) (tb : list Z) (took doc : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (peak
    cnt ran most : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  room_live_cf S' /\ exists Lam' peak' cnt' ran', Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly
      S) /\ peak <= peak' /\ cnt <= cnt' <= cnt + ck_crcs_max tb took doc t /\ (ran' = ran \/ ran' = 1) /\ ran' = ran
      /\ (ran' = 0 -> cnt' = cnt + ck_crcs_growth tb took doc t) /\ (ran' = 0 -> exists hist',
      PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os (rp_i + length (ck_crcs_evs ReaderRes.jr_strtod tb
      took doc t))%nat rp_H0 hist' S') /\ prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most 0 /\
      bytes_at W' mem' data tb /\ (doc <> 0 -> pj_nodeR segs (rdW W' mem') (prh_lin Lam') doc t D).

Lemma tcsP_Q_check : forall (CTX0 : list (list Z)), tcheck_reject_clean_starved_specX CTX0 ->
    tcheck_reject_clean_starved_specX CTX0.
Proof.
  intros CTX0 H. unfold tcheck_reject_clean_starved_specX in *.
  cbv zeta in H |- *.
  intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch data tb took doc t D Lam peak cnt ran most HP0 HP1 HP2
      HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23 HP24 HP25 HP26
      HP27 HP28 HP29 HP30 HP31.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (tcsP_Q rp_x rp_os rp_i rp_H0 ly S
      data tb took doc t D Lam peak cnt ran most) end.
  exact (H rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch data tb took doc t D Lam peak cnt ran most HP0 HP1
      HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23 HP24 HP25
      HP26 HP27 HP28 HP29 HP30 HP31).
Qed.

Record tcsP_R (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z) (ly :
    alayout) (S : astate) (data : Z) (tb : list Z) (took doc : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (peak cnt ran
    most : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word ->
    option byte) (Lam' : list (Z * Z)) (peak' cnt' ran' : Z) : Prop := {
  tcsP_room : room_live_cf S';
  tcsP_lam : Permutation Lam' Lam;
  tcsP_ablocks : Permutation (ablocks B ly' S') (ablocks B ly S);
  tcsP_peak_le : peak <= peak';
  tcsP_cnt_le : cnt <= cnt' <= cnt + ck_crcs_max tb took doc t;
  tcsP_ran_or : (ran' = ran \/ ran' = 1);
  tcsP_ran : ran' = ran;
  tcsP_cnt : (ran' = 0 -> cnt' = cnt + ck_crcs_growth tb took doc t);
  tcsP_pos : (ran' = 0 -> exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os (rp_i + length
      (ck_crcs_evs ReaderRes.jr_strtod tb took doc t))%nat rp_H0 hist' S');
  tcsP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most 0;
  tcsP_bytes : bytes_at W' mem' data tb;
  tcsP_node : (doc <> 0 -> pj_nodeR segs (rdW W' mem') (prh_lin Lam') doc t D) }.

Lemma tcsP_R_of : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 :
    list Z) (ly : alayout) (S : astate) (data : Z) (tb : list Z) (took doc : Z) (t : PjTree.jv) (D Lam : list (Z * Z))
    (peak cnt ran most : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem'
    : word -> option byte) (md' : Model),
  tcsP_Q rp_x rp_os rp_i rp_H0 ly S data tb took doc t D Lam peak cnt ran most ly' S' Hp' W' regs' mem' md' ->
  exists Lam' peak' cnt' ran', tcsP_R rp_x rp_os rp_i rp_H0 ly S data tb took doc t D Lam peak cnt ran most ly' S' Hp'
      W' regs' mem' Lam' peak' cnt' ran'.
Proof.
  intros rp_x rp_os rp_i rp_H0 ly S data tb took doc t D Lam peak cnt ran most ly' S' Hp' W' regs' mem' md' H. destruct
      H as (H0 & Lam' & peak' & cnt' & ran' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  exists Lam', peak', cnt', ran'.
  exact {| tcsP_room := H0; tcsP_lam := H1; tcsP_ablocks := H2; tcsP_peak_le := H3; tcsP_cnt_le := H4; tcsP_ran_or :=
      H5; tcsP_ran := H6; tcsP_cnt := H7; tcsP_pos := H8; tcsP_ledger := H9; tcsP_bytes := H10; tcsP_node := H11 |}.
Qed.

Lemma tcsP_Q_of_R : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 :
    list Z) (ly : alayout) (S : astate) (data : Z) (tb : list Z) (took doc : Z) (t : PjTree.jv) (D Lam : list (Z * Z))
    (peak cnt ran most : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem'
    : word -> option byte) (md' : Model) (Lam' : list (Z * Z)) (peak' cnt' ran' : Z),
  tcsP_R rp_x rp_os rp_i rp_H0 ly S data tb took doc t D Lam peak cnt ran most ly' S' Hp' W' regs' mem' Lam' peak' cnt'
      ran' ->
  tcsP_Q rp_x rp_os rp_i rp_H0 ly S data tb took doc t D Lam peak cnt ran most ly' S' Hp' W' regs' mem' md'.
Proof.
  intros rp_x rp_os rp_i rp_H0 ly S data tb took doc t D Lam peak cnt ran most ly' S' Hp' W' regs' mem' md' Lam' peak'
      cnt' ran' HR.
  refine (conj (tcsP_room HR) _).
  exists Lam', peak', cnt', ran'.
  exact (conj (tcsP_lam HR) (conj (tcsP_ablocks HR) (conj (tcsP_peak_le HR) (conj (tcsP_cnt_le HR) (conj (tcsP_ran_or
      HR) (conj (tcsP_ran HR) (conj (tcsP_cnt HR) (conj (tcsP_pos HR) (conj (tcsP_ledger HR) (conj (tcsP_bytes HR)
      (tcsP_node HR))))))))))).
Qed.

Local Unset Implicit Arguments.

(* round_trip_text (fuzz_preset.c:604-635 with rendered() :444-453 inlined; plain round_trip_text_c.v:84-130):
   text = pj_write (doc, pretty), want = rendered (doc, pretty) (tx_put / tx_value on a local struct text), the
   aborts (no text, text != want, the read-back refused, the read-back not the same tree), free (want),
   fuzz_free (text), then *copy = back (memcpy into the caller's frame, C-FRAME) or pj_free (&back). Its own frame
   is frame_alloc_1. g_fail_at = SIZE_MAX, so the property aborts are unreachable. DEFERRED (fixed harness #102): no
   abort arm for pj_write NULL (:612), the read-back refused (:622), or rendered()'s tx_put realloc NULL (header). *)
Definition tround_trip_text_specX (CTX0 : list (list Z)) : Prop :=
  forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch doc pretty copy t D Lam peak cnt ran most,
  let p := negb (pretty =? 0) in
  let FP := if copy =? 0 then [] else [(copy, copy + 56)] in
  fpre B ARx STK_round_trip_text ly S Hp W regs mem md ch ->
  (* the memory is normal at entry: this function's subtree reaches musl strtod (measured on BOTH rebuilt pins:
     strtod's only callers are ex_value and parse_value, and this text's subtree reaches one of them), whose row
     consumes it, and nothing below supplies it - it is seeded at main and threaded down. Same spelling and same
     reason as tex_value_specX's; see its comment for the suppliers and for the two halves of the route. *)
  YAkMemnorm.memnorm segs mem ->
  prh_univ_closure B CTX0 -> prh_ctx CTX0 F_round_trip_text (raZ regs :: spine ch) ->
  getr regs 10 = w64 doc -> getr regs 11 = w64 pretty -> getr regs 12 = w64 copy ->
  (pretty = 0 \/ pretty = 1) ->
  doc <> 0 -> ck_tree_ok ly S Lam W mem doc t D ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod t -> (PjTree.depth t <= 32)%nat -> PjWriteHyp.wlen t p + 1 <= 2 ^ 28 ->
  (copy = 0 \/
   (copy <> 0 /\ copy mod 8 = 0 /\ ck_out_ok STK_round_trip_text ly S W regs mem copy 56 /\
    (copy + 56 <= doc \/ doc + 56 <= copy))) ->
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 -> cnt < 2 ^ 62 ->
  (* ITS RUN EVENTS, as an entry premise (ck_rtt_evs: the model's rt_text, plus back's HBulk when copy is NULL);
     supplied by check_round_trip (ck_rtt_evs_supply) *)
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (ck_rtt_evs ReaderRes.jr_strtod t p copy) ->
  (* THE FLAGS ARE CLEAR AT ENTRY (the kit owner's ruling on the third #102 defect, 2026-10-29): g_own_ran_out = 0 and
     g_ran_out = 0, so out_of_memory() is 0 at entry and any 1 at the return comes from THIS call. Its callers are check_round_trip's two calls (new:776), the second only after
     the first returned 0, and check_round_trip itself runs only after out_of_memory () was 0 (new:820, :832). *)
  ran = 0 ->
  (* EVERY ALLOCATOR REQUEST OF THIS SUBTREE IS WITHIN g_most. A refusal of a request n > g_most sets NO flag
     (merged alloc.c:76-77), so out_of_memory() stays 0 and the property aborts become reachable on a reading or a
     write that was refused. The bound closes that. Its discharge is the P8 owner's lib/Spec/PjReqBound.v (every
     reader request <= PJ_ALLOC_BOUND (|x|)) at g_most = PJ_ALLOC_BOUND (size), set at new:810, not a premise
     restated per caller. The harness itself does not treat a request above the bound as impossible:
     check_bounded_alloc (new:565) tests for it. Only the ledger's requests count (fuzz_malloc / fuzz_realloc):
     the harness's own (noted (malloc ..), tx_put's realloc) are outside alloc.c and set g_own_ran_out instead. *)
  RQA_rtt t p <= most ->
  blocks_bytes S + LIVE_round_trip_text t p <= LIVE_MAX -> RQ_rtt t p + cf_head < cf_malloc_max ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_round_trip_text ->
  room_live_cf S -> PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 rp_hist S -> ck_frm0 ->
  (* THE RUN HAS AT MOST 4 CALLS: A17's prefix bound needs it where this text pays a post-form
     callee's hull budget from its position (lib/A/PresetHullPay.v hull_budget_of_room_pos) *)
  (length rp_os <= 4)%nat ->
  (* THE WILD BUDGET (the room count of P''): two wild sites in this subtree - rendered()'s tx_value run, whose
     grows are at most 30 (the model lemma `length (prhtx_evs 0 0 ks) <= 30`, PRH_FnTx.v; its exact term reaches
     tx_value by YCbqGwild.wild_room_le), and the read-back's parse_noting, which takes 2. So k is
     prh_wk F_round_trip_text = 32 = 30 + 2. *)
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_round_trip_text) (st_depot S) ->
  (* THE RUN'S STRTOD MODEL IS KEYED (HP_sm; tcheck_reject_clean_starved_specX's note): ReaderRes.jr_strtod where
     rp_sm stood *)
  (* THE CALL'S ALLOCATIONS ARE CONSUMER ALLOCATIONS OF THE RUN (the kit owner's ruling 2026-10-29 ~19:3xZ: the NAMED
     entry premise of the three ENTRY-KEYED check texts). With the entry position and the run premise, P8
     (PresetCfnA.preset_no_refusal; a NULL of malloc_cf is primary-only, YG0dcf.malloc_cf_null_post) and the
     engine's granted paths (PRH_Base.prh_rpost_granted over amreal, YG0d.v:73-92) exclude a REAL refusal at
     every allocation of the call, so the post states the refusal arm DEAD. Supplied by the caller from
     PresetRun.hcons (call_cons flags every event of round_trip / call_tail true; PRH_Base.prh_cons_from_app_iff
     splits the caller's window). *)
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i (length (ck_rtt_evs ReaderRes.jr_strtod t p copy)) ->
  (* THE LIVE REAL STACK ABOVE sp (the kit owner's ruling, 2026-10-30 10:58Z; the precedent is tsame_specX's premise at
     this cut, on the S1 owner's engine leaf YGcallStackUp.astack_up_x): rendered()'s tx calls (tx_put, tx_value) ask
     PRH_FnTx.prhtx_trace at the record t = s1 + 24 on this function's frame, whose first half is `forall a,
     t - 16 <= a < ly_top ly -> aview .. <> None`. fpre gives only this function's window [sp - STK, sp), and no
     AR_laws_x field can give [sp, ly_top) (YGcallStackUp.v's header: neither AR nor ARcf reads a real-stack byte).
     NOT GUARDED, unlike tsame_specX's: t lies below sp on every path, so every tx call reads the whole zone.
     Supplied by check_round_trip at its two calls (YGcallStackUp.astack_up_journal_x / astack_up_at_x). *)
  (* THE CALL CHAIN CARRIES IT (the unit owner's ruling, 2026-10-30 09:23Z): the same unguarded conjunct is appended
     last to every text on the caller chain up to the harness entry - tcheck_round_trip_specX below, then
     LLVMFuzzerTestOneInput's slot pre (PresetCfnA.v / PresetCfnB.v preset_lib_pre_x, owned by the driver-contract owner). MET AT THE REAL
     CALL STATE given check_round_trip's own entry fact: the check_round_trip walks prove it at both calls by
     YGcallStackUp.astack_up_at_xwR (lib/A/Prog/Crt102Arms.v:1102-1109, lib/A/Prog/Crt102B_RRT.v:1096-1101). The
     round-trip stack walker's witness and its controls C1 / C2 (RttStackUpA.v / RttStackUpB.v, RttStackUpCtlA.v /
     RttStackUpCtlB.v) are at commit 5208cc4f6eb0, not on this tree (HISTORY). *)
  YGcallStackUp.astack_up_x segs ly W (spZ regs) mem ->
  (* #102 (src-102/new:669 against the base's :604): round_trip_text RETURNS int, "1 when memory ran out, and the
     call ends" (new:668). Same shape as the two check_* rows: the condition on g_own_ran_out is stated through
     the ledger's own' (its generated row, PRH_Img.v:158-159).
     THE r = 1 ARM, from the body: two exits. (i) new:675-680, after pj_write and rendered: free(want),
     fuzz_free(text), return 1. (ii) new:694-695, after the read-back: parse_noting's reading ran out, so parse_noting
     already rejected it cleanly (back zero, its blocks freed). On both, copy is NOT written (the hand-off is after
     new:700), every block the call took is given back (Lam' ~ Lam, the allocator's blocks unchanged), FEWER calls
     ran than the r = 0 count, and g_ran_out may have become 1. So the EXACT count and `ran' = ran` are the r = 0
     arm's only; an earlier wording kept them outside the arm split, which was false on r = 1 (corrected
     2026-10-29). doc is read only, so its tree holds on both arms. *)
  (* UNIV-END, CLOSED (it asked the universe for the cursor end of a FRESH buffer this call allocates itself,
     pj_write's text buffer, src-102/new:691): the closure's clause 4b holds the cursor free's trace at every word, so
     parse_noting's text takes no membership of the end and nothing is owed here. *)
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.7); fpostFbm is already at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_round_trip_text) regs mem md)
    (fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_round_trip_text))
      STK_round_trip_text FP regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\ exists Lam' peak' cnt' ran' own',
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
       peak <= peak' /\
       pj_nodeR segs (rdW W' mem') (prh_lin Lam') doc t D /\
       exists r, getr regs' 10 = w64 r /\
         (* THE r = 1 ARM IS DEAD under prh_cons_from (above): every exit of r = 1 follows a REAL refusal (g_ran_out or
            g_own_ran_out set), and g_fail_at = SIZE_MAX here, so no chosen failure either *)
         r = 0 /\
         ((r = 1 /\ (own' = 1 \/ ran' = 1) /\ Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
           cnt <= cnt' <= cnt + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\
           (* copy is NOT written on this arm (the only write is R0's memcpy, A 0x84ccc), and check_round_trip's C1
              exit pj_frees what must still be the `empty` it zeroed (A 0x82a00 -> 0x82bb0): so its 56 bytes are kept,
              stated, not only said in the comment (the kit owner's Defect 1) *)
           (copy <> 0 -> forall a, copy <= a < copy + 56 -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a)) \/
          (r = 0 /\ own' = 0 /\
           cnt' = cnt + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\ ran' = ran /\
           (* THE EXACT ADVANCE, on the r = 0 arm: no allocation of this call was refused (a refusal sets g_ran_out
              or g_own_ran_out, and the requests are within g_most), so it made its whole list. The r = 1 arm is
              after a REAL refusal, dead under prh_cons_from (r = 0 above), so it states no position. *)
           (exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os (rp_i + length (ck_rtt_evs ReaderRes.jr_strtod t p copy))%nat
              rp_H0 hist' S') /\
           (copy = 0 -> Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S)) /\
           (copy <> 0 ->
              exists Db, Permutation Lam' (Db ++ Lam) /\
                (forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) /\
                Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) /\
               (* THE READ-BACK TREE'S BLOCKS, UP TO PERMUTATION, over the reader's OWN list (the kit owner's final ruling,
                  ~20:0xZ, the fourth correction on this conjunct: the model ties the live set to the run only up to
                  permutation, and the reader's allocation order differs from tblk's pre-order, so no ordered block
                  fact is available at any instance - the P8 owner's vm_compute: for
                  {"a":"x"} rd_blocks = [18; 18; 80; 464] while tblk puts 80, 464 first). back is the reading of
                  pj_write's text of t, x = wdoc t p, granted (r = 0). CFHEAD-16: rd_blocks adds the model's fixed
                  PresetReqAt.HEAD while Db's sizes are user sizes + cf_head, a free CfParams field here, so the guard.
                  A consumer that needs tblk t takes the P8 owner's PresetFreeFo.rd_blocks_wdoc (pj_wf sm t ->
                  Permutation (rd_blocks (rtr sm [] (wdoc t p))) (fo t)) and fo_tblk, both permutations, under this
                  text's own pj_wf premise (owned by the P8 owner). A PERMUTATION SUPPLIES NO pj_free: the next
                  conjunct is the ordered one. *)
               (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) Db)
                  (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod [] (WriterValue.wdoc t p)))) /\
               (* THE READ-BACK TREE'S FREE ORDER (the kit owner's order 2026-10-29; the re-route of the tblk
                  citation above). copy's tree is the reading of x = wdoc t p, all granted (r = 0), so pj_free's
                  order list F of copy carries the model's reader-side list PresetReqAt.pj_frees .. [] (wdoc t p),
                  IN ORDER - the same shape tparse_noting_specX's Some arm states for its own doc, moved to copy by
                  `*copy = back` (new:706-707), which copies the 56-byte header and leaves every block where
                  it is. ITS CONSUMERS: check_round_trip's pj_free (&copy) and its pj_set on copy
                  (PRH_FnPj.tpj_set_specX's ordered entry premise), each through
                  PresetFreeFo.pj_frees_wdoc_t (pj_wf sm t -> pj_frees sm [] (wdoc t p) = fo t, an EQUALITY) and
                  PRH_FnPj.prhPj_free_evs_supply_fo. CFHEAD-16: pj_frees carries PresetReqAt.HEAD. *)
               (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
                  exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') nn copy Db F /\
                    map (fun b => snd b + cf_head) F =
                      PresetReqAt.pj_frees ReaderRes.jr_strtod [] (WriterValue.wdoc t p)) /\
                Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) /\
                Permutation (ablocks B ly' S') (ablocks B ly S ++ ck_hblks Db) /\
                pj_nodeR segs (rdW W' mem') (prh_lin Lam') copy t Db /\
                (* CAP (PRH_Reader.pj_ncapR): copy is the read-back tree back (parse_noting's Some arm over
                   pj_write's text) moved by `*copy = back`, so every array / object node of it has header
                   cap = PresetReqAt.ncap of its count. check_round_trip's pj_set on copy needs it
                   (PRH_FnPj.prhPj_set_evs_supply's cap premise, F6), and the size multiset of Db cannot give it *)
                pj_ncapR segs (rdW W' mem') copy t))))).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tround_trip_text_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. trtP_Q IS the text's post (trtP_Q_check fails to build if
   the two ever differ); trtP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition trtP_A1 (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (copy : Z) (t : PjTree.jv)
    (Lam : list (Z * Z)) (cnt : Z) (p : bool) (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option
    byte) (Lam' : list (Z * Z)) (cnt' ran' own' r : Z) : Prop :=
  r = 1 /\ (own' = 1 \/ ran' = 1) /\ Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\ cnt <=
      cnt' <= cnt + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\ (copy <> 0 -> forall a, copy <= a < copy
      + 56 -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a).

Definition trtP_A2 (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z)
    (ly : alayout) (S : astate) (copy : Z) (t : PjTree.jv) (Lam : list (Z * Z)) (cnt ran : Z) (p : bool) (ly' :
    alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (Lam' : list (Z * Z)) (cnt' ran' own' r : Z)
    : Prop :=
  r = 0 /\ own' = 0 /\ cnt' = cnt + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\ ran' = ran /\ (exists
      hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os (rp_i + length (ck_rtt_evs ReaderRes.jr_strtod
      t p copy))%nat rp_H0 hist' S') /\ (copy = 0 -> Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B
      ly S)) /\ (copy <> 0 -> exists Db, Permutation Lam' (Db ++ Lam) /\ (forall a k, In (a, k) Db -> ~ In (a -
      cf_head, k + cf_head) (ablocks B ly S)) /\ Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz
      (PjRoundTrip.ttrace t))) /\ (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) Db)
      (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod [] (WriterValue.wdoc t p)))) /\ (cf_head =
      PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat -> exists F, PRH_PjOrder.pj_foR segs (rdW W' mem')
      (prh_lin Lam') nn copy Db F /\ map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod []
      (WriterValue.wdoc t p)) /\ Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) /\ Permutation (ablocks
      B ly' S') (ablocks B ly S ++ ck_hblks Db) /\ pj_nodeR segs (rdW W' mem') (prh_lin Lam') copy t Db /\ pj_ncapR
      segs (rdW W' mem') copy t).

Definition trtP_Q (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z)
    (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (doc copy : Z) (t : PjTree.jv) (D Lam :
    list (Z * Z)) (peak cnt ran most : Z) (p : bool) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  room_live_cf S' /\ exists Lam' peak' cnt' ran' own', prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran'
      most own' /\ peak <= peak' /\ pj_nodeR segs (rdW W' mem') (prh_lin Lam') doc t D /\ exists r, getr regs' 10 = w64
      r /\ r = 0 /\ (trtP_A1 ly S W mem copy t Lam cnt p ly' S' W' mem' Lam' cnt' ran' own' r \/ trtP_A2 rp_x rp_os
      rp_i rp_H0 ly S copy t Lam cnt ran p ly' S' W' mem' Lam' cnt' ran' own' r).

Lemma trtP_Q_check : forall (CTX0 : list (list Z)), tround_trip_text_specX CTX0 -> tround_trip_text_specX CTX0.
Proof.
  intros CTX0 H. unfold tround_trip_text_specX in *.
  cbv zeta in H |- *.
  intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc pretty copy t D Lam peak cnt ran most HP0 HP1 HP2
      HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23 HP24 HP25 HP26
      HP27 HP28.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (trtP_Q rp_x rp_os rp_i rp_H0 ly S
      W mem doc copy t D Lam peak cnt ran most (negb (pretty =? 0))) end.
  exact (H rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc pretty copy t D Lam peak cnt ran most HP0 HP1 HP2
      HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23 HP24 HP25 HP26
      HP27 HP28).
Qed.

Record trtP_R (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z) (ly :
    alayout) (S : astate) (W : world segs) (mem : word -> option byte) (doc copy : Z) (t : PjTree.jv) (D Lam : list (Z
    * Z)) (peak cnt ran most : Z) (p : bool) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' :
    bvmap 5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) (peak' cnt' ran' own' r : Z) : Prop := {
  trtP_room : room_live_cf S';
  trtP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own';
  trtP_peak_le : peak <= peak';
  trtP_node : pj_nodeR segs (rdW W' mem') (prh_lin Lam') doc t D;
  trtP_ret : getr regs' 10 = w64 r;
  trtP_r0 : r = 0;
  trtP_arm : (trtP_A1 ly S W mem copy t Lam cnt p ly' S' W' mem' Lam' cnt' ran' own' r \/ trtP_A2 rp_x rp_os rp_i rp_H0
      ly S copy t Lam cnt ran p ly' S' W' mem' Lam' cnt' ran' own' r) }.

Lemma trtP_R_of : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 :
    list Z) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (doc copy : Z) (t : PjTree.jv) (D
    Lam : list (Z * Z)) (peak cnt ran most : Z) (p : bool) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world
    segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  trtP_Q rp_x rp_os rp_i rp_H0 ly S W mem doc copy t D Lam peak cnt ran most p ly' S' Hp' W' regs' mem' md' ->
  exists Lam' peak' cnt' ran' own' r, trtP_R rp_x rp_os rp_i rp_H0 ly S W mem doc copy t D Lam peak cnt ran most p ly'
      S' Hp' W' regs' mem' Lam' peak' cnt' ran' own' r.
Proof.
  intros rp_x rp_os rp_i rp_H0 ly S W mem doc copy t D Lam peak cnt ran most p ly' S' Hp' W' regs' mem' md' H. destruct
      H as (H0 & Lam' & peak' & cnt' & ran' & own' & H1 & H2 & H3 & r & H4 & H5 & H6).
  exists Lam', peak', cnt', ran', own', r.
  exact {| trtP_room := H0; trtP_ledger := H1; trtP_peak_le := H2; trtP_node := H3; trtP_ret := H4; trtP_r0 := H5;
      trtP_arm := H6 |}.
Qed.

Lemma trtP_Q_of_R : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 :
    list Z) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (doc copy : Z) (t : PjTree.jv) (D
    Lam : list (Z * Z)) (peak cnt ran most : Z) (p : bool) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world
    segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (Lam' : list (Z * Z)) (peak' cnt' ran' own'
    r : Z),
  trtP_R rp_x rp_os rp_i rp_H0 ly S W mem doc copy t D Lam peak cnt ran most p ly' S' Hp' W' regs' mem' Lam' peak' cnt'
      ran' own' r ->
  trtP_Q rp_x rp_os rp_i rp_H0 ly S W mem doc copy t D Lam peak cnt ran most p ly' S' Hp' W' regs' mem' md'.
Proof.
  intros rp_x rp_os rp_i rp_H0 ly S W mem doc copy t D Lam peak cnt ran most p ly' S' Hp' W' regs' mem' md' Lam' peak'
      cnt' ran' own' r HR.
  refine (conj (trtP_room HR) _).
  exists Lam', peak', cnt', ran', own'.
  refine (conj (trtP_ledger HR) (conj (trtP_peak_le HR) (conj (trtP_node HR) _))).
  exists r.
  exact (conj (trtP_ret HR) (conj (trtP_r0 HR) (trtP_arm HR))).
Qed.

Record trtP_R1 (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (copy : Z) (t : PjTree.jv) (Lam
    : list (Z * Z)) (cnt : Z) (p : bool) (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte)
    (Lam' : list (Z * Z)) (cnt' ran' own' r : Z) : Prop := {
  trtP1_r1 : r = 1;
  trtP1_flag : (own' = 1 \/ ran' = 1);
  trtP1_lam : Permutation Lam' Lam;
  trtP1_ablocks : Permutation (ablocks B ly' S') (ablocks B ly S);
  trtP1_cnt_le : cnt <= cnt' <= cnt + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t);
  trtP1_keep : (copy <> 0 -> forall a, copy <= a < copy + 56 -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a)
      }.

Lemma trtP_R1_of : forall (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (copy : Z) (t :
    PjTree.jv) (Lam : list (Z * Z)) (cnt : Z) (p : bool) (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word
    -> option byte) (Lam' : list (Z * Z)) (cnt' ran' own' r : Z),
  trtP_A1 ly S W mem copy t Lam cnt p ly' S' W' mem' Lam' cnt' ran' own' r ->
  trtP_R1 ly S W mem copy t Lam cnt p ly' S' W' mem' Lam' cnt' ran' own' r.
Proof.
  intros ly S W mem copy t Lam cnt p ly' S' W' mem' Lam' cnt' ran' own' r H. destruct H as (H0 & H1 & H2 & H3 & H4 &
      H5).
  exact {| trtP1_r1 := H0; trtP1_flag := H1; trtP1_lam := H2; trtP1_ablocks := H3; trtP1_cnt_le := H4; trtP1_keep := H5
      |}.
Qed.

Lemma trtP_A1_of_R : forall (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (copy : Z) (t :
    PjTree.jv) (Lam : list (Z * Z)) (cnt : Z) (p : bool) (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word
    -> option byte) (Lam' : list (Z * Z)) (cnt' ran' own' r : Z),
  trtP_R1 ly S W mem copy t Lam cnt p ly' S' W' mem' Lam' cnt' ran' own' r ->
  trtP_A1 ly S W mem copy t Lam cnt p ly' S' W' mem' Lam' cnt' ran' own' r.
Proof.
  intros ly S W mem copy t Lam cnt p ly' S' W' mem' Lam' cnt' ran' own' r HR.
  exact (conj (trtP1_r1 HR) (conj (trtP1_flag HR) (conj (trtP1_lam HR) (conj (trtP1_ablocks HR) (conj (trtP1_cnt_le HR)
      (trtP1_keep HR)))))).
Qed.

Record trtP_R2 (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z) (ly
    : alayout) (S : astate) (copy : Z) (t : PjTree.jv) (Lam : list (Z * Z)) (cnt ran : Z) (p : bool) (ly' : alayout)
    (S' : astate) (W' : world segs) (mem' : word -> option byte) (Lam' : list (Z * Z)) (cnt' ran' own' r : Z) : Prop :=
    {
  trtP2_r0 : r = 0;
  trtP2_own0 : own' = 0;
  trtP2_cnt : cnt' = cnt + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t);
  trtP2_ran : ran' = ran;
  trtP2_pos : (exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os (rp_i + length (ck_rtt_evs
      ReaderRes.jr_strtod t p copy))%nat rp_H0 hist' S');
  trtP2_nocopy : (copy = 0 -> Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S));
  trtP2_copy : (copy <> 0 -> exists Db, Permutation Lam' (Db ++ Lam) /\ (forall a k, In (a, k) Db -> ~ In (a - cf_head,
      k + cf_head) (ablocks B ly S)) /\ Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t)))
      /\ (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) Db) (PresetReqAt.rd_blocks
      (PresetReqAt.rtr ReaderRes.jr_strtod [] (WriterValue.wdoc t p)))) /\ (cf_head = PresetReqAt.HEAD -> forall nn,
      (PjTree.depth t <= nn)%nat -> exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') nn copy Db F /\ map
      (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod [] (WriterValue.wdoc t p)) /\ Z.of_nat
      (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) /\ Permutation (ablocks B ly' S') (ablocks B ly S ++
      ck_hblks Db) /\ pj_nodeR segs (rdW W' mem') (prh_lin Lam') copy t Db /\ pj_ncapR segs (rdW W' mem') copy t) }.

Lemma trtP_R2_of : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 :
    list Z) (ly : alayout) (S : astate) (copy : Z) (t : PjTree.jv) (Lam : list (Z * Z)) (cnt ran : Z) (p : bool) (ly' :
    alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (Lam' : list (Z * Z)) (cnt' ran' own' r : Z),
  trtP_A2 rp_x rp_os rp_i rp_H0 ly S copy t Lam cnt ran p ly' S' W' mem' Lam' cnt' ran' own' r ->
  trtP_R2 rp_x rp_os rp_i rp_H0 ly S copy t Lam cnt ran p ly' S' W' mem' Lam' cnt' ran' own' r.
Proof.
  intros rp_x rp_os rp_i rp_H0 ly S copy t Lam cnt ran p ly' S' W' mem' Lam' cnt' ran' own' r H. destruct H as (H0 & H1
      & H2 & H3 & H4 & H5 & H6).
  exact {| trtP2_r0 := H0; trtP2_own0 := H1; trtP2_cnt := H2; trtP2_ran := H3; trtP2_pos := H4; trtP2_nocopy := H5;
      trtP2_copy := H6 |}.
Qed.

Lemma trtP_A2_of_R : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 :
    list Z) (ly : alayout) (S : astate) (copy : Z) (t : PjTree.jv) (Lam : list (Z * Z)) (cnt ran : Z) (p : bool) (ly' :
    alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (Lam' : list (Z * Z)) (cnt' ran' own' r : Z),
  trtP_R2 rp_x rp_os rp_i rp_H0 ly S copy t Lam cnt ran p ly' S' W' mem' Lam' cnt' ran' own' r ->
  trtP_A2 rp_x rp_os rp_i rp_H0 ly S copy t Lam cnt ran p ly' S' W' mem' Lam' cnt' ran' own' r.
Proof.
  intros rp_x rp_os rp_i rp_H0 ly S copy t Lam cnt ran p ly' S' W' mem' Lam' cnt' ran' own' r HR.
  exact (conj (trtP2_r0 HR) (conj (trtP2_own0 HR) (conj (trtP2_cnt HR) (conj (trtP2_ran HR) (conj (trtP2_pos HR) (conj
      (trtP2_nocopy HR) (trtP2_copy HR))))))).
Qed.

(* the CONSEQUENTS of trtP_R2's guarded conjuncts, NAMED: each conjunct of an implication's conclusion, read from
   the record through one lemma (a consumer that applies the guard and destructs its conclusion is not broken by the
   next conjunct appended there) *)

Lemma trtP2_nocopy_lam : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat)
    (rp_H0 : list Z) (ly : alayout) (S : astate) (copy : Z) (t : PjTree.jv) (Lam : list (Z * Z)) (cnt ran : Z) (p :
    bool) (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (Lam' : list (Z * Z)) (cnt' ran'
    own' r : Z),
  trtP_R2 rp_x rp_os rp_i rp_H0 ly S copy t Lam cnt ran p ly' S' W' mem' Lam' cnt' ran' own' r ->
  copy = 0 ->
  Permutation Lam' Lam.
Proof.
  intros rp_x rp_os rp_i rp_H0 ly S copy t Lam cnt ran p ly' S' W' mem' Lam' cnt' ran' own' r HR HP0.
  pose proof (trtP2_nocopy HR) as G.
  exact (proj1 (G HP0)).
Qed.

Lemma trtP2_nocopy_ablocks : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat)
    (rp_H0 : list Z) (ly : alayout) (S : astate) (copy : Z) (t : PjTree.jv) (Lam : list (Z * Z)) (cnt ran : Z) (p :
    bool) (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (Lam' : list (Z * Z)) (cnt' ran'
    own' r : Z),
  trtP_R2 rp_x rp_os rp_i rp_H0 ly S copy t Lam cnt ran p ly' S' W' mem' Lam' cnt' ran' own' r ->
  copy = 0 ->
  Permutation (ablocks B ly' S') (ablocks B ly S).
Proof.
  intros rp_x rp_os rp_i rp_H0 ly S copy t Lam cnt ran p ly' S' W' mem' Lam' cnt' ran' own' r HR HP0.
  pose proof (trtP2_nocopy HR) as G.
  exact (proj2 (G HP0)).
Qed.

Local Unset Implicit Arguments.

(* check_round_trip (fuzz_preset.c:683-692 with round_trip_rewrite :638-681 inlined; plain check_round_trip_c.v
   :127-169): round_trip_text (doc, 0, &copy) and (doc, 1, NULL) into its own frame (frame_alloc_3), for an object
   the rewrite (pj_string, pj_set (&copy, "modifiedAt"), pj_write, pj_parse, the member compares, fuzz_free,
   pj_free), pj_free (&copy), the frame released (set_shadow_f5). The property aborts are unreachable for the
   grammar's tree of an input x with the plain length bounds and g_fail_at = SIZE_MAX. cset is pj_set's allocation
   count (0 when the member exists). DEFERRED (fixed harness #102): no abort arm for pj_string / pj_set failed
   (:647), the rewrite's pj_write / pj_parse failed (:653), or its two round_trip_text calls' NULL sites (header). *)
Definition tcheck_round_trip_specX (CTX0 : list (list Z)) (a_mod_at a_stamp : Z) : Prop :=
  forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch doc t D (x : list Z) Lam peak cnt ran most,
  fpre B ARx STK_check_round_trip ly S Hp W regs mem md ch ->
  (* the memory is normal at entry: this function's subtree reaches musl strtod (measured on BOTH rebuilt pins:
     strtod's only callers are ex_value and parse_value, and this text's subtree reaches one of them), whose row
     consumes it, and nothing below supplies it - it is seeded at main and threaded down. Same spelling and same
     reason as tex_value_specX's; see its comment for the suppliers and for the two halves of the route. *)
  YAkMemnorm.memnorm segs mem ->
  prh_univ_closure B CTX0 -> prh_ctx CTX0 F_check_round_trip (raZ regs :: spine ch) ->
  getr regs 10 = w64 doc ->
  ck_tree_ok ly S Lam W mem doc t D ->
  ck_read x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  kept_img B a_mod_at (Z.of_nat (length ck_MOD_AT) + 1) -> kept_img B a_stamp (Z.of_nat (length ck_STAMP) + 1) ->
  PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x) -> PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54 ->
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 -> cnt < 2 ^ 62 - 2 ^ 30 ->
  (* ITS RUN EVENTS, as an entry premise: the model's own list for this call, PresetReqAt.round_trip (both
     round_trip_text calls, the rewrite of an object, pj_free (&copy)); supplied by LLVMFuzzerTestOneInput's walk from
     PresetRun.call_tail *)
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (PresetReqAt.round_trip ReaderRes.jr_strtod t) ->
  (* THE FLAGS ARE CLEAR AT ENTRY (the kit owner's ruling on the third #102 defect, 2026-10-29): g_own_ran_out = 0 and
     g_ran_out = 0, so out_of_memory() is 0 at entry and any 1 at the return comes from THIS call. Its only call is new:832, reached only after out_of_memory () was 0 at new:820
     and nothing between allocates through the ledger (read_members only looks members up). *)
  ran = 0 ->
  (* EVERY ALLOCATOR REQUEST OF THIS SUBTREE IS WITHIN g_most. A refusal of a request n > g_most sets NO flag
     (merged alloc.c:76-77), so out_of_memory() stays 0 and the property aborts become reachable on a reading or a
     write that was refused. The bound closes that. Its discharge is the P8 owner's lib/Spec/PjReqBound.v (every
     reader request <= PJ_ALLOC_BOUND (|x|)) at g_most = PJ_ALLOC_BOUND (size), set at new:810, not a premise
     restated per caller. The harness itself does not treat a request above the bound as impossible:
     check_bounded_alloc (new:565) tests for it. Only the ledger's requests count (fuzz_malloc / fuzz_realloc):
     the harness's own (noted (malloc ..), tx_put's realloc) are outside alloc.c and set g_own_ran_out instead. *)
  RQA_crt t <= most ->
  blocks_bytes S + LIVE_check_round_trip t <= LIVE_MAX -> RQ_crt t + cf_head < cf_malloc_max ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_round_trip ->
  room_live_cf S -> PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 rp_hist S -> ck_frm0 ->
  (* THE RUN HAS AT MOST 4 CALLS: A17's prefix bound needs it where this text pays a post-form
     callee's hull budget from its position (lib/A/PresetHullPay.v hull_budget_of_room_pos) *)
  (length rp_os <= 4)%nat ->
  (* THE WILD BUDGET (the room count of P''): two round_trip_text calls (new:776, pretty 0 then pretty 1), each of
     32, and round_trip_rewrite's own pj_parse (new:731), which takes 2. So k is prh_wk F_check_round_trip = 66 =
     32 + 32 + 2. The constants compose here because this one IS the sum of its callees' (a per-call constant would
     not: see prh_wk's note on the tx family). *)
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_round_trip) (st_depot S) ->
  (* THE RUN'S STRTOD MODEL IS KEYED (HP_sm; tcheck_reject_clean_starved_specX's note): ReaderRes.jr_strtod where
     rp_sm stood *)
  (* THE CALL'S ALLOCATIONS ARE CONSUMER ALLOCATIONS OF THE RUN (the kit owner's ruling 2026-10-29 ~19:3xZ: the NAMED
     entry premise of the three ENTRY-KEYED check texts). With the entry position and the run premise, P8
     (PresetCfnA.preset_no_refusal; a NULL of malloc_cf is primary-only, YG0dcf.malloc_cf_null_post) and the
     engine's granted paths (PRH_Base.prh_rpost_granted over amreal, YG0d.v:73-92) exclude a REAL refusal at
     every allocation of the call, so the post states the refusal arm DEAD. Supplied by the caller from
     PresetRun.hcons (call_cons flags every event of round_trip / call_tail true; PRH_Base.prh_cons_from_app_iff
     splits the caller's window). *)
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i (length (PresetReqAt.round_trip ReaderRes.jr_strtod t)) ->
  (* THE LIVE REAL STACK ABOVE sp, AT check_round_trip's ENTRY (the kit owner's ruling, 2026-10-30 10:58Z, on
     tround_trip_text_specX; the unit owner's chain ruling, 2026-10-30 09:23Z: the same unguarded conjunct, appended
     last, on every text of the caller chain up to the harness entry). Both round_trip_text calls (new:776) take
     tround_trip_text_specX's last premise `YGcallStackUp.astack_up_x segs ly W (spZ regs) mem` at their call state.
     Nothing else gives it there: fpre gives only this function's window [sp - STK, sp), and no AR_laws_x field reads
     a real-stack byte (YGcallStackUp.v's header). MET AT THE REAL CALL STATE GIVEN THIS ENTRY FACT: this text's walks
     carry this conjunct and the journal to each call by YGcallStackUp.astack_up_at_xwR (lib/A/Prog/Crt102Arms.v
     :1102-1109, lib/A/Prog/Crt102B_RRT.v:1096-1101). The round-trip stack walker's witness and its controls C1 / C2
     (RttStackUpA.v / RttStackUpB.v, RttStackUpCtlA.v / RttStackUpCtlB.v) are at commit 5208cc4f6eb0, not on this
     tree (HISTORY).
     NOT GUARDED (tsame_specX's guarded twin is a different statement). Supplied by LLVMFuzzerTestOneInput's caller
     through the slot pre (PresetCfnA.v / PresetCfnB.v preset_lib_pre_x, owned by the driver-contract owner); its root at the initial
     state is YGcallStackUp.astack_up_init with the start-up residuals (a start-up proof still to write). *)
  YGcallStackUp.astack_up_x segs ly W (spZ regs) mem ->
  (* #102 (src-102/new:772 against the base's :683): check_round_trip RETURNS int, "1 when memory ran out, and the
     call ends" (new:771). Same shape as the three rows above (g_own_ran_out's row is generated). Its two round_trip_text
     calls now return the same flag, which is how the end reaches it; `copy` is initialised from a new file static
     `empty` (new:774-775), so the frame's slot is a known zero tree at entry rather than indeterminate. *)
  (* THE r = 1 ARM, from the body (new:776-780): `ran_out = round_trip_text (doc, 0, &copy) || round_trip_text (doc,
     1, NULL) || (object && round_trip_rewrite (doc, &copy))`, then pj_free (&copy) on BOTH arms. So every block is
     given back on both arms (copy is freed whatever the rewrite left in it; round_trip_rewrite's own exits
     new:723-724 and :732-735 hold no read-back tree, since parse_noting rejects a reading that ran out), but on
     r = 1 FEWER calls ran and g_ran_out may have become 1: the exact count and `ran' = ran` are the r = 0 arm's only
     (corrected 2026-10-29; an earlier wording kept them outside the split). *)
  (* UNIV-END, CLOSED (it asked the universe for the cursor end of a FRESH buffer this call allocates itself,
     round_trip_rewrite's own text, src-102/new:723-735): the closure's clause 4b holds the cursor free's trace at
     every word, so parse_noting's text takes no membership of the end and nothing is owed here. *)
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.8); fpostFbm is already at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_check_round_trip) regs mem md)
    (fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_check_round_trip))
      STK_check_round_trip [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\ exists Lam' peak' cset cnt' ran' own',
       Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\ peak <= peak' /\
       0 <= cset <= 3 /\ (forall ms, t = PjTree.JObj ms -> In ck_MOD_AT (map fst ms) -> cset = 0) /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
       pj_nodeR segs (rdW W' mem') (prh_lin Lam') doc t D /\
       exists r, getr regs' 10 = w64 r /\
         (* THE r = 1 ARM IS DEAD under prh_cons_from (above; see round_trip_text) *)
         r = 0 /\
         ((r = 1 /\ (own' = 1 \/ ran' = 1) /\ cnt <= cnt' <= cnt + ck_crt_count t cset) \/
          (r = 0 /\ own' = 0 /\ cnt' = cnt + ck_crt_count t cset /\ ran' = ran /\
           (* THE EXACT ADVANCE on the r = 0 arm; the r = 1 arm states none (see round_trip_text) *)
           exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os
             (rp_i + length (PresetReqAt.round_trip ReaderRes.jr_strtod t))%nat rp_H0 hist' S')))).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tcheck_round_trip_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. tcrP_Q IS the text's post (tcrP_Q_check fails to build if
   the two ever differ); tcrP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition tcrP_A1 (t : PjTree.jv) (cnt cset cnt' ran' own' r : Z) : Prop :=
  r = 1 /\ (own' = 1 \/ ran' = 1) /\ cnt <= cnt' <= cnt + ck_crt_count t cset.

Definition tcrP_A2 (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z)
    (t : PjTree.jv) (cnt ran : Z) (S' : astate) (cset cnt' ran' own' r : Z) : Prop :=
  r = 0 /\ own' = 0 /\ cnt' = cnt + ck_crt_count t cset /\ ran' = ran /\ exists hist', PresetRoomPos.iface_room_pos
      ReaderRes.jr_strtod rp_x rp_os (rp_i + length (PresetReqAt.round_trip ReaderRes.jr_strtod t))%nat rp_H0 hist' S'.

Definition tcrP_Q (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z)
    (ly : alayout) (S : astate) (doc : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (peak cnt ran most : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  room_live_cf S' /\ exists Lam' peak' cset cnt' ran' own', Permutation Lam' Lam /\ Permutation (ablocks B ly' S')
      (ablocks B ly S) /\ peak <= peak' /\ 0 <= cset <= 3 /\ (forall ms, t = PjTree.JObj ms -> In ck_MOD_AT (map fst
      ms) -> cset = 0) /\ prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\ pj_nodeR segs
      (rdW W' mem') (prh_lin Lam') doc t D /\ exists r, getr regs' 10 = w64 r /\ r = 0 /\ (tcrP_A1 t cnt cset cnt' ran'
      own' r \/ tcrP_A2 rp_x rp_os rp_i rp_H0 t cnt ran S' cset cnt' ran' own' r).

Lemma tcrP_Q_check : forall (CTX0 : list (list Z)) (a_mod_at a_stamp : Z), tcheck_round_trip_specX CTX0 a_mod_at
    a_stamp -> tcheck_round_trip_specX CTX0 a_mod_at a_stamp.
Proof.
  intros CTX0 a_mod_at a_stamp H. unfold tcheck_round_trip_specX in *.
  intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most HP0 HP1 HP2 HP3 HP4 HP5
      HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23 HP24 HP25 HP26.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (tcrP_Q rp_x rp_os rp_i rp_H0 ly S
      doc t D Lam peak cnt ran most) end.
  exact (H rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most HP0 HP1 HP2 HP3 HP4
      HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23 HP24 HP25 HP26).
Qed.

Record tcrP_R (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z) (ly :
    alayout) (S : astate) (doc : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (peak cnt ran most : Z) (ly' : alayout) (S'
    : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (Lam' : list (Z *
    Z)) (peak' cset cnt' ran' own' r : Z) : Prop := {
  tcrP_room : room_live_cf S';
  tcrP_lam : Permutation Lam' Lam;
  tcrP_ablocks : Permutation (ablocks B ly' S') (ablocks B ly S);
  tcrP_peak_le : peak <= peak';
  tcrP_cset : 0 <= cset <= 3;
  tcrP_cset_mod : (forall ms, t = PjTree.JObj ms -> In ck_MOD_AT (map fst ms) -> cset = 0);
  tcrP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own';
  tcrP_node : pj_nodeR segs (rdW W' mem') (prh_lin Lam') doc t D;
  tcrP_ret : getr regs' 10 = w64 r;
  tcrP_r0 : r = 0;
  tcrP_arm : (tcrP_A1 t cnt cset cnt' ran' own' r \/ tcrP_A2 rp_x rp_os rp_i rp_H0 t cnt ran S' cset cnt' ran' own' r)
      }.

Lemma tcrP_R_of : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 :
    list Z) (ly : alayout) (S : astate) (doc : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (peak cnt ran most : Z) (ly' :
    alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' :
    Model),
  tcrP_Q rp_x rp_os rp_i rp_H0 ly S doc t D Lam peak cnt ran most ly' S' Hp' W' regs' mem' md' ->
  exists Lam' peak' cset cnt' ran' own' r, tcrP_R rp_x rp_os rp_i rp_H0 ly S doc t D Lam peak cnt ran most ly' S' Hp'
      W' regs' mem' Lam' peak' cset cnt' ran' own' r.
Proof.
  intros rp_x rp_os rp_i rp_H0 ly S doc t D Lam peak cnt ran most ly' S' Hp' W' regs' mem' md' H. destruct H as (H0 &
      Lam' & peak' & cset & cnt' & ran' & own' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & r & H8 & H9 & H10).
  exists Lam', peak', cset, cnt', ran', own', r.
  exact {| tcrP_room := H0; tcrP_lam := H1; tcrP_ablocks := H2; tcrP_peak_le := H3; tcrP_cset := H4; tcrP_cset_mod :=
      H5; tcrP_ledger := H6; tcrP_node := H7; tcrP_ret := H8; tcrP_r0 := H9; tcrP_arm := H10 |}.
Qed.

Lemma tcrP_Q_of_R : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 :
    list Z) (ly : alayout) (S : astate) (doc : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (peak cnt ran most : Z) (ly' :
    alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' :
    Model) (Lam' : list (Z * Z)) (peak' cset cnt' ran' own' r : Z),
  tcrP_R rp_x rp_os rp_i rp_H0 ly S doc t D Lam peak cnt ran most ly' S' Hp' W' regs' mem' Lam' peak' cset cnt' ran'
      own' r ->
  tcrP_Q rp_x rp_os rp_i rp_H0 ly S doc t D Lam peak cnt ran most ly' S' Hp' W' regs' mem' md'.
Proof.
  intros rp_x rp_os rp_i rp_H0 ly S doc t D Lam peak cnt ran most ly' S' Hp' W' regs' mem' md' Lam' peak' cset cnt'
      ran' own' r HR.
  refine (conj (tcrP_room HR) _).
  exists Lam', peak', cset, cnt', ran', own'.
  refine (conj (tcrP_lam HR) (conj (tcrP_ablocks HR) (conj (tcrP_peak_le HR) (conj (tcrP_cset HR) (conj (tcrP_cset_mod
      HR) (conj (tcrP_ledger HR) (conj (tcrP_node HR) _))))))).
  exists r.
  exact (conj (tcrP_ret HR) (conj (tcrP_r0 HR) (tcrP_arm HR))).
Qed.

Record tcrP_R1 (t : PjTree.jv) (cnt cset cnt' ran' own' r : Z) : Prop := {
  tcrP1_r1 : r = 1;
  tcrP1_flag : (own' = 1 \/ ran' = 1);
  tcrP1_cnt_le : cnt <= cnt' <= cnt + ck_crt_count t cset }.

Lemma tcrP_R1_of : forall (t : PjTree.jv) (cnt cset cnt' ran' own' r : Z),
  tcrP_A1 t cnt cset cnt' ran' own' r ->
  tcrP_R1 t cnt cset cnt' ran' own' r.
Proof.
  intros t cnt cset cnt' ran' own' r H. destruct H as (H0 & H1 & H2).
  exact {| tcrP1_r1 := H0; tcrP1_flag := H1; tcrP1_cnt_le := H2 |}.
Qed.

Lemma tcrP_A1_of_R : forall (t : PjTree.jv) (cnt cset cnt' ran' own' r : Z),
  tcrP_R1 t cnt cset cnt' ran' own' r ->
  tcrP_A1 t cnt cset cnt' ran' own' r.
Proof.
  intros t cnt cset cnt' ran' own' r HR.
  exact (conj (tcrP1_r1 HR) (conj (tcrP1_flag HR) (tcrP1_cnt_le HR))).
Qed.

Record tcrP_R2 (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z) (t :
    PjTree.jv) (cnt ran : Z) (S' : astate) (cset cnt' ran' own' r : Z) (hist' : list chunk) : Prop := {
  tcrP2_r0 : r = 0;
  tcrP2_own0 : own' = 0;
  tcrP2_cnt : cnt' = cnt + ck_crt_count t cset;
  tcrP2_ran : ran' = ran;
  tcrP2_pos : PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os (rp_i + length (PresetReqAt.round_trip
      ReaderRes.jr_strtod t))%nat rp_H0 hist' S' }.

Lemma tcrP_R2_of : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 :
    list Z) (t : PjTree.jv) (cnt ran : Z) (S' : astate) (cset cnt' ran' own' r : Z),
  tcrP_A2 rp_x rp_os rp_i rp_H0 t cnt ran S' cset cnt' ran' own' r ->
  exists hist', tcrP_R2 rp_x rp_os rp_i rp_H0 t cnt ran S' cset cnt' ran' own' r hist'.
Proof.
  intros rp_x rp_os rp_i rp_H0 t cnt ran S' cset cnt' ran' own' r H. destruct H as (H0 & H1 & H2 & H3 & hist' & H4).
  exists hist'.
  exact {| tcrP2_r0 := H0; tcrP2_own0 := H1; tcrP2_cnt := H2; tcrP2_ran := H3; tcrP2_pos := H4 |}.
Qed.

Lemma tcrP_A2_of_R : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 :
    list Z) (t : PjTree.jv) (cnt ran : Z) (S' : astate) (cset cnt' ran' own' r : Z) (hist' : list chunk),
  tcrP_R2 rp_x rp_os rp_i rp_H0 t cnt ran S' cset cnt' ran' own' r hist' ->
  tcrP_A2 rp_x rp_os rp_i rp_H0 t cnt ran S' cset cnt' ran' own' r.
Proof.
  intros rp_x rp_os rp_i rp_H0 t cnt ran S' cset cnt' ran' own' r hist' HR.
  refine (conj (tcrP2_r0 HR) (conj (tcrP2_own0 HR) (conj (tcrP2_cnt HR) (conj (tcrP2_ran HR) _)))).
  exists hist'.
  exact (tcrP2_pos HR).
Qed.

Local Unset Implicit Arguments.

End c.
