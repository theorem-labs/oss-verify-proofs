(* This file carries the kit's text of the re-hiding move for its three crossing texts
   (`PRIMED-SHAPES.md (sha256 9e4880d18317; internal record)` sec. 2.9, 2.10, 2.H3): tpj_free_specX and tpj_set_specX conclude SRr' segs RZ_cf with the
   post fpostWmR .. (wle' segs RZ_cf) (fpostWm is SHARED); tpj_parse_specX concludes SRr' segs RZ_cf and keeps
   fpostWFbm, which is AFTER-FREE-ONLY and already at wle' (PRH_Base.v). tpjP_Q_check matches the primed conclusion.
   The unit owner's ruling C2 (2026-10-31 04:19Z) struck the scratch notice that stood here,
   by a comment-only edit that keeps the header at 7 lines, so every line after it keeps its number and the line
   numbers other files cite below the header still hold. *)
(* fuzz_preset, program part (the kit's pj texts): the ASan contract TEXTS of preset_file.c's tree API - pj_parse, pj_free,
   pj_get, pj_get_str, pj_set, pj_string - in cgif's per-function form (cgif_file lib/YC21.v:33-66; the fm port's FMH_Fn.v:101-231),
   copied from lib/A/PRH_FnAlloc.v: fpre (YCbqG's afn_pre_x + the read-only view), argument registers, the allocation trace
   in the image's universe where the function allocates, the alloc.c ledger (PRH_Base.v prh_ledger), and SRr or SRr' to the
   return address. Every conclusion is `srealizes`, in the continuation form SRr (lib/Reusable/YA0n.v:38-41) or SRr' (YA0nH.v:163).
   IMAGE-PARAMETRIC: the entry is pa_sigma AS_<fn>, the frame STK_<fn> (PRH_Base.v, depth-indexed for pj_free / pj_set); no
   image constant and no numeral address. ALLOCATOR-PARAMETRIC: ARx is an explicit argument.
   FUNCTIONAL CONTENT: preset's released plain contracts lib/Prog/{pj_parse,pj_free,pj_get,pj_get_str,pj_set,pj_string}_c.v,
   restated (results, the tree, the trace model, the ledger moves), over the C source src/preset_file.c @246923f04ac0
   (:296-309, :334-350, :352-369, :373-392, :406-411). Plain-only machinery is dropped: rf_ok / rf_room /
   room_run -> live room on blocks_bytes (LIVE_<fn> below, derived from the plain bound cited at each); reader_env -> fpre;
   rpost -> the journal; rd_cells / ro_agree -> nothing (arodata in fpre); new_blks over `blocks L A` -> over ablocks.
   THE READER'S PREDICATES are the recursive-reader author's lib/A/PRH_Reader.v (imported: pj_nodeR, pj_fdR, pj_zeroR, pj_rwR, pj_hdrR,
   pj_cstrR, rd_u64, pj_apartR, pj_holdsR, pj_footR, pj_freeableR over mrestrict (w_H W) mem with lblk := prh_lin Lam;
   cap2R, kids_blkR, keys_blkR; and its pure trace layer hpeakR, lszR, nliveR), so pj_parse states over the same set as
   parse_value. ONE NAME FOR THE STRTOD MODEL IN THE TEXTS (the kit owner's ruling, 2026-10-29 ~20:0xZ): tpj_parse_specX
   and its supply state over ReaderRes.jr_strtod, as parse_value / parse_items and the check texts do;
   PRH_Reader.prh_jr_strtod has its body (FloatScan.scan_strtod (txt ++ [0])), so the two are convertible, and it stays
   the name of the granted-trace helpers (prhPj_ptrace here, PRH_Charge's prhPv_gtrace / prhPi_gtrace). No
   plain memory-predicate file (PjStruct, PjIn) is Required. Other pure model names, Required only, qualified, no lemma
   cited: PjTree, PjGrammar, PjRoundTrip (maxrun), ReaderRes (fail_after, jr_strtod); pj_set's request list is restated from
   pj_set_c.v:17-20 (prhPj_set_trace).
   prh_alloc_post (PRH_FnAlloc.v:238) is fuzz_strdup's outcome, which pj_string returns.
   room: room_live_cf (PRH_Base.v, owned by the allocator-model owner), room_cf at none (pj_string's strdup and every other allocator call
   these texts reach get their primary room from P8's preset_room through the driver); margins removed. The four
   allocating texts take room_live_cf S and give room_live_cf S' in every post; pj_get / pj_get_str carry
   room_live_cf S -> room_live_cf S'. Where a struct or text is handed to a reader callee its premise is the callee's own: PRH_FnReader.v's
   prhReader_at (place) and prhReader_home (text home).
   allocator traces: prh_univ_closure (PRH_Base.v), taken by pj_parse, pj_free, pj_set and pj_string (CTX0, the driver's
   contexts); dropped prh_malloc_univ (pj_parse, pj_set, pj_string), the realloc pair In [cf_pc_realloc_ra0] /
   In [cf_pc_realloc_ra0; pi_ret_realloc] (pj_parse, pj_set), prhPj_free_univ (pj_parse, pj_free, pj_set) and pj_parse's
   membership In (raZ regs :: spine ch) CTX; kept prhPj_rd_free_univ (pj_parse only: its subtree's parse_string /
   parse_items free, whose s0 is the struct pj_in on pj_parse's REAL stack, so the chain reads pj_parse's frame words,
   which the closure does not cover; G-Pj9). Every other allocator call these functions reach has an EMPTY chain, so
   its trace is a closure literal [pc0; return site]: fuzz_malloc and fuzz_realloc hold n in s0, and pj_free tail-calls
   the free wrapper through fuzz_free with s0 = the node v (A 0x8651c `mv s0, a0`), below alloc_ceiling (a block or a
   fake frame), so achain gives []. A node on the caller's REAL stack would make achain read the bytes below it as a
   frame chain, so the structs pj_free, pj_parse (out) and pj_set (val) hand to pj_free are below alloc_ceiling; every
   harness caller keeps them in its fake frame (the use-after-return flag is 1, every __asan_stack_malloc_N returned a
   fake frame: 716 of 716 on in/v/small.hdr1.bin, the kit owner's qemu run).
   THE CALLER-WINDOW FORM is the kit's fwin / fpostW / fpostWF (PRH_Base.v, this lane's form lifted): pj_parse,
   pj_free, pj_set and pj_string write a 56-byte struct pj the CALLER owns (plain rplace / pj_place, PjStruct.v:131-134:
   on the caller's stack `sl <= p`, or in a block). In a live block or a caller's fake-stack frame (frames S: every
   harness caller takes its `struct pj` locals in one, __asan_stack_malloc_N) the journal allows the write through FP;
   on the caller's REAL stack above sp, apost_base_x forbids it; fpostW runs the journal at (STK + d) (spZ regs + d) and
   keeps every byte of [sp, sp + d) outside FP. The written struct goes in FP (the kit's rule).
   R1 (a preserved caller buffer is placed so the journal keeps it): pj_get / pj_get_str read the header in a live
   block, a caller frame or the stack above sp (prhPj_rslot) and do not restate the key's bytes after the call.
   NAMED GAPS / ASSUMPTIONS:
   - G-Pj1 (shadow of live blocks): the tree's blocks, keys and strings lie in live harness blocks; their user bytes'
     shadow is addressable by the instance (the allocator-model owner's AR_head_shadow_cf: shadow 0 on [a + cf_head, a + req_size n),
     the head poisoned; YCbqG's generic alx_shadow is not true of harness blocks), so no text premises it. A caller's
     struct on the real stack is addressable by alx_zshadow (YCbqG ea24ad37a3c; the stack is zero_shadow_ranges' head).
   - G-Pj2 (pj_string, s = NULL): `strdup (s ? s : "")` duplicates the image's empty-string literal; the walk needs that
     literal's cstr_ok and kept_at (read-only bytes via arodata_okP; shadow via in_zs), an image fact no premise can name.
     Its cstr_ok is now PRH_Base.cstr_ok_ro's, the image premise decided by YGcallRoStr.ro_str_check (vm_compute).
     No harness call passes NULL (fuzz_preset.c:647).
   - G-Pj3 (pj_parse's text): the text is at parse_value's home, prhReader_home (kept_at, or a live allocator block whose
     base is not a hidden head: the libFuzzer input, plain CrsRun.v:90 DBLK), so its bytes and shadow survive the read's
     allocator calls; the plain text_ok's caller-stack case is not admitted (no ASan caller uses it).
   - G-Pj4 (fake-stack room): pj_parse's subtree takes at most DOC_D class-0 frames (parse_value's __asan_stack_malloc_0, both
     images); the premise bounds frames S against YG00's fs_frames 0 (cgif YG0d.v:288's count_cid bound).
   - G-Pj5 (parse_value 0's premises, PRH_FnParse.v rd_pre): each follows from pj_parse's at the call (frm_zero, window,
     home, place, room prhPv_rk (prhPv_gtrace 0 tl) <= prhPj_parse_steps tl by its first summand, live room, the
     outcome-list bound below); pj_free DOC_D needs
     pj_fdR .. DOC_D out D on its refusal (parse_value gives depth MAXD - 0: pj_fdR's depth is monotone).
   - G-Pj6 (composition through a caller's fake frame): a struct in a caller's frame is in the callee's FP; the callers'
     walks compose through YCbqG b092d73a858's ajournal_x_sub (four disjuncts: the caller's FP, a temporary block, the
     caller's own new frame, the caller's real-stack window).
   - G-Pj7 (pj_parse's live room and request over the GRANTED run): parse_value asks its live room at each event of its
     granted run (PRH_FnParse.rd_room, PRH_Base.prh_live_evs) and its request bound over that run; pj_parse states its
     own over prhPj_ptrace tl (every call granted). A run with a refused call is the granted
     run's prefix with EFail in place of the refused event and stops there (PjGrammar.v jbind / jalloc), so its hpeakR
     and calls are at most the granted run's: a pure grammar fact (PjGrammar.v:726 agrees) the walk proves once.
   - G-Pj8 CLOSED (parse_value's CTX): under the closure parse_value takes no context premise; pj_parse is not a
     frame-pointer function (s0 = out), so parse_value runs in [pi_call_rets F_pj_parse F_parse_value]'s literal context.
  - G-Pj9 CLOSED INTO THE CLOSURE (the kit owner's ruling; PRH_Base.v prh_s0 / prh_univ_closure's clauses 4a and 4b).
   parse_string and parse_items keep s0 = q + pi_s0cur F at their free (q the
    struct pj_in on pj_parse's real stack; generated: A 0 / 0, B parse_string 0, parse_items 16), and fuzz_free
    tail-calls free, so the trace is [pc0; r] or [pc0; r; w], w the word at q + pi_s0cur F - 8. MEASURED on both
    pins: A q = pj_parse's sp (0x85e60 `mv a0, sp`), w = the top parse_value's saved ra (a return site of pj_parse's
    `jal parse_value`, A 0x85e6c (PRH_Img.v:301), a CODE word); B q = pj_parse's sp + 8 (0x86330): parse_items' w = the cursor's end
    t0 + len (a DATA word) and parse_string's w = pj_parse's never-written slot at its sp, i.e. the ENTRY word at
    spZ regs - pi_frame F_pj_parse (a DATA word, arbitrary). The universe is the IMAGE's (the S1 owner's P'' answer):
    clause 4b holds the trace at EVERY w through the wild arm, so pj_parse states no membership of either word; its
    two run-word premises and their OPEN supply note are REMOVED with DW. (The Pj part's earlier prhPj_rd_free_univ
    missed B's parse_items, s0 = q + 16, and is deleted.)
   - pj_set's key and pj_string's text take kept_at, whose third case is an image string under route (a), the
     const-shadow cells kept by AR_laws_x field 16 alx_const_cells (D2: check_round_trip's "modifiedAt" and stamp
     have a partial last granule; image B's cells wait on the image-B memnorm owner's regeneration).
   Statements, and the SUPPLY LEMMA of each text's run premise (proved here, next to the text it serves).
   THE MODEL-RUN POSITION, TWO FAMILIES (the kit owner's ruling, 2026-10-29 ~17:25Z). A position of the model run is
   PresetRoomPos.iface_room_pos sm x os i H0 hist S (lib/Spec/PresetRoomPos.v, the one home; the driver-contract owner's
   PresetCfnA.v re-exports it); the run's events at a position are PRH_Base.prh_run_at.
   - READING-CHAIN / LEAF: POST-IMPLICATION form, no entry position, no entry run premise, no rp_* binder:
     tpj_parse_specX (reading chain) and tpj_free_specX (leaf). The post states, for EVERY model run (sm x os) and
     position (i H0 hist) at which S is the position and the run's next events are the call's own list E (computed
     from the outcomes the post binds), the position for S' at the EXACT advance i + length E. Only the position
     is under that implication; the result, memory, ledger and blocks are unconditional. The caller chooses the
     run after the call, to match the outcomes, and chains the implications. Post-form texts call only post-form
     texts: tpj_parse calls parse_value 0 (PRH_FnParse.v) and tpj_free; tpj_free calls itself and fuzz_free
     (PRH_FnAlloc.tfuzz_free_specX, a leaf).
   - WRITER / TX / ROUND-TRIP / CRCS / AS_WRITTEN: ENTRY-keyed list: the rp_* binders, iface_room_pos rp_sm rp_x
     rp_os rp_i rp_H0 rp_hist S UNCONDITIONALLY at entry, the run events the calls make as an ENTRY premise (the
     text's own computed list), and the position at the EXACT advance in the post: tpj_string_specX and
     tpj_set_specX (the rewrite's two, called by check_round_trip). That family's rp_on entry spelling (the kit owner's
     order: a caller that cannot produce a position passes rp_on := False) is NOT applied to these two texts here;
     tpj_string's restatement is left to another walk. Entry-keyed texts may call both families: tpj_set calls
     pj_get (no event), grow (PRH_FnReader.tgrow_specX), fuzz_strdup (PRH_FnAlloc) and pj_free, all post-form;
     tpj_string calls fuzz_strdup.
   The bare pair `exists rp_i' rp_hist', (rp_i <= rp_i')%nat /\ iface_room_pos .. rp_i' .. rp_hist' S'`, which this
   header once called load-bearing, is FALSE (PRH_Base.prh_run_at's note: three measurements) and unusable by a
   caller, which can never name the event at an existential rp_i'; no text here posts it. The live-set bounds at
   each inner allocator call follow from the position by the driver-contract owner's counts_of_room_pos_rl / counts_of_room_pos_ok.
   (The entry-keyed binders are rp_* because several texts already bind x and i; the post-implication binders are
   sm x os i H0 hist, which neither post-form text binds otherwise.)
   THE MODEL OF RECORD for every list below is lib/Spec/PresetReqAt.v blob 43c958024221 with lib/Spec/PresetRun.v
   5ac818ab1fe6 (the #102 model of record, the P8 owner's blobs, taken by path; PresetReqAt.v differs from its
   predecessor 379c33e9e482 in comments only): its HBulk event carries pj_free's POST-ORDER list (fo t / pj_frees
   ok x), not the live-block list the kit's earlier blob used. A premise over the earlier blob typechecks the same
   and denotes a different list.
   THE GRANT LIST (F1, the position census): no text here takes a model grant list any more. tpj_parse_specX's E is
   computed from the outcomes ok its post binds, and the caller picks the model run whose list has that E at the
   position (no prhReader_agree condition). OPEN CORRESPONDENCE, owned by the P8 owner (P8 and the run model):
   nothing in the kit says the allocator's real outcome at a reading's call is the model run's grant list (`git
   grep -w okof` over lib/A and lib/Spec/PresetRoomPos*.v: 0 hits). It is NOT assumed here; it is what a caller
   must bring to find a run whose list has the reading's E inside check_no_overread's readings. pj_string, pj_free
   and pj_set take no grant list: the model grants every allocation they make (PresetReqAt.set_evs; the rewrite is
   outside the readings), and their failure arms are keyed on the outcome the post already names.
   THE EMPTY BULK (F2, census row 7), SETTLED: the model emits HBulk [] for an ACCEPTED document with no blocks and
   NOTHING for a refused one, and pj_free sees the same zeroed node in both, so tpj_free_specX's list is keyed on
   its ORDER LIST F (empty -> no event), not on v <> 0, and the caller steps over an empty bulk event by the kit
   lemma prhPj_bulk_nil_pos below. A pj_free text keyed on v <> 0 (the image-B pj walker's pj_free_evs) has an unsatisfiable
   premise at check_no_overread's pj_free of a refused reading's zeroed node.
   THE ORDER LIST has ONE HOME, lib/A/PRH_PjOrder.v (pj_foR and pj_free_fo, taken by path from the image-B pj walker's
   lane, commit ab365ca51d33; that lane drops its own copies and cites the kit).
   ITS TIE TO A MODEL LIST IS ORDERED, NEVER A PERMUTATION (the kit owner's order 2026-10-29, the owner's
   reversal of the Permutation restatement): PresetRoomPos.iface_room_pos reads the free history IN ORDER, so
   PresetFreeFo.hbulk_perm - which settles the hlive LEDGER state after a bulk - moves no position and is cited
   only where that state alone matters. The two right-hand lists are PresetReqAt.pj_frees (reader-built) and
   PresetReqAt.fo (read back from the writer's text, through PresetFreeFo.pj_frees_wdoc_t); see
   prhPj_free_evs_supply. pj_free_fo's own premise is the ORDERED WRITER-SIZED block list, which no text of the
   kit states, so no text routes through it now (the finding is at prhPj_free_evs_supply_fo).
   pj_free's frees and fuzz_free: PRH_FnAlloc.tfuzz_free_specX is in the post-implication form too (no entry
   position); its bulk arm moves the bulk sub-position PresetRoomPosKeep.iface_room_pos_bulk .. L k to .. L (S k)
   under a run-quantified implication, which is the step pj_free's walk chains across its frees. The earlier OPEN
   item here (fuzz_free taking iface_room_pos at EVERY entry, which pj_free's second and later frees do not have;
   the image-B pj walker's tfuzz_free_specX_FIX widening) does not arise in that form.
   *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_Charge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAtNoMiss PresetFreeFo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
(* the re-hiding move's SRr' and wle' (YA0nH) and preset's zone (YGcfRehidePost.RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the shared pieces ---- *)

(* the allocator blocks of harness blocks (user address, user size) *)
Definition prhPj_hbl (D : list (Z * Z)) : list (Z * Z) := map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) D.

(* the plain new_blks (ReaderRes.v:164-165) over the allocator's blocks *)
Definition prhPj_new (ly : alayout) (S : astate) (D : list (Z * Z)) : Prop :=
  forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S).

(* the allocator blocks other than the harness blocks are unchanged; the harness blocks move from Lam to Lam' *)
Definition prhPj_blocks (ly : alayout) (S : astate) (Lam : list (Z * Z)) (ly' : alayout) (S' : astate)
  (Lam' : list (Z * Z)) : Prop :=
  exists other, Permutation (ablocks B ly S) (prhPj_hbl Lam ++ other) /\
    Permutation (ablocks B ly' S') (prhPj_hbl Lam' ++ other).

(* a struct pj the function writes: placed where its reader callees take it (PRH_FnReader.v prhReader_at: a live
   harness block's user bytes, a live non-harness allocator block, a fake-stack frame of frames S, or the caller's
   window [sp, sp + d)), 8-aligned and writable (pj_rwR), outside the runtime's own bytes and the function's stack
   window, addressable for the instrumented stores and __asan_memset *)
Definition prhPj_slot (STK d : Z) (ly : alayout) (S : astate) (Lam : list (Z * Z)) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (p : Z) : Prop :=
  4096 <= p /\ prhReader_at B ly S Lam regs d p 56 /\ pj_rwR segs (rdW W mem) p /\ amem_range p 56 /\
  (forall a, p <= a < p + 56 -> ~ aowned B ly S a /\ ~ (spZ regs - STK <= a < spZ regs)) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p 56 /\ shadow_hull_vis (aview segs (w_H W) mem) p 56.

(* pj_free's free-call universe as the kit's prh_free_univ (PRH_Base.v): s0 holds the node, below alloc_ceiling. No
   text takes it now: prh_univ_closure implies it (prh_univ_closure_lit); kept as a name for callers' citations *)
Definition prhPj_free_univ : Prop := prh_free_univ B F_pj_free.

(* (pj_parse's G-Pj9 universe premise prhPj_rd_free_univ is subsumed by prh_univ_closure's clause 4b, and deleted) *)

(* a struct pj the function only reads: in a live allocator block, a caller's fake-stack frame or the caller's real
   stack above sp (so the journal keeps it: R1), outside its stack window, addressable for the instrumented loads *)
Definition prhPj_rslot (STK : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (p : Z) : Prop :=
  4096 <= p /\
  ((exists b n, In (b, n) (ablocks B ly S) /\ b <= p /\ p + 56 <= b + req_size n) \/
   (exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= p /\
      p + 56 <= frame_addr ly cid pos + fs_frame_bytes cid) \/
   (spZ regs <= p /\ p + 56 <= ly_top ly)) /\
  amem_range p 56 /\ (forall a, p <= a < p + 56 -> ~ (spZ regs - STK <= a < spZ regs)) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p 56 /\ shadow_hull_vis (aview segs (w_H W) mem) p 56.

(* ---- live room, heads included, each from its plain bound ---- *)

(* pj_parse: over the grammar's trace of the text with every allocation granted, as the plain room_run is
   (pj_parse_c.v:42, room_run F b (snd (jr_run jr_strtod (zb tb) []))); a refused run follows a prefix of that trace and
   then only frees. The room: the trace's peak user bytes (hpeakR), one head per live block (at most its calls), and the
   old block a realloc still holds while it takes the new one (at most the peak again, and its head). parse_value's own
   live room (PRH_FnParse.rd_room: at each event of its granted run, PRH_Base.prh_live_evs) lies under it at every
   event, at cf_head = HEAD. By the plain bound hpeak <= 224 * len + 16384
   (pj_parse_c.v:55) and calls <= 2 * len + 2 it is at most 2 * (224 * len + 16384) + cf_head * (2 * len + 3); the trace
   form also serves a read-back of a long pretty text whose tree is small (round_trip_text, check_round_trip). The
   request bound is parse_value's (prh_maxreq of the trace below cf_malloc_max, rd_room), over the granted run (G-Pj7). *)
Definition prhPj_ptrace (tl : list Z) : list PjGrammar.ev := snd (PjGrammar.jr_run prh_jr_strtod tl []).
Definition LIVE_pj_parse (tl : list Z) : Z :=
  2 * hpeakR (prhPj_ptrace tl) + cf_head * (Z.of_nat (PjGrammar.calls (prhPj_ptrace tl)) + 1).
(* the REQUEST bound, in USER bytes as every RQ_* of the kit (the use site adds the head: `RQ_pj_parse tl + cf_head <
   cf_malloc_max`): the largest single request of the granted reading (PRH_Charge.v prh_maxreq) - NOT the peak, which
   is a high-water mark (the B' walker's full-size witness: the old peak form was false at an accepted 3 MiB input). Its
   callers' RQ_* (PRH_FnCheck.v) inherit it by name. *)
Definition RQ_pj_parse (tl : list Z) : Z := prh_maxreq (prhPj_ptrace tl).

(* ---- the allocator steps on each function's longest path, as model expressions (RK_malloc, RK_free, RK_realloc):
   no text takes them since room is an invariant (ruling (B)); kept because PRH_FnCheck.v (ck_rk_read) and
   PRH_Charge.v's header cite them ---- *)

(* pj_free over a freeable tree with blocks D: one fuzz_free per pointer it frees, NULL included (fuzz_free's text takes
   RK_free either way): str, kids and keys of each node, and keys[i] of each slot; the nodes are 1 + the slots, and the
   slots are at most the kids blocks' 56-byte cells, so at most 3 + 4 * (lsum D / 56) calls *)
Definition prhPj_fsteps (D : list (Z * Z)) : nat := prh_fsteps_bytes (Ledger.lsum D).

(* pj_parse: the GRAMMAR's charge of the granted reading (PRH_Charge.v: parse_value 0's own charge, cited, not
   re-encoded), then pj_free DOC_D of what a refused read built - the refused run agrees with the granted one up to
   the refusal, so its blocks hold at most the granted run's peak *)
Definition prhPj_parse_steps (tl : list Z) : nat :=
  prhPv_rk (prhPv_gtrace 0 tl) + prh_fsteps_bytes (hpeakR (prhPv_gtrace 0 tl)).

(* pj_set: grow's room when n = cap (PRH_FnReader.v LIVE_grow at ty = 6, an object: kids 56 cap2 and keys 8 cap2 with
   their heads, plain set_trace pj_set_c.v:17-20, room_run :55), then the key's strdup klen + 1 and its head *)
Definition LIVE_pj_set (n cap klen : Z) : Z :=
  (if n =? cap then LIVE_grow 6 cap else 0) + klen + 1 + cf_head.

(* pj_string: rf_room (len + 17) (pj_string_c.v:41), one strdup of len + 1 user bytes and its head *)
Definition LIVE_pj_string (len : Z) : Z := len + 1 + cf_head.

(* ---- THE RUN EVENTS of the four allocating texts, and the SUPPLY of each one's run premise: at entry for the
   entry-keyed tpj_string / tpj_set, under the post's implication for the post-form tpj_parse / tpj_free (the
   model of record is the header's: PresetReqAt.v 43c958024221 with PresetRun.v 5ac818ab1fe6) ---- *)

(* THE EMPTY BULK STEP (F2): the model's HBulk [] - an ACCEPTED document with no blocks (`null`, `true`, `false`:
   PresetRun.p1_tfree / call_tail, PresetReqAt.round_trip) - changes neither the live list (hstep s (HBulk []) =
   rmall [] s = s) nor the free history (PresetRunQ.hfrees_q .. ++ PresetRunQ.qfilter []), so the position at rp_i
   IS the position at S rp_i in the same state. pj_free cannot key its own advance on that event (it sees the same
   zeroed node when the model emits nothing at all, after a refused parse), so the CALLER, which holds the model's
   list, steps over it with this. *)
Lemma prhPj_bulk_nil_pos : forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist S,
  nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i = Some (PresetReqAt.HBulk []) ->
  (PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S <->
   PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 rp_hist S).
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist S He.
  destruct (PresetRoomPosKeep.rp_model_bulk rp_sm rp_x rp_os rp_i [] He) as (_ & E1 & E2).
  unfold PresetRoomPos.iface_room_pos. rewrite E1, (PresetRoomPosKeep.rp_q_list _ _ _ E2), PresetRunQ.qfilter_nil.
  rewrite (PresetRoomPosKeep.rp_count_bulk_eq rp_sm rp_x rp_os rp_i [] S He).
  cbn [PresetReqAt.rmall fold_left].
  rewrite app_nil_r. split; intro H; exact H.
Qed.

(* the empty list is every position's premise (a text that makes no model event) *)
Lemma prhPj_run_at_nil : forall rp_sm rp_x rp_os rp_i, prh_run_at rp_sm rp_x rp_os rp_i [].
Proof. intros rp_sm rp_x rp_os rp_i. reflexivity. Qed.

(* pj_string's own model event: its one fuzz_strdup of len + 1 user bytes is the run's HMal (len + 1 + cf_head) -
   unless this is the allocation the harness chose to fail (g_count = g_fail_at), where failing() returns NULL
   without calling the allocator and the model has no event (PresetReqAt.rd_hev (EFail _) = []). A REFUSAL (NULL at
   cnt <> fail) also makes no event; it is excluded in the post's arm, not here. No grant list: pj_string's only
   caller is check_round_trip's rewrite, where the model grants (PresetReqAt.set_evs's head is unconditional). *)
Definition prhPj_string_evs (len cnt fail : Z) : list PresetReqAt.hev :=
  if (cnt =? fail)%Z then [] else [PresetReqAt.HMal (len + 1 + cf_head)].

(* THE SUPPLY: the rewrite calls pj_string (&v, STAMP) first (fuzz_preset.c:615), so the model's set_evs head IS
   this call's event. Its caller has g_fail_at = SIZE_MAX and g_count < 2 ^ 62 (PRH_FnCheck's ledger), hence
   cnt <> fail; cf_head = PresetReqAt.HEAD is 16 = 16 at CfParams_preset. *)
Lemma prhPj_string_evs_supply : forall rp_sm rp_x rp_os rp_i ms cnt fail,
  cf_head = PresetReqAt.HEAD -> cnt <> fail ->
  prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.set_evs ms) ->
  prh_run_at rp_sm rp_x rp_os rp_i
    (prhPj_string_evs (Z.of_nat (length PresetReqAt.MOD_VAL)) cnt fail).
Proof.
  intros rp_sm rp_x rp_os rp_i ms cnt fail Hhd Hne H.
  unfold prhPj_string_evs. rewrite (proj2 (Z.eqb_neq cnt fail) Hne).
  replace (Z.of_nat (length PresetReqAt.MOD_VAL) + 1 + cf_head)
    with (Z.of_nat (Datatypes.S (length PresetReqAt.MOD_VAL)) + PresetReqAt.HEAD)
    by (rewrite Nat2Z.inj_succ, Hhd; lia).
  unfold PresetReqAt.set_evs in H.
  assert (E : forall (a : PresetReqAt.hev) (l : list PresetReqAt.hev), a :: l = [a] ++ l) by reflexivity.
  rewrite E in H. exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H)).
Qed.

(* pj_free's own model events: its frees are ONE model event, the bulk free of the requests of its ORDER LIST F
   (PRH_PjOrder.pj_foR: for each slot the subtree of kids[i], then keys[i]; then kids, keys, str), and NO event when
   F is empty - a NULL argument, an accepted document with no blocks (the model emits HBulk [] there, and the caller
   steps over it by prhPj_bulk_nil_pos), or the zeroed node a refused pj_parse left (the model emits nothing:
   PresetRun.p1_tfree's None arm). Keying on F rather than on v <> 0 is what makes ONE text serve all five call
   sites (F2). *)
Definition prhPj_free_evs (F : list (Z * Z)) : list PresetReqAt.hev :=
  match F with
  | [] => []
  | _ :: _ => [PresetReqAt.HBulk (map (fun b => snd b + cf_head) F)]
  end.

(* THE SUPPLY, generic over the bulk's list Lb (the kit owner's order, 2026-10-29; KEPT ORDERED after the owner's
   reversal ~21:3xZ, which withdrew the Permutation restatement): a caller whose list has the model's HBulk Lb here,
   and whose tree's order list F carries Lb's requests IN ORDER, gets pj_free's run premise. The tie is the ordered
   equality, NEVER a permutation, and the reason is THE POSITION, not the ledger state:
   PresetRoomPos.iface_room_pos reads the free history IN ORDER (PresetRunQ.hfrees_q of the prefix, which each HBulk L
   extends by PresetRunQ.qfilter L - L's frees that enter the quarantine, in order - against YGcfFrees.cf_frees_follow),
   so a walk that frees a permutation of Lb lands at no position of the run. The P8 owner's PresetFreeFo.hbulk_perm
   settles only the hlive LEDGER STATE after the bulk
   and whether it hits (hlive_from and okf are equal for permuted lists); it is cited where that state alone
   matters and NEVER to move a position. ORDERED AGAINST THE WRONG LIST IS FALSE: at {"a":"x"} the order
   [18; 18; 464; 80] and the permutation [18; 18; 80; 464] are different free histories.
   WHERE Lb AND F COME FROM - two lists, each keyed on ITS OWN:
   - a READER-BUILT tree (check_no_overread's three pj_free calls of an accepted reading, pj_parse's own
     pj_free (out) on a refusal): Lb = PresetReqAt.pj_frees sm ok x, the model's reader-side list, computed from the
     TEXT, in pj_free's post-order and with the READER's sizes. The ordered tie of F to it is the Some / None arm's
     own conjunct of PRH_FnParse.tparse_value_specX, carried up by tpj_parse_specX's Some arm (:768-770) and
     PRH_FnCheck.tparse_noting_specX (:738-740): map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees .. ok ..
     It is no longer a premise without a supplier - PJF-TIE is CLOSED by those conjuncts.
   - a tree READ BACK FROM THE WRITER'S TEXT (check_round_trip's pj_free (&copy) / (&back), round_trip_text's
     pj_free (&back)): Lb = PresetReqAt.fo t, and the reader-side ordered list of that same reading IS fo t, by
     the P8 owner's PresetFreeFo.pj_frees_wdoc_t - pj_wf sm t -> pj_frees sm [] (wdoc t p) = fo t, an EQUALITY of
     lists in order, proved (not the permutation rd_blocks_wdoc). The corollary prhPj_free_evs_supply_fo below is
     that one step.
   (The binder is Lb because L is the Section's symbol table.) *)
Lemma prhPj_free_evs_supply : forall rp_sm rp_x rp_os rp_i (F : list (Z * Z)) (Lb : list Z),
  map (fun b => snd b + cf_head) F = Lb ->
  prh_run_at rp_sm rp_x rp_os rp_i [PresetReqAt.HBulk Lb] ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhPj_free_evs F).
Proof.
  intros rp_sm rp_x rp_os rp_i F Lb HF HR. unfold prhPj_free_evs.
  destruct F as [|b F']; [apply prhPj_run_at_nil|]. rewrite HF. exact HR.
Qed.

(* THE SUPPLY AT Lb := fo t, A TREE READ BACK FROM THE WRITER'S TEXT (the kit owner's order 2026-10-29, on the
   owner's reversal; the walk that cited the earlier form is the image-B pj walker's lib/B/Prog/pj_set_seg_ret.v:210,
   commit 76a34fc50dae). The caller holds the tree's READER-side ordered free list - the
   reading here is of x = wdoc t p, so map (snd + cf_head) F = PresetReqAt.pj_frees sm [] (wdoc t p), from
   PRH_FnCheck.tparse_noting_specX's Some arm (with prhPj_frees_acc below where that arm's list is at its own grants
   ok) - and the model's event at this position carries fo t. The two lists are EQUAL, in order, under pj_wf sm t:
   the P8 owner's PresetFreeFo.pj_frees_wdoc_t. ONE CITATION; nothing is re-derived here.
   WHAT THIS REPLACES, AND THE FINDING (the kit owner, 2026-10-29): the earlier statement took the ORDERED,
   WRITER-SIZED block premise `map (fun b => snd b + cf_head) D = PresetReqAtNoMiss.tblk t` and went through
   PRH_PjOrder.pj_free_fo. NO KIT TEXT SUPPLIES THAT PREMISE AT ANY INSTANCE. (1) Every text's block fact is a
   Permutation (tparse_noting_specX :722, :730-731, tround_trip_text_specX's copy arm, tpj_set_specX's entry), and a
   permutation of sizes identifies no block (PRH_Reader.v:219-224). (2) At a READER-BUILT tree it is UNSATISFIABLE
   as soon as the input holds an escape: the reader sizes a string or key block by the ESCAPED INPUT SPAN
   (src/preset_file.c:127, PjGrammar.jr_string:207) while tblk / fo use the writer's re-escape of the decoded text -
   the input [ "\u0041" ] gives 23 where tblk gives 18 (the P8 owner's vm_compute probe, log
   the internal file build-20261029T173818Z.log of its freefo run; also "\/" 19 vs 18, "\u00e9" 23 vs 19, a surrogate
   pair 29 vs 21, the key {"\u0041":1} 23 vs 18). PRH_PjOrder.pj_free_fo is UNCHANGED, still proved and still the
   ONE HOME of the order list (its own premise is satisfiable at a read-back tree); it is cited by no text of the
   kit now, and a consumer that wants it must first produce an ordered writer-sized block list. *)
Lemma prhPj_free_evs_supply_fo : forall rp_sm rp_x rp_os rp_i (F : list (Z * Z)) sm (t : PjTree.jv) p,
  PjRoundTrip.pj_wf sm t ->
  map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees sm [] (WriterValue.wdoc t p) ->
  prh_run_at rp_sm rp_x rp_os rp_i [PresetReqAt.HBulk (PresetReqAt.fo t)] ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhPj_free_evs F).
Proof.
  intros rp_sm rp_x rp_os rp_i F sm t p Hw HF HR.
  apply (prhPj_free_evs_supply rp_sm rp_x rp_os rp_i F (PresetReqAt.fo t)); [|exact HR].
  rewrite HF. exact (PresetFreeFo.pj_frees_wdoc_t sm t p Hw).
Qed.

(* THE SUPPLY AT A READER-SIDE FREE (the kit owner's order 2026-10-29 ~18:5xZ, on the P8 owner's measurement: on a tree
   READ FROM THE INPUT, pj_frees sm ok x differs from fo t as soon as a string or key holds an escape - the C reader
   sizes a string block by the escaped input span, src/preset_file.c:127, model jr_string:207, fo by the writer's
   re-escape; probe log, the internal file build-20261029T173818Z.log (the P8 owner's freefo run): [ "\u0041" ] 23 vs 18, "\/" 19 vs
   18, "\u00e9" 23 vs 19, a surrogate pair 29 vs 21, the key {"\u0041":1} 23 vs 18). The reader-side pj_free is keyed
   on the model's own list Lb := pj_frees sm ok x, IN ORDER; the block side, up to permutation, follows from
   PresetReqAtNoMiss.pj_frees_blocks. NO result may discharge a reader-side pj_free through the fo t form (the
   corollary above is for a tree read back from the writer's text only).
   PJF-TIE IS CLOSED (the kit owner's order 2026-10-29): the ordered tie of F to pj_frees was a named
   premise with no supplier; it is now a conjunct of the texts that BUILD the tree - PRH_FnParse.tparse_value_specX
   (both arms, over prhPv_frees at the call's own cursor), tpj_parse_specX's Some arm (:768-770, at d = 0 where
   prhPv_frees 0 tl ok IS pj_frees ok tl) and PRH_FnCheck.tparse_noting_specX (:738-740). A caller of pj_free
   passes that conjunct straight into this lemma. *)
Lemma prhPj_free_evs_supply_pjf : forall rp_sm rp_x rp_os rp_i (F : list (Z * Z)) sm ok x,
  map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees sm ok x ->
  prh_run_at rp_sm rp_x rp_os rp_i [PresetReqAt.HBulk (PresetReqAt.pj_frees sm ok x)] ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhPj_free_evs F) /\
  Permutation (map (fun b => snd b + cf_head) F) (PresetReqAt.rd_blocks (PresetReqAt.rtr sm ok x)).
Proof.
  intros rp_sm rp_x rp_os rp_i F sm ok x HF HR. split.
  - exact (prhPj_free_evs_supply rp_sm rp_x rp_os rp_i F _ HF HR).
  - rewrite HF. exact (PresetReqAtNoMiss.pj_frees_blocks sm ok x).
Qed.

(* THE ACCEPTED ARM'S BRIDGE, ok TO [] (the driver-contract owner's cut shape, the kit owner's order 2026-10-29). Every post
   stays keyed on ok, the grant list of the run premise it took: tpj_parse_specX binds ok with
   PjGrammar.jr_run ReaderRes.jr_strtod tl ok = (res, tr), and its Some arm's free-order conjunct is over
   PresetReqAt.pj_frees .. ok tl. A caller that cut its own list at the ALL-GRANTED reading (the model's
   parse_evs .. x [] in PresetReqAt.rt_text, PresetRun.call_rest) keeps the [] form with ONE rewrite by this:
   a reading that ACCEPTED met no refusal, so jfv / jfl take the same branches as under [] and the two free lists
   are EQUAL, in order. The model fact is the P8 owner's PresetFreeFo.pj_frees_acc (proved by acc_fuel over
   PjGrammar.agrees_some / jbind_some); cited, not re-derived. The hypothesis is exactly what the Some arms give. *)
Lemma prhPj_frees_acc : forall sm (x : list Z) (ok : list bool) (t : PjTree.jv) tr,
  PjGrammar.jr_run sm x ok = (Some t, tr) ->
  PresetReqAt.pj_frees sm ok x = PresetReqAt.pj_frees sm [] x.
Proof. intros sm x ok t tr E. exact (PresetFreeFo.pj_frees_acc sm x ok t tr E). Qed.

(* THE SUPPLY at a refused reading's zeroed node (check_no_overread's pj_free (&a) after a refused pj_parse): the
   model has no event there and the order list is empty. *)
Lemma prhPj_free_evs_nil : forall rp_sm rp_x rp_os rp_i, prh_run_at rp_sm rp_x rp_os rp_i (prhPj_free_evs []).
Proof. intros rp_sm rp_x rp_os rp_i. apply prhPj_run_at_nil. Qed.

(* THE STEP AT pj_parse's OWN pj_free (out) ON A REFUSAL (FREEORD-NONE, #102; the B' pj_parse walk's open site,
   commit 8a088cd72fac lib/B/Prog/pj_parse_seg_c2ref.v:388-395). On a refusal
   PresetReqAt.parse_evs emits HBulk (pj_frees ok tl) UNCONDITIONALLY (PresetReqAt.v:300-305) - HBulk [] when the
   refused tree holds no block (no allocation made, the first allocation refused, an empty container followed by a
   non-blank tail) - while pj_free (out) makes ONE event for a non-empty order list F and NONE for F = []
   (prhPj_free_evs). (Not the same place as PresetRun.p1_tfree: that is the LATER pj_free (&a) of a P1 reading, where
   the model emits nothing after a refusal and prhPj_free_evs_nil applies.) From the ordered tie of F to the model's
   list Lb - pj_parse's walk takes it from parse_value's free-order conjunct (PRH_FnParse.v tparse_value_specX, either
   arm, at d = 0 and n := DOC_D, where prhPv_frees 0 tl ok IS pj_frees ok tl) - and the run's HBulk Lb at index j:
   pj_free's run premise, and the position at j + length (prhPj_free_evs F) IS the position at j + 1. For F <> [] that
   is the identity; for F = [] it is the step over the model's HBulk [] by prhPj_bulk_nil_pos. *)
Lemma prhPj_free_evs_bulk : forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sr (F : list (Z * Z)) (Lb : list Z),
  map (fun b => snd b + cf_head) F = Lb ->
  prh_run_at rp_sm rp_x rp_os rp_i [PresetReqAt.HBulk Lb] ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhPj_free_evs F) /\
  (PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhPj_free_evs F)) rp_H0 rp_hist Sr ->
   PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + 1) rp_H0 rp_hist Sr).
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sr F Lb HF HR. split.
  - exact (prhPj_free_evs_supply rp_sm rp_x rp_os rp_i F Lb HF HR).
  - destruct F as [|b F'].
    + cbn [map] in HF. subst Lb. cbn [prhPj_free_evs length]. rewrite Nat.add_0_r, Nat.add_1_r.
      exact (proj1 (prhPj_bulk_nil_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sr
        (proj1 (prh_run_at_one rp_sm rp_x rp_os rp_i _) HR))).
    + cbn [prhPj_free_evs length]. intro H. exact H.
Qed.

(* THE SUPPLY of pj_parse's run premise (the one under its post's implication, at the outcomes ok the post binds):
   the model's own list for this reading, PresetReqAt.parse_evs (the reader's events under ok, then the HBulk of
   what pj_free (out) frees on a refusal), is a SEGMENT of every caller's list - check_no_overread's three readings
   (PresetRun.call_evs: parse_evs x (okof o_k)), LLVMFuzzerTestOneInput's own parse (call_rest: parse_evs x []),
   check_reject_clean_starved's (PresetReqAt.starved_parse: parse_evs x (okk (pick x took)), aligned by
   prhPj_parse_evs_starved below) and round_trip_text's parse_noting of the writer's text (PresetReqAt.rt_text:
   parse_evs (wdoc t p) []). The caller applies it at the ok the post binds, once it knows that ok is the run's. *)
Lemma prhPj_parse_evs_supply : forall rp_sm rp_x rp_os rp_i (tl : list Z) (ok : list bool) rest,
  prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.parse_evs ReaderRes.jr_strtod tl ok ++ rest) ->
  prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.parse_evs ReaderRes.jr_strtod tl ok).
Proof.
  intros rp_sm rp_x rp_os rp_i tl ok rest H.
  exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H)).
Qed.

(* THE ALIGNMENT for check_reject_clean_starved (the reject-starved walker's crcs, its interim crs_pexact): the model's list at that
   call is PresetReqAt.starved_parse x took (:340-341), and for took > 0 it IS tpj_parse_specX's E at the starved
   outcome list okk (pick x took). What crcs needs beyond this to use it at the post's ok (the list prh_oks bounds):
   (a) fail = cnt + pick x took at the call (fuzz_alloc_fail (pick x took) just before it); (b) no refusal among the
   calls the reading made (prh_granted ok cnt fail (calls tr): tpj_parse_specX's post, THE OUTCOME OF AN INJECTED
   READING, at the run whose next events are parse_evs tl (okk (Z.to_nat (fail - cnt))), which is this list by (a));
   then (c) by prh_oks's first conjunct and (b), the post's ok agrees with okk (pick x took) on the first calls tr
   outcomes (prhReader_agree, plain arithmetic); and (d) OWED, a pure grammar lemma (owned by the recursive-reader author): grant lists
   that agree on the first calls tr outcomes give PjGrammar.jr_run the same (res, tr) and PresetReqAt.pj_frees the
   same list, hence the same parse_evs - so E at ok IS E at okk (pick x took). Not proved here. *)
Lemma prhPj_parse_evs_starved : forall (sm : list Z -> Z * Z) (tb : list Z) (took : nat), (0 < took)%nat ->
  PresetReqAt.parse_evs sm tb (PresetReqAt.okk (PresetReqAt.pick tb took)) = PresetReqAt.starved_parse sm tb took.
Proof.
  intros sm tb took Ht. destruct took as [|took']; [lia | reflexivity].
Qed.

(* the member of that name: PresetReqAt.mfind (:197-201) at any key, since pj_set's key is a parameter *)
Fixpoint prhPj_mfind (kname : list Z) (ms : list (list Z * PjTree.jv)) : option PjTree.jv :=
  match ms with
  | [] => None
  | (k, u) :: r => if PresetReqAt.zl_eqb k kname then Some u else prhPj_mfind kname r
  end.

Lemma prhPj_mfind_mod : forall ms, prhPj_mfind PresetReqAt.MOD_KEY ms = PresetReqAt.mfind ms.
Proof.
  induction ms as [|[k u] r IH]; [reflexivity|].
  cbn [prhPj_mfind PresetReqAt.mfind]. destruct (PresetReqAt.zl_eqb k PresetReqAt.MOD_KEY); [reflexivity | exact IH].
Qed.

(* pj_set's own model events, the model's set_evs tail at this text's binders: the key PRESENT -> pj_free of the
   value it replaces, one bulk free of that value's blocks (PresetReqAt.fo, the writer's sizes - the object pj_set
   is handed is a tree read back from the writer's text); ABSENT -> grow's reallocs (none when n < cap, else kids
   then keys to cap2) and the key's strdup. The model's own events, so the requests carry PresetReqAt.HEAD; the
   callees' texts carry cf_head, and the two meet at cf_head = HEAD (16 = 16 at CfParams_preset). The callee lists
   are PRH_FnReader's prhPg_evs true n cap [] for grow and prhPj_string_evs / fuzz_strdup's HMal for the key. *)
Definition prhPj_set_evs (ms : list (list Z * PjTree.jv)) (kname : list Z) (n cap : Z) : list PresetReqAt.hev :=
  match prhPj_mfind kname ms with
  | Some u => [PresetReqAt.HBulk (PresetReqAt.fo u)]
  | None => PresetReqAt.rd_hevs (PjRoundTrip.grow_ev true (Z.to_nat n) (Z.to_nat cap) ++
      [PjGrammar.EAlloc (Datatypes.S (length kname))])
  end.

(* THE SUPPLY, and F6 (the position census row 8): the model's set_evs uses the capacity a PARSED object of
   `length ms` members has, PresetReqAt.ncap (length ms), while pj_set's text reads n and cap out of the node's
   header. The two agree exactly when the object is the parse of the writer's text, which is what the rewrite hands
   it - so the supply TAKES `n = |ms|` and `cap = ncap |ms|` as premises and the caller (check_round_trip, whose
   copy is parsed from pj_write's text at :638-681) discharges them. It is a fact about parsed trees, and this text
   does not assume it. THE TEXTS STATE IT PER NODE (CAP, PRH_Reader.pj_ncapR): tpj_parse_specX's Some arm,
   PRH_FnCheck's tparse_noting_specX Some arm and tround_trip_text_specX's r = 0, copy <> 0 arm carry pj_ncapR of the
   accepted tree, so the caller reads `cap = ncap |ms|` off copy's header word at + 48 and `n = |ms|` off pj_nodeR. A
   permutation of sizes identifies no block, so the size multiset of copy's blocks cannot give it. pj_string's event
   is the one before, so the position here is S rp_i. *)
Lemma prhPj_set_evs_supply : forall rp_sm rp_x rp_os rp_i ms n cap,
  n = Z.of_nat (length ms) -> cap = Z.of_nat (PresetReqAt.ncap (length ms)) ->
  prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.set_evs ms) ->
  prh_run_at rp_sm rp_x rp_os (Datatypes.S rp_i) (prhPj_set_evs ms PresetReqAt.MOD_KEY n cap).
Proof.
  intros rp_sm rp_x rp_os rp_i ms n cap -> -> H.
  unfold prhPj_set_evs. rewrite prhPj_mfind_mod, !Nat2Z.id.
  unfold PresetReqAt.set_evs in H.
  assert (E : forall (a : PresetReqAt.hev) (l : list PresetReqAt.hev), a :: l = [a] ++ l) by reflexivity.
  rewrite E in H. pose proof (proj2 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H)) as H2.
  cbn [length] in H2. rewrite Nat.add_1_r in H2. exact H2.
Qed.

(* ---- pj_get / pj_get_str's results (pj_get_c.v:12-26, pj_get_str_c.v:12-27), restated over segs: the plain ones are
   stated over Img0's image-A segments ---- *)
Definition prhPj_get_res (m : word -> option byte) (lblk : Z -> Z -> Prop) (o : Z) (t : PjTree.jv) (D : list (Z * Z))
  (kname : list Z) (z : Z) : Prop :=
  match t with
  | PjTree.JObj members =>
      (forall nm u, In (nm, u) members -> nm <> kname) /\ z = 0 \/
      exists i v kids Di,
        nth_error members i = Some (kname, v) /\
        (forall j nm u, (j < i)%nat -> nth_error members j = Some (nm, u) -> nm <> kname) /\
        rd_u64 segs m (o + 24) kids /\ z = kids + 56 * Z.of_nat i /\
        pj_nodeR segs m lblk z v Di /\ incl Di D
  | _ => z = 0
  end.

Definition prhPj_get_str_res (m : word -> option byte) (lblk : Z -> Z -> Prop) (o : Z) (t : PjTree.jv)
  (D : list (Z * Z)) (kname : list Z) (z : Z) : Prop :=
  match t with
  | PjTree.JObj members =>
      (forall nm u, In (nm, u) members -> nm <> kname) /\ z = 0 \/
      exists i v kids,
        nth_error members i = Some (kname, v) /\
        (forall j nm u, (j < i)%nat -> nth_error members j = Some (nm, u) -> nm <> kname) /\
        rd_u64 segs m (o + 24) kids /\
        match v with
        | PjTree.JStr s => rd_u64 segs m (kids + 56 * Z.of_nat i + 16) z /\
            exists n, pj_cstrR segs m lblk z n s /\ In (z, n) D
        | _ => z = 0
        end
  | _ => z = 0
  end.

(* ======== the texts ======== *)

(* pj_parse (:296-309; plain pj_parse_c.v:27-69). memset (out, 0, 56); parse_value (&in, out) over [t0, t0 + len); then
   skip_ws and the end check; on any refusal pj_free (out) and -1. It reaches musl strtod (parse_value): the float-state
   form, with the entry rounding mode 0 (an arm that does not reach strtod leaves fx as it was). Its write outside its
   window and the new blocks is out's header: FP = [(out, out + 56)], caller window d; out is below alloc_ceiling
   (pj_free's empty-chain traces). Outcomes: jr_run over the outcome list ok of its allocator calls; ok follows
   prh_oks (the chosen failure fails, any other failure is the allocator's refusal, which sets g_ran_out when its
   request is at most g_most and raises g_peak in every case: the peak' conjunct's prh_refused_peak). Some t: 0, the
   tree pj_node over Lam' = D ++ Lam, D the new live blocks, every container at the reader's capacity (CAP,
   pj_ncapR); None: -1, the header zeroed (pj_zero), Lam and the allocator blocks back as they were.
   FAMILY: READING-CHAIN, POST-IMPLICATION form - no position and no run premise at entry, no rp_* binder, no grant
   list; the post states the position transfer under a run-quantified implication (the header). It calls only
   post-form texts: parse_value 0 (PRH_FnParse.v) and pj_free (out) (tpj_free_specX below). *)
Definition tpj_parse_specX (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall most own,
  forall ly S Hp W regs mem md ch d t0 len out (tl : list Z) Lam peak cnt fail ran,
  fpre B ARx STK_pj_parse ly S Hp W regs mem md ch ->
  (* the memory is normal at entry: this function's subtree reaches musl strtod (measured on BOTH rebuilt pins:
     strtod's only callers are ex_value and parse_value, and this text's subtree reaches one of them), whose row
     consumes it, and nothing below supplies it - it is seeded at main and threaded down. Same spelling and same
     reason as tex_value_specX's; see its comment for the suppliers and for the two halves of the route. *)
  YAkMemnorm.memnorm segs mem ->
  prh_univ_closure B CTX0 ->
  (* THE CURSOR SET CW, IN THE SLOT THE TWO DW MEMBERSHIPS VACATED (PRH_Base.prh_cw_pj, whose comment carries the
     reason each cursor function has ONE PINNED arm rather than a conjunction over both words): on B' the trace each
     cursor free of this subtree makes is in CW - parse_items' built from the cursor's end t0 + len, which this
     function writes at q + 8 (B' sp + 16, 0x86318 `sd a1,16(sp)`), parse_string's from the never-written slot at
     sp - pi_frame F_pj_parse, which is the cursor's q - 8 on image B. On A' both frees store the code-word trace
     (0x85e6c), which the premise does not name and need not: neither A' obligation reads it (parse_value's
     prh_cw_entry holds at every CW on A', and both A' cursor traces are fixed, ACej.v:229, :232; PRH_Base.prh_cw_pj's
     comment). |CW| = pi_univ_cur = 2, one trace per cursor function. *)
  prh_cw_pj B CW W mem regs t0 len ->
  (* THE WILD BUDGET (the room count of P''): the wild sites of this subtree are exactly those cursor frees, whose
     traces are CW, so the room is stated against the SET CW with NO fresh slot. A caller pays CW out of its own
     fresh slots (YCbqGwild.wild_room_set); that is the 2 in PRH_Base.prh_wk F_parse_noting and its family. *)
  YCbqGwild.wild_room (as_universe B) CW 0 (st_depot S) ->
  room_live_cf S -> frm_zero (@YK11.fp_csr fx) ->
  getr regs 10 = w64 t0 -> getr regs 11 = w64 len -> getr regs 12 = w64 out ->
  Z.of_nat (length tl) = len -> src_rd W mem t0 tl -> prhReader_home B ly S Hp Lam t0 len ->
  (* the reader's text ends strictly below the ceiling: parse_value's rd_pre takes it as its last conjunct
     (PRH_FnParse.rd_pre's note has the reason and the source); the caller supplies it from the harness *)
  t0 + len < YM05.alloc_ceiling ->
  Z.of_nat (PjRoundTrip.maxrun tl) < 2 ^ 30 ->
  fwin ly W regs mem d -> prhPj_slot STK_pj_parse d ly S Lam W regs mem out -> out < YM05.alloc_ceiling ->
  (forall a k, In (a, k) Lam -> out + 56 <= a \/ a + k <= out) ->
  (* the text lies apart from the out node WHEN THERE IS A TEXT: at len = 0 pj_parse reads nothing, and nothing places
     an empty text outside a fresh fake frame (the kit owner's fourth order, the reject-starved walker's crcs X1/H1 segment walk, 2026-10-29) *)
  (0 < len -> t0 + len <= out \/ out + 56 <= t0) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  cnt + 2 * len + 2 < 2 ^ 64 - 1 ->
  RQ_pj_parse tl + cf_head < cf_malloc_max ->
  (* THE REQUESTS ARE WITHIN g_most (the kit owner's batch order, ~19:5xZ; the form crcs and check_no_overread already
     take, PRH_FnCheck): every allocator request of the reading is at most g_most, so a refusal there sets g_ran_out
     (prh_alloc_post's RAN' = if n <=? most then 1 else ran), which is what the reading's refusal arms state *)
  RQ_pj_parse tl <= most ->
  blocks_bytes S + LIVE_pj_parse tl <= LIVE_MAX ->
  Z.of_nat (length (frames S)) + Z.of_nat DOC_D <= fs_frames 0 ->
  (* THE ROOM COUNTS (#102 premise-gap sweep, the room-count class): pj_parse calls parse_value 0, whose text asks the
     peaks of the secondary and class-24 counts along its ALL-GRANTED events (tparse_value_specX, over rd_hevs
     (prhPv_gtrace 0 ..)), and on a refusal pj_free (out), which asks `out <> 0 -> ccnt24 <= L24 + DRV` at its call
     (tpj_free_specX); this text carried no count. These two are the B' walker's twin's, VERBATIM up to the strtod name
     (tpj_parse_specX_pkR, commit 8a088cd72fac lib/B/Prog/pj_parse_defs.v:126-129, where
     the walk is PROVED with exactly these two added; prh_jr_strtod there is convertible to ReaderRes.jr_strtod), in the
     reading chain's spelling over the reading's all-granted events (tparse_noting_specX's, over the same list). They
     give BOTH callee needs: parse_value's by PresetRun.pkR_app (its granted events are this list's first part: the
     twin's pjc_pkR_gtrace) and pj_free (out)'s. A2, EXPLICITLY: pj_free (out)'s premise `out <> 0 ->
     YGcfRoomLive.ccnt24 S1 <= PresetLiveBounds.L24 + PresetLiveBounds.DRV` (tpj_free_specX; S1 the state at that call,
     after parse_value and skip_ws, on either refusal path) is IMPLIED by the class-24 premise below: the live set
     after ANY reading is inside the all-granted peak (the twin's pjc_cnt_run_parse, by PjGrammar.agrees_jr_value and
     PresetRun.pkR_prefix), carried to S1 by parse_value's live-set Permutation and PresetReqAt.cnt_perm, ccnt24 being
     that count by conversion - PROVED in the twin's lib/B/Prog/pj_parse_seg_c2ref.v:197-203. So NO third (ccnt24)
     premise.
     SUPPLIED (no longer open): each caller carries both verbatim - parse_noting (its callers derive them from a
     position by the driver-contract owner's PresetRoomCounts.peak_sec_of_room_pos / peak_c24_of_room_pos) and
     check_reject_clean_starved (supplied by PresetRoomCounts.peak_sec_at_tail / peak_c24_at_tail /
     peak_sec_after_rt / peak_c24_after_rt, PresetRoomCounts.v:304-372; PRH_FnCheck's note at that text). *)
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tl [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tl [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* THE HULL BUDGET (route (b) of the allocator hull premise; lib/Spec/PresetHullBudget.v,
     PRH_FnAlloc.v's header): the meters leave room for the reading's ALL-GRANTED events, the list the room counts
     above name; parse_value 0 and pj_free (out) are paid from it *)
  PresetHullBudget.hull_budget S (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []) ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.H3); fpostWFbm is already at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_pj_parse) regs mem md)
    (fpostWFbm B ARx SK (YCbqGwild.wbudget CW 0) STK_pj_parse d [(out, out + 56)] regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\
       (* THE HULL USE: at most the entry budget's list *)
       PresetHullBudget.hull_used S S' (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []) /\
       exists (ok : list bool) (res : option PjTree.jv) (tr : list PjGrammar.ev) Lam' peak' cnt' fail' ran',
       PjGrammar.jr_run ReaderRes.jr_strtod tl ok = (res, tr) /\
       prh_oks ok cnt fail (PjGrammar.calls tr) (prh_ev_reqs tr) most ran ran' /\
       cnt' = cnt + Z.of_nat (PjGrammar.calls tr) /\
       ReaderRes.fail_after cnt fail (PjGrammar.calls tr) fail' /\
       (* THE REFUSAL PEAK (#102, PRH_Base.v prh_refused_peak): the refused call's live count plus request, read off the
          granted trace prhPj_ptrace tl. COUNTEREXAMPLE to `peak' = Z.max peak (Ledger.lsum Lam + hpeakR tr)` alone:
          tl the JSON string ab (bytes 34 97 98 34), ok = [false], cnt <> fail, Lam = [], peak = 0: fuzz_malloc (3) is
          refused and g_peak = 3, while hpeakR [EFail 3] = 0. *)
       peak' = Z.max (Z.max peak (Ledger.lsum Lam + hpeakR tr))
         (prh_refused_peak ok cnt fail (PjGrammar.calls tr)
            (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds (prhPj_ptrace tl)))) /\
       hpeakR tr <= 224 * len + 16384 /\
       (cnt <= fail < cnt + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tl) -> res = None) /\
       ((fail < cnt \/ cnt + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tl) <= fail) ->
          prh_granted ok cnt fail (PjGrammar.calls tr) ->
          res = PjGrammar.json_read ReaderRes.jr_strtod tl /\
          PjGrammar.calls tr = PjGrammar.ncalls ReaderRes.jr_strtod tl) /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own /\
       (* THE POSITION TRANSFER, the post-implication form (the kit owner's ruling, 2026-10-29 ~17:25Z): for EVERY model
          run and position at which S is the position and the run's next events are THIS call's own, E =
          PresetReqAt.parse_evs ReaderRes.jr_strtod tl ok - the reader's events under the outcomes ok this call met, then on
          a refusal the HBulk of what pj_free (out) frees (PresetReqAt.pj_frees ok tl) - S' is the position at the
          EXACT advance i + length E. Only the position is under the implication; the result, the tree, the ledger
          and the blocks are unconditional. The caller chooses the run AFTER the call, to match ok, so no
          grant-list agreement is stated here (the header's OPEN CORRESPONDENCE is what the caller brings to find
          that run). The supply: prhPj_parse_evs_supply (the reading's segment of the caller's list) and, at
          check_reject_clean_starved, prhPj_parse_evs_starved (this E at ok = okk (pick x took) IS the model's
          PresetReqAt.starved_parse x took). *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i (PresetReqAt.parse_evs ReaderRes.jr_strtod tl ok) ->
          exists hist', PresetRoomPos.iface_room_pos sm x os
            (i + length (PresetReqAt.parse_evs ReaderRes.jr_strtod tl ok))%nat H0 hist' S') /\
       (* THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS): at a model run and position whose next events
          are the ALL-GRANTED reading's (parse_evs .. tl []), every allocation among them a CONSUMER event
          (PRH_Base.prh_cons_from), with no injected failure in the reading's window, the reading GRANTED: g_ran_out
          unchanged, the instance's reading IS the all-granted one (its result and trace - so res = json_read tl - and
          its events), and S' is the position at the GRANTED advance. *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []) ->
          PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.parse_evs ReaderRes.jr_strtod tl [])) ->
          (fail < cnt \/ cnt + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tl) <= fail) ->
          ran' = ran /\ PjGrammar.jr_run ReaderRes.jr_strtod tl [] = (res, tr) /\
          PresetReqAt.parse_evs ReaderRes.jr_strtod tl ok = PresetReqAt.parse_evs ReaderRes.jr_strtod tl [] /\
          exists hist', PresetRoomPos.iface_room_pos sm x os
            (i + length (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []))%nat H0 hist' S') /\
       (* THE OUTCOME OF AN INJECTED READING (GUARDED): at a model run and position whose next
          events are the reading's under the model's grant list with the chosen failure at its call fail - cnt
          (PresetReqAt.okk; at check_reject_clean_starved this list is PresetReqAt.starved_parse x took,
          prhPj_parse_evs_starved), every allocation among them a CONSUMER event (PRH_Base.prh_cons_from), with the
          chosen failure INSIDE the reading's window, no call was REFUSED: every failed outcome is the chosen one. The
          run premise names the MODEL's grant list, not the outcomes ok the post binds.
          THE SUPPLY: PRH_FnParse.tparse_value_specX's conjunct of the same name, THIS one at d = 0 over the whole
          text (its note has the per-call derivation). The walk's ACCEPTED path needs no
          supply (a refusal in the window makes res = None, so the Some arm is excluded, and an accepted value's ok
          is all-true up to calls tr by PjGrammar.agrees_some); the REFUSED path cites parse_value's conjunct. *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i
            (PresetReqAt.parse_evs ReaderRes.jr_strtod tl (PresetReqAt.okk (Z.to_nat (fail - cnt)))) ->
          PRH_Base.prh_cons_from sm x os i
            (length (PresetReqAt.parse_evs ReaderRes.jr_strtod tl (PresetReqAt.okk (Z.to_nat (fail - cnt))))) ->
          cnt <= fail < cnt + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tl) ->
          PRH_Base.prh_granted ok cnt fail (PjGrammar.calls tr)) /\
       match res with
       | Some t =>
           getr regs' 10 = w64 0 /\
           exists D, Permutation Lam' (D ++ Lam) /\
             Permutation (map snd D) (map Z.of_nat (lszR tr)) /\
             Z.of_nat (length D) = nliveR tr /\ prhPj_new ly S D /\
             Permutation (ablocks B ly' S') (prhPj_hbl D ++ ablocks B ly S) /\
             (* THE BUILT TREE'S FREE ORDER (FREEORD-NONE, the sweep's D3: tparse_noting_specX's Some-arm conjunct
                has its source here, in the same shape): for every depth bound n >= depth t, pj_free's order list F of
                out's tree carries the model's reader-side list PresetReqAt.pj_frees (the reader's own sizes; never
                fo / tblk here), IN ORDER. By citation of parse_value 0's Some arm (PRH_FnParse.v), where
                prhPv_frees 0 tl ok IS pj_frees ok tl by unfolding. CFHEAD-16: pj_frees carries
                PresetReqAt.HEAD. *)
             (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
                exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n out D F /\
                  map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod ok tl) /\
             pj_nodeR segs (rdW W' mem') (prh_lin Lam') out t D /\
             (* CAP (PRH_Reader.pj_ncapR, its comment has the source lines): every array / object node of the
                accepted tree has header cap = PresetReqAt.ncap of its count - parse_items grows cap from 0 by gcap.
                pj_nodeR alone does not pin it (only n <= cap), and neither does the size multiset of D *)
             pj_ncapR segs (rdW W' mem') out t
       | None =>
           getr regs' 10 = w64 (-1) /\ Permutation Lam' Lam /\
           Permutation (ablocks B ly' S') (ablocks B ly S) /\
           pj_zeroR segs (rdW W' mem') out
       end)).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tpj_parse_specX's POST, NAMED (read the text's post through NAMED projections; destruct once, cite
    the
   lemma). ADDITIVE: the text above is unchanged. tpjP_Q IS the text's post (tpjP_Q_check fails to build if the two ever
   differ); tpjP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas build the post
   from them. A consumer that reads and builds the post through these is not broken by the NEXT appended conjunct. ====
       *)

Definition tpjP_ASome (ly : alayout) (S : astate) (out : Z) (tl : list Z) (Lam : list (Z * Z)) (ly' : alayout) (S' :
    astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (tr : list
    PjGrammar.ev) (Lam' : list (Z * Z)) (t : PjTree.jv) : Prop :=
  getr regs' 10 = w64 0 /\ exists D, Permutation Lam' (D ++ Lam) /\ Permutation (map snd D) (map Z.of_nat (lszR tr))
    /\ Z.of_nat (length D) = nliveR tr /\ prhPj_new ly S D /\ Permutation (ablocks B ly' S') (prhPj_hbl D ++ ablocks
    B ly S) /\ (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat -> exists F, PRH_PjOrder.pj_foR
    segs (rdW W' mem') (prh_lin Lam') n out D F /\ map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees
    ReaderRes.jr_strtod ok tl) /\ pj_nodeR segs (rdW W' mem') (prh_lin Lam') out t D /\ pj_ncapR segs (rdW W' mem')
    out t.

Definition tpjP_ANone (ly : alayout) (S : astate) (out : Z) (Lam : list (Z * Z)) (ly' : alayout) (S' : astate) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) : Prop :=
  getr regs' 10 = w64 (-1) /\ Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\ pj_zeroR
    segs (rdW W' mem') out.

Definition tpjP_Q (most own : Z) (ly : alayout) (S : astate) (len out : Z) (tl : list Z) (Lam : list (Z * Z)) (peak cnt
    fail ran : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  room_live_cf S' /\ PresetHullBudget.hull_used S S' (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []) /\ exists (ok :
    list bool) (res : option PjTree.jv) (tr : list PjGrammar.ev) Lam' peak' cnt' fail'
    ran', PjGrammar.jr_run ReaderRes.jr_strtod tl ok = (res, tr) /\ prh_oks ok cnt fail (PjGrammar.calls tr)
    (prh_ev_reqs tr) most ran ran' /\ cnt' = cnt + Z.of_nat (PjGrammar.calls tr) /\ ReaderRes.fail_after cnt fail
    (PjGrammar.calls tr) fail' /\ peak' = Z.max (Z.max peak (Ledger.lsum Lam + hpeakR tr)) (prh_refused_peak ok cnt
    fail (PjGrammar.calls tr) (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds (prhPj_ptrace tl)))) /\ hpeakR tr <= 224 *
    len + 16384 /\ (cnt <= fail < cnt + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tl) -> res = None) /\ ((fail <
    cnt \/ cnt + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tl) <= fail) -> prh_granted ok cnt fail
    (PjGrammar.calls tr) -> res = PjGrammar.json_read ReaderRes.jr_strtod tl /\ PjGrammar.calls tr = PjGrammar.ncalls
    ReaderRes.jr_strtod tl) /\ prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own /\ (forall (sm :
    list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist :
    list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tl ok) -> exists hist', PresetRoomPos.iface_room_pos sm x os (i +
    length (PresetReqAt.parse_evs ReaderRes.jr_strtod tl ok))%nat H0 hist' S') /\ (forall (sm : list Z -> Z * Z) (x :
    list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (PresetReqAt.parse_evs
    ReaderRes.jr_strtod tl []) -> PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.parse_evs ReaderRes.jr_strtod
    tl [])) -> (fail < cnt \/ cnt + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tl) <= fail) -> ran' = ran /\
    PjGrammar.jr_run ReaderRes.jr_strtod tl [] = (res, tr) /\ PresetReqAt.parse_evs ReaderRes.jr_strtod tl ok =
    PresetReqAt.parse_evs ReaderRes.jr_strtod tl [] /\ exists hist', PresetRoomPos.iface_room_pos sm x os (i + length
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []))%nat H0 hist' S') /\ (forall (sm : list Z -> Z * Z) (x : list
    Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (PresetReqAt.parse_evs
    ReaderRes.jr_strtod tl (PresetReqAt.okk (Z.to_nat (fail - cnt)))) -> PRH_Base.prh_cons_from sm x os i (length
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tl (PresetReqAt.okk (Z.to_nat (fail - cnt))))) -> cnt <= fail < cnt +
    Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tl) -> PRH_Base.prh_granted ok cnt fail (PjGrammar.calls tr)) /\
    match res with | Some t => tpjP_ASome ly S out tl Lam ly' S' W' regs' mem' ok tr Lam' t | None => tpjP_ANone ly S
    out Lam ly' S' W' regs' mem' Lam' end.

Lemma tpjP_Q_check : forall (CTX0 CW : list (list Z)), tpj_parse_specX CTX0 CW -> tpj_parse_specX CTX0 CW.
Proof.
  intros CTX0 CW H. unfold tpj_parse_specX in *.
  intros most own ly S Hp W regs mem md ch d t0 len out tl Lam peak cnt fail ran.
  specialize (H most own ly S Hp W regs mem md ch d t0 len out tl Lam peak cnt fail ran).
  (* the conclusion is SRr' (the re-hiding move), so the post is found under SRr' *)
  lazymatch type of H with context [SRr' _ _ _ _ (?F ?Q)] => change Q with (tpjP_Q most own ly S len out tl Lam peak cnt
      fail ran) in H end.
  exact H.
Qed.

Record tpjP_R (most own : Z) (ly : alayout) (S : astate) (len out : Z) (tl : list Z) (Lam : list (Z * Z)) (peak cnt
    fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word ->
    option byte) (ok : list bool) (res : option PjTree.jv) (tr : list PjGrammar.ev) (Lam' : list (Z * Z)) (peak' cnt'
    fail' ran' : Z) : Prop := {
  tpjP_room : room_live_cf S';
  tpjP_hull : PresetHullBudget.hull_used S S' (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []);
  tpjP_run : PjGrammar.jr_run ReaderRes.jr_strtod tl ok = (res, tr);
  tpjP_oks : prh_oks ok cnt fail (PjGrammar.calls tr) (prh_ev_reqs tr) most ran ran';
  tpjP_cnt : cnt' = cnt + Z.of_nat (PjGrammar.calls tr);
  tpjP_fail : ReaderRes.fail_after cnt fail (PjGrammar.calls tr) fail';
  tpjP_peak : peak' = Z.max (Z.max peak (Ledger.lsum Lam + hpeakR tr)) (prh_refused_peak ok cnt fail (PjGrammar.calls
    tr) (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds (prhPj_ptrace tl))));
  tpjP_hpeak : hpeakR tr <= 224 * len + 16384;
  tpjP_window_none : (cnt <= fail < cnt + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tl) -> res = None);
  tpjP_granted : ((fail < cnt \/ cnt + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tl) <= fail) -> prh_granted ok
    cnt fail (PjGrammar.calls tr) -> res = PjGrammar.json_read ReaderRes.jr_strtod tl /\ PjGrammar.calls tr =
    PjGrammar.ncalls ReaderRes.jr_strtod tl);
  tpjP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own;
  tpjP_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at
    sm x os i (PresetReqAt.parse_evs ReaderRes.jr_strtod tl ok) -> exists hist', PresetRoomPos.iface_room_pos sm x os
    (i + length (PresetReqAt.parse_evs ReaderRes.jr_strtod tl ok))%nat H0 hist' S');
  tpjP_outcome : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []) -> PRH_Base.prh_cons_from sm x os
    i (length (PresetReqAt.parse_evs ReaderRes.jr_strtod tl [])) -> (fail < cnt \/ cnt + Z.of_nat (PjGrammar.ncalls
    ReaderRes.jr_strtod tl) <= fail) -> ran' = ran /\ PjGrammar.jr_run ReaderRes.jr_strtod tl [] = (res, tr) /\
    PresetReqAt.parse_evs ReaderRes.jr_strtod tl ok = PresetReqAt.parse_evs ReaderRes.jr_strtod tl [] /\ exists
    hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []))%nat H0
    hist' S');
  tpjP_injected : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.parse_evs ReaderRes.jr_strtod tl (PresetReqAt.okk (Z.to_nat (fail -
    cnt)))) -> PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.parse_evs ReaderRes.jr_strtod tl
    (PresetReqAt.okk (Z.to_nat (fail - cnt))))) -> cnt <= fail < cnt + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod
    tl) -> PRH_Base.prh_granted ok cnt fail (PjGrammar.calls tr));
  tpjP_arm : match res with | Some t => tpjP_ASome ly S out tl Lam ly' S' W' regs' mem' ok tr Lam' t | None =>
    tpjP_ANone ly S out Lam ly' S' W' regs' mem' Lam' end }.

Lemma tpjP_R_of : forall (most own : Z) (ly : alayout) (S : astate) (len out : Z) (tl : list Z) (Lam : list (Z * Z))
    (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem'
    : word -> option byte) (md' : Model),
  tpjP_Q most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' ->
  exists ok res tr Lam' peak' cnt' fail' ran', tpjP_R most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W'
      regs' mem' ok res tr Lam' peak' cnt' fail' ran'.
Proof.
  intros most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' H. destruct H as (H0 & Hh & ok &
      res & tr & Lam' & peak' & cnt' & fail' & ran' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 &
      H13).
  exists ok, res, tr, Lam', peak', cnt', fail', ran'.
  exact {| tpjP_room := H0; tpjP_hull := Hh; tpjP_run := H1; tpjP_oks := H2; tpjP_cnt := H3; tpjP_fail := H4;
      tpjP_peak := H5; tpjP_hpeak := H6; tpjP_window_none := H7; tpjP_granted := H8; tpjP_ledger := H9; tpjP_pos :=
      H10; tpjP_outcome := H11; tpjP_injected := H12; tpjP_arm := H13 |}.
Qed.

Lemma tpjP_Q_of_R : forall (most own : Z) (ly : alayout) (S : astate) (len out : Z) (tl : list Z) (Lam : list (Z * Z))
    (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem'
    : word -> option byte) (md' : Model) (ok : list bool) (res : option PjTree.jv) (tr : list PjGrammar.ev) (Lam' :
    list (Z * Z)) (peak' cnt' fail' ran' : Z),
  tpjP_R most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ok res tr Lam' peak' cnt' fail' ran' ->
  tpjP_Q most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md'.
Proof.
  intros most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' ok res tr Lam' peak' cnt' fail'
      ran' HR.
  refine (conj (tpjP_room HR) (conj (tpjP_hull HR) _)).
  exists ok, res, tr, Lam', peak', cnt', fail', ran'.
  exact (conj (tpjP_run HR) (conj (tpjP_oks HR) (conj (tpjP_cnt HR) (conj (tpjP_fail HR) (conj (tpjP_peak HR) (conj
      (tpjP_hpeak HR) (conj (tpjP_window_none HR) (conj (tpjP_granted HR) (conj (tpjP_ledger HR) (conj (tpjP_pos HR)
      (conj (tpjP_outcome HR) (conj (tpjP_injected HR) (tpjP_arm HR))))))))))))).
Qed.

(* the CONSEQUENTS of the post's guarded conjuncts, NAMED: each conjunct of an implication's conclusion, read from the
   record through one lemma (a consumer that applies the guard and destructs its conclusion is not broken
   by the next conjunct appended there) *)

Lemma tpjP_granted_read : forall (most own : Z) (ly : alayout) (S : astate) (len out : Z) (tl : list Z) (Lam : list (Z
    * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (ok : list bool) (res : option PjTree.jv) (tr : list PjGrammar.ev) (Lam' : list (Z *
    Z)) (peak' cnt' fail' ran' : Z),
  tpjP_R most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ok res tr Lam' peak' cnt' fail' ran' ->
  (fail < cnt \/ cnt + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tl) <= fail) -> prh_granted ok cnt fail
      (PjGrammar.calls tr) ->
  res = PjGrammar.json_read ReaderRes.jr_strtod tl.
Proof.
  intros most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ok res tr Lam' peak' cnt' fail' ran'
      HR HP0 HP1.
  exact (proj1 (tpjP_granted HR HP0 HP1)).
Qed.

Lemma tpjP_granted_calls : forall (most own : Z) (ly : alayout) (S : astate) (len out : Z) (tl : list Z) (Lam : list (Z
    * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (ok : list bool) (res : option PjTree.jv) (tr : list PjGrammar.ev) (Lam' : list (Z *
    Z)) (peak' cnt' fail' ran' : Z),
  tpjP_R most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ok res tr Lam' peak' cnt' fail' ran' ->
  (fail < cnt \/ cnt + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tl) <= fail) -> prh_granted ok cnt fail
      (PjGrammar.calls tr) ->
  PjGrammar.calls tr = PjGrammar.ncalls ReaderRes.jr_strtod tl.
Proof.
  intros most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ok res tr Lam' peak' cnt' fail' ran'
      HR HP0 HP1.
  exact (proj2 (tpjP_granted HR HP0 HP1)).
Qed.

Lemma tpjP_outcome_ran : forall (most own : Z) (ly : alayout) (S : astate) (len out : Z) (tl : list Z) (Lam : list (Z *
    Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (ok : list bool) (res : option PjTree.jv) (tr : list PjGrammar.ev) (Lam' : list (Z *
    Z)) (peak' cnt' fail' ran' : Z),
  tpjP_R most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ok res tr Lam' peak' cnt' fail' ran' ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []) -> PRH_Base.prh_cons_from sm x os i (length
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tl [])) -> (fail < cnt \/ cnt + Z.of_nat (PjGrammar.ncalls
      ReaderRes.jr_strtod tl) <= fail) ->
  ran' = ran.
Proof.
  intros most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ok res tr Lam' peak' cnt' fail' ran'
      HR sm x os i H0 hist HP0 HP1 HP2 HP3.
  exact (proj1 (tpjP_outcome HR HP0 HP1 HP2 HP3)).
Qed.

Lemma tpjP_outcome_run : forall (most own : Z) (ly : alayout) (S : astate) (len out : Z) (tl : list Z) (Lam : list (Z *
    Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (ok : list bool) (res : option PjTree.jv) (tr : list PjGrammar.ev) (Lam' : list (Z *
    Z)) (peak' cnt' fail' ran' : Z),
  tpjP_R most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ok res tr Lam' peak' cnt' fail' ran' ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []) -> PRH_Base.prh_cons_from sm x os i (length
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tl [])) -> (fail < cnt \/ cnt + Z.of_nat (PjGrammar.ncalls
      ReaderRes.jr_strtod tl) <= fail) ->
  PjGrammar.jr_run ReaderRes.jr_strtod tl [] = (res, tr).
Proof.
  intros most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ok res tr Lam' peak' cnt' fail' ran'
      HR sm x os i H0 hist HP0 HP1 HP2 HP3.
  exact (proj1 (proj2 (tpjP_outcome HR HP0 HP1 HP2 HP3))).
Qed.

Lemma tpjP_outcome_evs : forall (most own : Z) (ly : alayout) (S : astate) (len out : Z) (tl : list Z) (Lam : list (Z *
    Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (ok : list bool) (res : option PjTree.jv) (tr : list PjGrammar.ev) (Lam' : list (Z *
    Z)) (peak' cnt' fail' ran' : Z),
  tpjP_R most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ok res tr Lam' peak' cnt' fail' ran' ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []) -> PRH_Base.prh_cons_from sm x os i (length
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tl [])) -> (fail < cnt \/ cnt + Z.of_nat (PjGrammar.ncalls
      ReaderRes.jr_strtod tl) <= fail) ->
  PresetReqAt.parse_evs ReaderRes.jr_strtod tl ok = PresetReqAt.parse_evs ReaderRes.jr_strtod tl [].
Proof.
  intros most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ok res tr Lam' peak' cnt' fail' ran'
      HR sm x os i H0 hist HP0 HP1 HP2 HP3.
  exact (proj1 (proj2 (proj2 (tpjP_outcome HR HP0 HP1 HP2 HP3)))).
Qed.

Lemma tpjP_outcome_pos : forall (most own : Z) (ly : alayout) (S : astate) (len out : Z) (tl : list Z) (Lam : list (Z *
    Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (ok : list bool) (res : option PjTree.jv) (tr : list PjGrammar.ev) (Lam' : list (Z *
    Z)) (peak' cnt' fail' ran' : Z),
  tpjP_R most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ok res tr Lam' peak' cnt' fail' ran' ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []) -> PRH_Base.prh_cons_from sm x os i (length
      (PresetReqAt.parse_evs ReaderRes.jr_strtod tl [])) -> (fail < cnt \/ cnt + Z.of_nat (PjGrammar.ncalls
      ReaderRes.jr_strtod tl) <= fail) ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []))%nat
      H0 hist' S'.
Proof.
  intros most own ly S len out tl Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ok res tr Lam' peak' cnt' fail' ran'
      HR sm x os i H0 hist HP0 HP1 HP2 HP3.
  exact (proj2 (proj2 (proj2 (tpjP_outcome HR HP0 HP1 HP2 HP3)))).
Qed.


Record tpjP_RSome (ly : alayout) (S : astate) (out : Z) (tl : list Z) (Lam : list (Z * Z)) (ly' : alayout) (S' :
    astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (tr : list
    PjGrammar.ev) (Lam' : list (Z * Z)) (t : PjTree.jv) (D : list (Z * Z)) : Prop := {
  tpjPs_ret : getr regs' 10 = w64 0;
  tpjPs_lam : Permutation Lam' (D ++ Lam);
  tpjPs_sizes : Permutation (map snd D) (map Z.of_nat (lszR tr));
  tpjPs_nlive : Z.of_nat (length D) = nliveR tr;
  tpjPs_new : prhPj_new ly S D;
  tpjPs_ablocks : Permutation (ablocks B ly' S') (prhPj_hbl D ++ ablocks B ly S);
  tpjPs_freeord : (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat -> exists F, PRH_PjOrder.pj_foR
    segs (rdW W' mem') (prh_lin Lam') n out D F /\ map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees
    ReaderRes.jr_strtod ok tl);
  tpjPs_node : pj_nodeR segs (rdW W' mem') (prh_lin Lam') out t D;
  tpjPs_ncap : pj_ncapR segs (rdW W' mem') out t }.

Lemma tpjP_RSome_of : forall (ly : alayout) (S : astate) (out : Z) (tl : list Z) (Lam : list (Z * Z)) (ly' : alayout)
    (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (tr : list
    PjGrammar.ev) (Lam' : list (Z * Z)) (t : PjTree.jv),
  tpjP_ASome ly S out tl Lam ly' S' W' regs' mem' ok tr Lam' t ->
  exists D, tpjP_RSome ly S out tl Lam ly' S' W' regs' mem' ok tr Lam' t D.
Proof.
  intros ly S out tl Lam ly' S' W' regs' mem' ok tr Lam' t H. destruct H as (H0 & D & H1 & H2 & H3 & H4 & H5 & H6 & H7
      & H8).
  exists D.
  exact {| tpjPs_ret := H0; tpjPs_lam := H1; tpjPs_sizes := H2; tpjPs_nlive := H3; tpjPs_new := H4; tpjPs_ablocks :=
      H5; tpjPs_freeord := H6; tpjPs_node := H7; tpjPs_ncap := H8 |}.
Qed.

Lemma tpjP_ASome_of_R : forall (ly : alayout) (S : astate) (out : Z) (tl : list Z) (Lam : list (Z * Z)) (ly' : alayout)
    (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (tr : list
    PjGrammar.ev) (Lam' : list (Z * Z)) (t : PjTree.jv) (D : list (Z * Z)),
  tpjP_RSome ly S out tl Lam ly' S' W' regs' mem' ok tr Lam' t D ->
  tpjP_ASome ly S out tl Lam ly' S' W' regs' mem' ok tr Lam' t.
Proof.
  intros ly S out tl Lam ly' S' W' regs' mem' ok tr Lam' t D HR.
  refine (conj (tpjPs_ret HR) _).
  exists D.
  exact (conj (tpjPs_lam HR) (conj (tpjPs_sizes HR) (conj (tpjPs_nlive HR) (conj (tpjPs_new HR) (conj (tpjPs_ablocks
      HR) (conj (tpjPs_freeord HR) (conj (tpjPs_node HR) (tpjPs_ncap HR)))))))).
Qed.


Record tpjP_RNone (ly : alayout) (S : astate) (out : Z) (Lam : list (Z * Z)) (ly' : alayout) (S' : astate) (W' : world
    segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)) : Prop := {
  tpjPn_ret : getr regs' 10 = w64 (-1);
  tpjPn_lam : Permutation Lam' Lam;
  tpjPn_ablocks : Permutation (ablocks B ly' S') (ablocks B ly S);
  tpjPn_zero : pj_zeroR segs (rdW W' mem') out }.

Lemma tpjP_RNone_of : forall (ly : alayout) (S : astate) (out : Z) (Lam : list (Z * Z)) (ly' : alayout) (S' : astate)
    (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)),
  tpjP_ANone ly S out Lam ly' S' W' regs' mem' Lam' ->
  tpjP_RNone ly S out Lam ly' S' W' regs' mem' Lam'.
Proof.
  intros ly S out Lam ly' S' W' regs' mem' Lam' H. destruct H as (H0 & H1 & H2 & H3).
  exact {| tpjPn_ret := H0; tpjPn_lam := H1; tpjPn_ablocks := H2; tpjPn_zero := H3 |}.
Qed.

Lemma tpjP_ANone_of_R : forall (ly : alayout) (S : astate) (out : Z) (Lam : list (Z * Z)) (ly' : alayout) (S' : astate)
    (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (Lam' : list (Z * Z)),
  tpjP_RNone ly S out Lam ly' S' W' regs' mem' Lam' ->
  tpjP_ANone ly S out Lam ly' S' W' regs' mem' Lam'.
Proof.
  intros ly S out Lam ly' S' W' regs' mem' Lam' HR.
  exact (conj (tpjPn_ret HR) (conj (tpjPn_lam HR) (conj (tpjPn_ablocks HR) (tpjPn_zero HR)))).
Qed.

Local Unset Implicit Arguments.

(* pj_free (:334-350; plain pj_free_c.v:23-44), n more nested calls of itself. v = NULL returns. Otherwise, for each of
   the n slots, pj_free (&kids[i]) and fuzz_free (keys[i]); fuzz_free (kids), (keys), (str); memset (v, 0, 56). The tree
   is pj_foR n (PRH_PjOrder.v: PRH_Reader's pj_fdR - freeable, at most n levels below v - with the list F of its
   blocks IN THE ORDER pj_free frees them, which is the order the model's HBulk event carries) over the harness
   blocks; every block of D is freed (in FP, with v's header), Lam loses exactly D, the counters stay. Its four
   fuzz_free calls have s0 = v below alloc_ceiling (a block or a fake frame), so their traces are closure literals.
   F IS NOT A NEW OBLIGATION: every pj_fdR tree has one (PRH_PjOrder.pj_fdR_foR), and it is a permutation of D
   (pj_foR_fdR), so a caller that had the old premise has this one.
   FAMILY: LEAF, POST-IMPLICATION form - no position and no run premise at entry, no rp_* binder; the post states
   the position transfer under a run-quantified implication (the header). It calls only post-form texts: itself
   and fuzz_free (PRH_FnAlloc.tfuzz_free_specX, a leaf). *)
Definition tpj_free_specX (CTX0 : list (list Z)) (n : nat) : Prop :=
  forall most own,
  forall ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran,
  fpre B ARx (STK_pj_free n) ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 -> room_live_cf S ->
  (* THE CLASS-24 BOUND AT ENTRY, a NAMED PREMISE, position-free (the kit owner's ruling and ORDER 1 + 2, 2026-10-29),
     needed only when v <> 0: pj_free (NULL) returns before any call, so that arm takes no room premise. Otherwise
     pj_free's first fuzz_free call of a non-NULL pointer asks it (tfuzz_free_specX's entry premise), and every
     later one gets it back from the one before, because a free never raises ccnt24 (the S1 owner's internal file CCNT24-FREE.md:
     the count of live class-24 blocks, which a free lowers by its own block or leaves alone). The caller has the
     room facts and supplies it; it is NOT derived here from a position through counts_of_room_pos_rl, which would
     pull PresetLiveSec and the plain lib/Prog/*_c.v files into the kit's closure. *)
  (v <> 0 -> YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV) ->
  (* THE HULL BUDGET (lib/Spec/PresetHullBudget.v): the admission for its fuzz_free calls, needed
     only when v <> 0 (pj_free (NULL) returns before any call); frees make no secondary entry *)
  (v <> 0 -> PresetHullBudget.hull_budget S []) ->
  getr regs 10 = w64 v ->
  fwin ly W regs mem d ->
  (v = 0 /\ D = [] /\ F = [] \/
   v <> 0 /\ v < YM05.alloc_ceiling /\ pj_foR segs (rdW W mem) (prh_lin Lam) n v D F /\
   prhPj_slot (STK_pj_free n) d ly S Lam W regs mem v) ->
  (* THE HEAD IS AT LEAST ONE WORD WIDE (CFHEAD-16's family, the kit owner's check order 2026-10-29 ~19:4xZ, the
     second of the image-B pj walker's two reasons): pj_free zeroes every node it frees (src/preset_file.c:349, memset (v, 0,
     sizeof *v); pj_zeroR below), and its recursive call on each kids[i] (:342) zeroes that slot INSIDE the live kids
     block before free (v->kids) (:346). With cf_head < 8 the
     zeroing of kids[0], which starts the block, overwrites part of the block's head word, so the fuzz_free (kids)
     that follows reads a broken head and the ledger after it is false - the same hole as tpj_string_specX's memset.
     Preset's cf_head is 16 (the allocator-model owner's preset_head_wide discharges it); the kit's one spelling, PRH_Base.v's
     prh_head_wide := 8 <= cf_head. *)
  prh_head_wide ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.9): fpostWm is SHARED, so the post is its R
     form at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_pj_free) regs mem md)
    (fpostWmR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) (STK_pj_free n) d
       (if v =? 0 then [] else (v, v + 56) :: ablocks_fp (prhPj_hbl D))
       regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\
       (* THE HULL USE: frees keep both meters *)
       PresetHullBudget.hull_used S S' [] /\
       (* THE POSITION TRANSFER, the post-implication form (the kit owner's ruling, 2026-10-29 ~17:25Z), unconditional
          in the outcome: pj_free allocates nothing, so no outcome can make it diverge from the model. For EVERY
          model run and position at which S is the position and the run's next events are E = prhPj_free_evs F -
          one bulk free of its order list's requests, none at all when that list is empty (F2, the header: a NULL
          argument, an accepted document with no blocks, where the model emits HBulk [] and the caller steps over it
          by prhPj_bulk_nil_pos, or the zeroed node a refused pj_parse left, where the model emits nothing) - S' is
          the position at the EXACT advance i + length E (at F = [] the implication is the identity on the
          position). The supply: prhPj_free_evs_supply from the caller's HBulk Lb and the ORDERED tie of F to Lb -
          reader-built Lb = PresetReqAt.pj_frees sm ok x, the tie a conjunct of the text that built the tree
          (tpj_parse_specX's Some arm, PRH_FnCheck.tparse_noting_specX; PJF-TIE closed); read back from the
          writer's text Lb = PresetReqAt.fo t, by prhPj_free_evs_supply_fo (PresetFreeFo.pj_frees_wdoc_t under
          pj_wf sm t) - or prhPj_free_evs_nil at a zeroed node. A PERMUTATION of Lb never supplies this: the
          position reads the free history in order (prhPj_free_evs_supply's note). *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i (prhPj_free_evs F) ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPj_free_evs F))%nat H0 hist' S') /\
       exists Lam', Permutation Lam (D ++ Lam') /\
       Permutation (ablocks B ly S) (prhPj_hbl D ++ ablocks B ly' S') /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak cnt fail ran most own /\
       (v = 0 -> Lam' = Lam /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S) /\
       (v <> 0 -> pj_zeroR segs (rdW W' mem') v) /\
       (* the count never rises across the frees, so the caller keeps its bound *)
       YGcfRoomLive.ccnt24 S' <= YGcfRoomLive.ccnt24 S)).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tpj_free_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. tpfP_Q IS the text's post (tpfP_Q_check fails to build if
   the two ever differ); tpfP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition tpfP_Q (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v : Z) (D F Lam : list (Z * Z)) (peak cnt
    fail ran : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  room_live_cf S' /\ PresetHullBudget.hull_used S S' [] /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os : list
      (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
      PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (prhPj_free_evs F) -> exists
      hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPj_free_evs F))%nat H0 hist' S') /\ exists Lam',
      Permutation Lam (D ++ Lam') /\ Permutation (ablocks B ly S) (prhPj_hbl D ++ ablocks B ly' S') /\ prh_ledger B ly'
      S' Hp' W' mem' Lam' peak cnt fail ran most own /\ (v = 0 -> Lam' = Lam /\ Hp' = Hp /\ ablocks B ly' S' = ablocks
      B ly S) /\ (v <> 0 -> pj_zeroR segs (rdW W' mem') v) /\ YGcfRoomLive.ccnt24 S' <= YGcfRoomLive.ccnt24 S.

Lemma tpfP_Q_check : forall (CTX0 : list (list Z)) (n : nat), tpj_free_specX CTX0 n -> tpj_free_specX CTX0 n.
Proof.
  intros CTX0 n H. unfold tpj_free_specX in *.
  intros most own ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (tpfP_Q most own ly S Hp v D F Lam
      peak cnt fail ran) end.
  exact (H most own ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9).
Qed.

Record tpfP_R (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v : Z) (D F Lam : list (Z * Z)) (peak cnt fail
    ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word ->
    option byte) (Lam' : list (Z * Z)) : Prop := {
  tpfP_room : room_live_cf S';
  tpfP_hull : PresetHullBudget.hull_used S S' [];
  tpfP_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
      (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at
      sm x os i (prhPj_free_evs F) -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPj_free_evs
      F))%nat H0 hist' S');
  tpfP_lam : Permutation Lam (D ++ Lam');
  tpfP_ablocks : Permutation (ablocks B ly S) (prhPj_hbl D ++ ablocks B ly' S');
  tpfP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' peak cnt fail ran most own;
  tpfP_null : (v = 0 -> Lam' = Lam /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S);
  tpfP_zero : (v <> 0 -> pj_zeroR segs (rdW W' mem') v);
  tpfP_ccnt24 : YGcfRoomLive.ccnt24 S' <= YGcfRoomLive.ccnt24 S }.

Lemma tpfP_R_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v : Z) (D F Lam : list (Z * Z))
    (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem'
    : word -> option byte) (md' : Model),
  tpfP_Q most own ly S Hp v D F Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' ->
  exists Lam', tpfP_R most own ly S Hp v D F Lam peak cnt fail ran ly' S' Hp' W' regs' mem' Lam'.
Proof.
  intros most own ly S Hp v D F Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' H. destruct H as (H0 & H1 & H2 &
      Lam' & H3 & H4 & H5 & H6 & H7 & H8).
  exists Lam'.
  exact {| tpfP_room := H0; tpfP_hull := H1; tpfP_pos := H2; tpfP_lam := H3; tpfP_ablocks := H4; tpfP_ledger := H5;
      tpfP_null := H6; tpfP_zero := H7; tpfP_ccnt24 := H8 |}.
Qed.

Lemma tpfP_Q_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v : Z) (D F Lam : list (Z * Z))
    (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem'
    : word -> option byte) (md' : Model) (Lam' : list (Z * Z)),
  tpfP_R most own ly S Hp v D F Lam peak cnt fail ran ly' S' Hp' W' regs' mem' Lam' ->
  tpfP_Q most own ly S Hp v D F Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md'.
Proof.
  intros most own ly S Hp v D F Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' Lam' HR.
  refine (conj (tpfP_room HR) (conj (tpfP_hull HR) (conj (tpfP_pos HR) _))).
  exists Lam'.
  exact (conj (tpfP_lam HR) (conj (tpfP_ablocks HR) (conj (tpfP_ledger HR) (conj (tpfP_null HR) (conj (tpfP_zero HR)
      (tpfP_ccnt24 HR)))))).
Qed.

(* the CONSEQUENTS of tpfP_R's guarded conjuncts, NAMED: each conjunct of an implication's conclusion, read from
   the record through one lemma (a consumer that applies the guard and destructs its conclusion is not broken by the
   next conjunct appended there) *)

Lemma tpfP_null_lam : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v : Z) (D F Lam : list (Z * Z))
    (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem'
    : word -> option byte) (Lam' : list (Z * Z)),
  tpfP_R most own ly S Hp v D F Lam peak cnt fail ran ly' S' Hp' W' regs' mem' Lam' ->
  v = 0 ->
  Lam' = Lam.
Proof.
  intros most own ly S Hp v D F Lam peak cnt fail ran ly' S' Hp' W' regs' mem' Lam' HR HP0.
  pose proof (tpfP_null HR) as G.
  exact (proj1 (G HP0)).
Qed.

Lemma tpfP_null_hp : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v : Z) (D F Lam : list (Z * Z))
    (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem'
    : word -> option byte) (Lam' : list (Z * Z)),
  tpfP_R most own ly S Hp v D F Lam peak cnt fail ran ly' S' Hp' W' regs' mem' Lam' ->
  v = 0 ->
  Hp' = Hp.
Proof.
  intros most own ly S Hp v D F Lam peak cnt fail ran ly' S' Hp' W' regs' mem' Lam' HR HP0.
  pose proof (tpfP_null HR) as G.
  exact (proj1 (proj2 (G HP0))).
Qed.

Lemma tpfP_null_ablocks : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v : Z) (D F Lam : list (Z *
    Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (Lam' : list (Z * Z)),
  tpfP_R most own ly S Hp v D F Lam peak cnt fail ran ly' S' Hp' W' regs' mem' Lam' ->
  v = 0 ->
  ablocks B ly' S' = ablocks B ly S.
Proof.
  intros most own ly S Hp v D F Lam peak cnt fail ran ly' S' Hp' W' regs' mem' Lam' HR HP0.
  pose proof (tpfP_null HR) as G.
  exact (proj2 (proj2 (G HP0))).
Qed.

Local Unset Implicit Arguments.

(* pj_get (:352-362; plain pj_get_c.v:28-51): NULL or not an object gives NULL; else the first member whose key strcmp
   finds equal (&kids[i]), or NULL. Reads only: FP empty, no allocator call (room_live_cf kept). The key is read by the strcmp
   interceptor (cstr_ok); its bytes after the call are the journal's to keep (where the caller placed it). *)
Definition tpj_get_specX : Prop :=
  forall ly S Hp W regs mem md ch o k (kname : list Z) (t : PjTree.jv) D Lam peak cnt fail ran most own,
  fpre B ARx STK_pj_get ly S Hp W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 11 = w64 k ->
  (o = 0 \/ pj_nodeR segs (rdW W mem) (prh_lin Lam) o t D /\ prhPj_rslot STK_pj_get ly S W regs mem o) ->
  cstr_ok W mem k kname ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_pj_get) regs mem md)
    (fpostm B ARx SK STK_pj_get [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       (room_live_cf S -> room_live_cf S') /\
       (o = 0 /\ getr regs' 10 = w64 0 \/
        o <> 0 /\ pj_nodeR segs (rdW W' mem') (prh_lin Lam) o t D /\
        exists z, getr regs' 10 = w64 z /\ prhPj_get_res (rdW W' mem') (prh_lin Lam) o t D kname z))).

(* pj_get_str (:364-369; plain pj_get_str_c.v:29-52): pj_get, then the member's str when it is a string, else NULL;
   no allocator call (room_live_cf kept) *)
Definition tpj_get_str_specX : Prop :=
  forall ly S Hp W regs mem md ch o k (kname : list Z) (t : PjTree.jv) D Lam peak cnt fail ran most own,
  fpre B ARx STK_pj_get_str ly S Hp W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 11 = w64 k ->
  (o = 0 \/ pj_nodeR segs (rdW W mem) (prh_lin Lam) o t D /\ prhPj_rslot STK_pj_get_str ly S W regs mem o) ->
  cstr_ok W mem k kname ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_pj_get_str) regs mem md)
    (fpostm B ARx SK STK_pj_get_str [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       (room_live_cf S -> room_live_cf S') /\
       (o = 0 /\ getr regs' 10 = w64 0 \/
        o <> 0 /\ pj_nodeR segs (rdW W' mem') (prh_lin Lam) o t D /\
        exists z, getr regs' 10 = w64 z /\ prhPj_get_str_res (rdW W' mem') (prh_lin Lam) o t D kname z))).

(* the allocator requests pj_set's absent-key arm makes, in order (pj_set_c.v:17-20 set_trace, restated at
   klen = length kname): when n = cap the kids and keys reallocs to cap2, then the strdup of the key *)
Definition prhPj_set_trace (n cap : Z) (kname : list Z) : list PjGrammar.ev :=
  (if n =? cap then [PjGrammar.EGrow (Z.to_nat (56 * cap)) (Z.to_nat (56 * cap2R cap));
                     PjGrammar.EGrow (Z.to_nat (8 * cap)) (Z.to_nat (8 * cap2R cap))] else []) ++
  [PjGrammar.EAlloc (Z.to_nat (Z.of_nat (length kname) + 1))].

(* ---- THE REFUSAL PEAK OF pj_set's ABSENT-KEY ARM, EVALUATED (the kit owner's check order 2026-10-29, on
   the image-B pj walker's site). The rule: at a refusal, the `ran` half and the `peak` half are SEPARATE obligations, each
   keyed on the CALLEE, and the peak must be refused()'s own expression - g_peak = max (g_peak, min (SIZE_MAX,
   g_live + n)) at the g_live of the moment (merged alloc.c:70-78, refused(); PRH_Base.prh_refused_peak's note;
   PRH_FnAlloc.prh_alloc_post's refusal arm states the same shape, Z.max peak (Z.min SIZE_MAXZ
   (Ledger.lsum Lam + n))). These two lemmas CHECK that the term the arm already carries IS that expression on the
   STRDUP refusal, so the kit keeps ONE definition, PRH_Base.prh_refused_peak, and states no second form. ---- *)

Lemma prh_fold_max_nonneg : forall l, 0 <= fold_right Z.max 0 l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [fold_right]. lia. Qed.

Lemma prh_fold_max_app : forall l1 l2,
  fold_right Z.max 0 (l1 ++ l2) = Z.max (fold_right Z.max 0 l1) (fold_right Z.max 0 l2).
Proof.
  induction l1 as [|x l1 IH]; intros l2; cbn [app fold_right].
  - pose proof (prh_fold_max_nonneg l2). lia.
  - rewrite IH. lia.
Qed.

Lemma prh_max0 : forall v : Z, Z.max 0 (Z.max v 0) = Z.max 0 v.
Proof.
  intro v. destruct (Z.le_gt_cases 0 v) as [Hv|Hv].
  - rewrite (Z.max_l v 0) by exact Hv. reflexivity.
  - rewrite (Z.max_r v 0) by lia. rewrite (Z.max_l 0 v) by lia. apply Z.max_id.
Qed.

(* the whole peak of k + 1 calls of which only the LAST is refused: that call's own term *)
Lemma prh_refused_peak_last : forall ok cnt fail k hs,
  (forall i, (i < k)%nat -> nth i ok true = true) ->
  prh_refused_peak ok cnt fail (Datatypes.S k) hs =
  Z.max 0 (if prh_refused ok cnt fail k then Z.min SIZE_MAXZ (nth k hs 0) else 0).
Proof.
  intros ok cnt fail k hs H. unfold prh_refused_peak.
  rewrite List.seq_S, map_app, prh_fold_max_app.
  assert (E0 : fold_right Z.max 0
    (map (fun i => if prh_refused ok cnt fail i then Z.min SIZE_MAXZ (nth i hs 0) else 0) (List.seq 0 k)) = 0).
  { assert (A : forall l, (forall i, In i l -> (i < k)%nat) ->
      fold_right Z.max 0
        (map (fun i => if prh_refused ok cnt fail i then Z.min SIZE_MAXZ (nth i hs 0) else 0) l) = 0).
    { induction l as [|i l IH]; intros HL; [reflexivity|]. cbn [map fold_right].
      rewrite IH by (intros j Hj; apply HL; right; exact Hj).
      unfold prh_refused. rewrite (H i (HL i (or_introl eq_refl))). reflexivity. }
    apply A. intros i Hi. apply List.in_seq in Hi. lia. }
  rewrite E0. cbn [map fold_right]. apply prh_max0.
Qed.

(* THE CHECK (case (a) of the order): on the STRDUP refusal - the last call of prhPj_set_trace, every earlier call
   of the arm granted - the arm's term is EXACTLY refused()'s expression, Z.min SIZE_MAXZ (g_live + klen + 1) at the
   g_live AFTER the granted grows: Lv is the entry's Ledger.lsum Lam and the bracket is the grows' net bytes
   (56 * cap2 - 56 * cap and 8 * cap2 - 8 * cap, nothing when n < cap), so Lv + bracket IS Ledger.lsum Lam2. With
   Ledger.lsum Lam' + Ledger.lsum Dw = Ledger.lsum Lam2 on this arm (its own Dold / Dnew / Dr permutations) and
   peak2 = Z.max peak (Ledger.lsum Lam2) (own ()'s g_peak after each grant), the arm's
   `Z.max (Z.max peak (lsum Lam' + lsum Dw)) (prh_refused_peak ..)` IS
   `Z.max peak2 (Z.min SIZE_MAXZ (Ledger.lsum Lam2 + Z.of_nat (length kname) + 1))`. NOT the discarded form
   `Z.max peak (lsum Lam' + lsum Dw)` alone, which asserts a peak the machine need not have (the arm's own
   counterexample: n < cap, kname = [97], c = 1, ok = [false], cnt <> fail, peak = lsum Lam - g_peak is
   lsum Lam + 2 while Lam' ++ Dw holds exactly lsum Lam). *)
Lemma prhPj_set_refused_peak_strdup : forall ok cnt fail n cap (kname : list Z) (Lv : Z) (k : nat),
  0 <= cap -> 0 <= Lv ->
  length (prhPj_set_trace n cap kname) = Datatypes.S k ->
  (forall i, (i < k)%nat -> nth i ok true = true) ->
  prh_refused ok cnt fail k = true ->
  prh_refused_peak ok cnt fail (Datatypes.S k)
    (map (Z.add Lv) (prh_ev_helds (prhPj_set_trace n cap kname))) =
  Z.min SIZE_MAXZ
    ((Lv + (if n =? cap then 56 * cap2R cap - 56 * cap + (8 * cap2R cap - 8 * cap) else 0))
     + (Z.of_nat (length kname) + 1)).
Proof.
  intros ok cnt fail n cap kname Lv k Hc HL Hlen Hg Hr.
  assert (Hc2 : cap <= cap2R cap) by (unfold cap2R; destruct (cap =? 0) eqn:E;
    [apply Z.eqb_eq in E; lia | apply Z.eqb_neq in E; lia]).
  rewrite (prh_refused_peak_last ok cnt fail k _ Hg), Hr.
  unfold prhPj_set_trace in Hlen |- *. destruct (n =? cap) eqn:En; cbn [app length] in Hlen.
  - assert (Ek : k = 2%nat) by lia. subst k.
    cbn [prh_ev_helds PjGrammar.is_call PjGrammar.held_ev app map nth].
    rewrite !Z2Nat.id by lia.
    rewrite (Z.max_r 0); [f_equal; lia | apply Z.min_glb; [unfold SIZE_MAXZ; lia | lia]].
  - assert (Ek : k = 0%nat) by lia. subst k.
    cbn [prh_ev_helds PjGrammar.is_call PjGrammar.held_ev app map nth].
    rewrite !Z2Nat.id by lia.
    rewrite (Z.max_r 0); [f_equal; lia | apply Z.min_glb; [unfold SIZE_MAXZ; lia | lia]].
Qed.

(* pj_set (:373-392; plain pj_set_c.v:32-108), dd: the nesting the pj_free calls may still make (the replaced value and,
   on failure, val have depth <= dd). old = pj_get (obj, key): present -> pj_free (old), *old = *val, memset (val), 0.
   Absent -> grow (obj) (when n = cap: realloc kids, then keys, to cap2) and keys[n] = strdup (key); either refused ->
   pj_free (val), -1; else kids[n++] = *val, memset (val), 0. The c allocator calls it makes have outcomes ok (prh_oks).
   FP: both headers and every block of the two trees (written, realloc'd or freed). Room: the sum of the callees'
   charges over both arms - pj_free (old), whose blocks are among D; grow's own charge for an object
   (PRH_Charge.v prhPv_rk (prhPg_gtrace true n cap): the grammar's PjGrammar.grow, none when n < cap), the key's
   strdup, and pj_free (val). obj is handed
   to grow (prhReader_at, LIVE_grow); val to pj_free, so it is below alloc_ceiling.
   FAMILY: ROUND-TRIP (the rewrite), ENTRY-keyed list (the header): the rp_* binders, the position and the run
   premise at entry; it may call both families (grow, fuzz_strdup and pj_free are post-form). *)
Definition tpj_set_specX (CTX0 : list (list Z)) (dd : nat) : Prop :=
  forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk) most own,
  forall ly S Hp W regs mem md ch d o k w ms tv D Dw num str kids keys n cap (kname : list Z) Lam peak cnt fail ran,
  fpre B ARx (STK_pj_set dd) ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 ->
  room_live_cf S -> PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* THE RUN HAS AT MOST 4 CALLS: A17's prefix bound needs it where this text pays a post-form
     callee's hull budget from its position (lib/A/PresetHullPay.v hull_budget_of_room_pos) *)
  (length rp_os <= 4)%nat ->
  (* THE RUN'S STRTOD MODEL IS KEYED (the unit owner's ruling HP_sm, one of six: tcheck_reject_clean_starved,
     tround_trip_text, tcheck_round_trip, tpj_set, tpj_string, tpj_write): the events of these six are spelled over
     the reader, so their CONTENT fixes the run's strtod model, and each writes ReaderRes.jr_strtod where rp_sm stood -
     no rp_sm binder, no `rp_sm = ReaderRes.jr_strtod` premise. A text carries exactly the constraints its content
     needs, no more and no fewer: the eight writer / tx texts (tput, tindent, tput_string, twrite_value, ttx_put,
     ttx_string, ttx_line, ttx_value) keep rp_sm free. *)
  (* THE CALL'S ALLOCATIONS ARE CONSUMER ALLOCATIONS OF THE RUN (the kit owner's ruling 2026-10-29, the NAMED
     entry premise of the ENTRY-KEYED texts, here as in the three check texts). With the entry position and the run
     premise, P8 (PresetCfnA.preset_no_refusal; a NULL of malloc_cf is primary-only, YG0dcf.malloc_cf_null_post) and
     the engine's granted paths (PRH_Base.prh_rpost_granted over amreal, YG0d.v:73-92) exclude a REAL refusal at
     every allocation of the call (grow's kids and keys reallocs: grow's refused-arm exclusions, PRH_FnReader; the
     key's strdup: fuzz_strdup's outcome clause, PRH_FnAlloc), so the post states the refusal arm DEAD
     (DEAD-PJSET). Supplied by the caller (check_round_trip's rewrite) from its own prh_cons_from
     (PRH_Base.prh_cons_from_app_iff splits its window). *)
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i (length (prhPj_set_evs ms kname n cap)) ->
  getr regs 10 = w64 o -> getr regs 11 = w64 k -> getr regs 12 = w64 w ->
  fwin ly W regs mem d ->
  pj_nodeR segs (rdW W mem) (prh_lin Lam) o (PjTree.JObj ms) D ->
  pj_hdrR segs (rdW W mem) o 6 num str kids keys n cap -> cap <= 2 ^ 54 ->
  prhPj_slot (STK_pj_set dd) d ly S Lam W regs mem o ->
  pj_nodeR segs (rdW W mem) (prh_lin Lam) w tv Dw ->
  prhPj_slot (STK_pj_set dd) d ly S Lam W regs mem w -> w < YM05.alloc_ceiling ->
  (forall bk, In bk Dw -> ~ In bk D) ->
  (forall x, w <= x < w + 56 -> ~ pj_footR o D x) ->
  pj_apartR Dw o ->
  (PjTree.depth (PjTree.JObj ms) <= Datatypes.S dd)%nat -> (PjTree.depth tv <= dd)%nat ->
  cstr_ok W mem k kname -> kept_at B Lam k (Z.of_nat (length kname) + 1) ->
  (forall x, k <= x < k + Z.of_nat (length kname) + 1 -> ~ pj_footR o D x /\ ~ pj_footR w Dw x) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  cnt + 3 < 2 ^ 64 - 1 ->
  Z.of_nat (length kname) + 1 + cf_head < cf_malloc_max ->
  (* the largest single request of grow's step is the kids realloc (the items-element walk's form; LIVE_grow is a two-block total) *)
  (n = cap -> 56 * cap2R cap + cf_head < cf_malloc_max) ->
  blocks_bytes S + LIVE_pj_set n cap (Z.of_nat (length kname)) <= LIVE_MAX ->
  (* THE OBJECT'S BLOCKS CARRY THE WRITER'S SIZES, UP TO PERMUTATION (the kit owner's final ruling ~20:0xZ: the model
     ties the live set to the run only up to permutation, and the reader's allocation order differs from tblk's
     pre-order, so no ordered block fact is available at any instance). True of the copy check_round_trip's rewrite hands
     pj_set, a tree read back from
     pj_write's text (the P8 owner's PresetFreeFo.rd_blocks_wdoc + fo_tblk, under pj_wf sm t), and of nothing else -
     a tree parsed from arbitrary input has the input's string sizes. This conjunct is a BLOCK fact (a size
     multiset); it supplies the result's block conjuncts below, never a free ORDER - the ordered premise is the next
     one, keyed on fo, not on tblk. *)
  Permutation (map (fun b => snd b + cf_head) D) (PresetReqAtNoMiss.tblk (PjTree.JObj ms)) ->
  (* THE OBJECT'S OWN FREE ORDER (the kit owner's order 2026-10-29, the re-route of the tblk citation that
     stood here): pj_free's order list F of the copy carries the model's fo (JObj ms), IN ORDER. THE CALLER HAS IT:
     the copy is the read-back of pj_write's text, PRH_FnCheck.tround_trip_text_specX's copy arm states that
     reading's reader-side ordered list (map (snd + cf_head) F = PresetReqAt.pj_frees sm [] (wdoc t p)) and
     the P8 owner's PresetFreeFo.pj_frees_wdoc_t turns it into fo t under pj_wf sm t, an EQUALITY of lists. A
     permutation would not do: the position reads the free history in order (prhPj_free_evs_supply's note). This is
    the TOP-LEVEL half of the present-key arm's pj_free supply (the SUBTREE half is the P8 owner's proved
    pj_foR_member, cited on that arm),
     and it is also what both SUCCESS arms carry forward as the RESULT's own ordered list (FREEORD-COPY). *)
  (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth (PjTree.JObj ms) <= nn)%nat ->
     exists F, pj_foR segs (rdW W mem) (prh_lin Lam) nn o D F /\
       map (fun b => snd b + cf_head) F = PresetReqAt.fo (PjTree.JObj ms)) ->
  (* CFHEAD-16 (the kit owner's order, on the image-B pj walker's two-way controls): the head is the model's, 16 = 16 at
     CfParams_preset. The tblk equality above forces it only when D is nonempty (at ms = [] and cap = 0 it reads
     [] = [] for any cf_head), and the model's events (prhPj_set_evs, set_evs) carry PresetReqAt.HEAD while the callee
     texts carry cf_head, so the present-key arm's HBulk and the absent arm's requests meet only under it. Checked
     for the same hole: tpj_string_specX (its list is in cf_head terms, the supply takes cf_head = HEAD itself) and
     tpj_free_specX (keyed on F in cf_head terms) need no such premise. *)
  cf_head = PresetReqAt.HEAD ->
  (* ITS RUN EVENTS, as an entry premise: the model's own list at this call (PresetReqAt.set_evs's tail) - the key
     present, pj_free of the value it replaces, one bulk free of that value's blocks; absent, grow's reallocs
     (none when n < cap) and the key's strdup. Supplied by prhPj_set_evs_supply, which carries F6 (the model's
     capacity is a parsed object's ncap |ms|, the text's is the header's cap). *)
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (prhPj_set_evs ms kname n cap) ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.10): fpostWm is SHARED, so the post is its R
     form at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_pj_set) regs mem md)
    (fpostWmR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) (STK_pj_set dd) d
       ((o, o + 56) :: (w, w + 56) :: ablocks_fp (prhPj_hbl (D ++ Dw)))
       regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\
       exists Lam' peak' fail' ran' res (c : nat) (ok : list bool) Lr Do,
       getr regs' 10 = w64 res /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' (cnt + Z.of_nat c) fail' ran' most own /\
       prh_oks ok cnt fail c (prh_ev_reqs (prhPj_set_trace n cap kname)) most ran ran' /\
       ReaderRes.fail_after cnt fail c fail' /\
       Permutation Lam (D ++ Dw ++ Lr) /\ Permutation Lam' (Do ++ Lr) /\
       prhPj_blocks ly S Lam ly' S' Lam' /\
       pj_zeroR segs (rdW W' mem') w /\
       (* THE EXACT ADVANCE (the position sweep), on the arms that returned 0: the key present, the one bulk free
          of the replaced value (the model's HBulk (fo u); when that value holds no block the instance makes no
          allocator call and the step is prhPj_bulk_nil_pos's); absent and every allocation taken, grow's events
          and the strdup's. res = -1 is the arm where an allocation returned NULL - the chosen failure (excluded
          by its caller, whose g_fail_at is SIZE_MAX) or a refusal (excluded globally by the driver): the
          instance then also frees val's tree, which the all-granted model still holds, so no position of the
          model's run describes S' and that arm states none. *)
       (res = 0 -> exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os
          (rp_i + length (prhPj_set_evs ms kname n cap))%nat rp_H0 hist' S') /\
       ((fail < cnt \/ cnt + Z.of_nat (length (prhPj_set_trace n cap kname)) <= fail) ->
          prh_granted ok cnt fail c -> res = 0) /\
       (* DEAD-PJSET (the refusal arm DEAD under prh_cons_from, above; three supports: PRH_Base's ENTRY-KEYED
          note): res = -1 follows the chosen failure or a
          REAL refusal; prh_cons_from excludes the refusal at every allocation of the call, and with no chosen failure
          in the call's window (the leaves' pick condition, PRH_FnAlloc.tfuzz_malloc_specX's outcome clause) the
          call returns 0. The chosen failure is NOT a refusal and prh_cons_from does not exclude it: inside the window
          res = -1 stays reachable, so the conjunct is stated under the window condition and claims no more. *)
       ((fail < cnt \/ cnt + Z.of_nat (length (prhPj_set_trace n cap kname)) <= fail) -> res = 0) /\
       ( (* the key is present: the value replaced in place, its blocks freed, val's moved in *)
         (In kname (map fst ms) /\ c = 0%nat /\ res = 0 /\ peak' = peak /\
          (exists i vi Di Dr, nth_error ms i = Some (kname, vi) /\
             (forall j nm u, (j < i)%nat -> nth_error ms j = Some (nm, u) -> nm <> kname) /\
             pj_nodeR segs (rdW W mem) (prh_lin Lam) (kids + 56 * Z.of_nat i) vi Di /\
             Permutation D (Di ++ Dr) /\ Permutation Do (Dr ++ Dw)) /\
          pj_nodeR segs (rdW W' mem') (prh_lin Lam') o (PjTree.JObj (PjTree.pj_set_model ms kname tv)) Do /\
          (* THE REPLACED VALUE'S FREE (the kit owner's order 2026-10-29).
             The model's event on this arm is HBulk (PresetReqAt.fo vi) (PresetReqAt.set_evs's Some branch), so the
             walk's pj_free (old) needs the ORDERED tie of the REPLACED SUBTREE's order list Fv:
             map (fun b => snd b + cf_head) Fv = PresetReqAt.fo vi, with pj_foR .. (kids + 56 * i) Di Fv. The
             entry premise above gives the ORDERED list of the WHOLE object (fo (JObj ms)), and fo is
             COMPOSITIONAL - PresetFreeFo.fo_obj: fo (JObj ms) = concat (map fom ms) ++ arrz true (capf 0 0 |ms|),
             with fom m = fo (snd m) ++ [kblk (fst m)]. THE SPLIT OF pj_foR's F AT A MEMBER IS PROVED: the P8 owner's
             pj_foR_member (lib/A/PjFoMember.v:367, taken by path at blob 0d5cd17bf504 from
             commit 3bca528aa963; the proof commit is 9e51d07e4e62, and 3bca528aa963 is an
             empty commit whose message records both VERIFY checks), in the lemma's own binder list:
               forall m lblk o ms D F nn i kname vi Di kids,
                 pj_nodeR segs m lblk o (PjTree.JObj ms) D ->
                 pj_foR segs m lblk (S nn) o D F ->
                 map (fun b => snd b + PresetReqAt.HEAD) F = PresetReqAt.fo (PjTree.JObj ms) ->
                 nth_error ms i = Some (kname, vi) ->
                 pj_nodeR segs m lblk (kids + 56 * Z.of_nat i) vi Di ->
                 rd_u64 segs m (o + 24) kids ->
                 (forall a k k', lblk a k -> lblk a k' -> k = k') ->
                 (forall a k, lblk a k -> a <> 0) ->
                 exists Fv, pj_foR segs m lblk nn (kids + 56 * Z.of_nat i) Di Fv /\
                   map (fun b => snd b + PresetReqAt.HEAD) Fv = PresetReqAt.fo vi.
             THE SUPPLIERS of its last three premises, all closed: kids = pj_hdrR's 5th conjunct (PRH_Reader.v:108, at
             the entry premise pj_hdrR .. o 6 num str kids keys n cap); lblk FUNCTIONAL = PRH_Base.prh_lin_functional
             (lblk := prh_lin Lam, from prh_ledger's NoDup (map fst Lam)); no block at address 0 =
             PRH_Base.prh_ledger_nonzero (outcome (b): AR_laws_x's field alx_blocks, YCbqG.ARx_blocks_law, gives
             `4096 <= p` for every block of ablocks, and prh_hblock's `In (a - cf_head, ..) (ablocks B ly S)` then
             gives a >= 4096 + cf_head > 0).
             The P8 owner's reviewer's CALL-SITE CHECK: the lemma FITS this present-key arm because of the ORDERED
             entry premise `map (fun b => snd b + cf_head) F = PresetReqAt.fo (PjTree.JObj ms)` above (the free-permutation walk's
             2878b4c53320); at walkkit-next de5e947c224b, which had only the tblk Permutation (its :775), it does NOT
             apply. Satisfiability: no jointly unsatisfiable case, because a non-empty object forces kids >= 4096 +
             cf_head.
             Its route: pj_foR's object arm is pf_oitemsR slot by slot (value's Fv, then the key block), fo_obj is
             that same shape, and the two line up once each slot's lengths agree - |Fv_j| = |Di_j| (pj_foR_fdR's
             Permutation) and |Di_j| >= |tblk v_j| = |fo v_j| (PRH_PjOrder.pf_node_len, PresetReqAtNoMiss.fo_tblk),
             with the totals equal, so every slot is exact. PresetReqAtNoMiss.fo_tblk holds for ANY tree, subtrees
             included, which is what makes the counting argument go through. NOT WRITTEN AS A PERMUTATION: a
             permuted free list is a different free history and moves no position.
             THE BLOCK LIST of the result, UNDER val's sizes: Do keeps the arrays and every key and other value of
             D, whose sizes the entry's tblk permutation fixes (cap > 0 here, so that equality also forces
             cf_head = HEAD), and takes Dw at the replaced value's place. FALSE WITHOUT the premise on Dw, a FINDING
             reported to the owner (the pj walk, 2026-10-29): tv = JStr [97] with Dw = [(a, 5)] (pj_cstrR allows k >= 2)
             gives 5 + 16 = 21 where tblk (JStr [97]) = [18]. check_round_trip supplies it: val is pj_string's
             node, Dw = [(a, 21)], and MOD_VAL has no special character, so tblk (JStr MOD_VAL) = [37]. It is a
             BLOCK fact (a size multiset) and supplies no free ORDER: the later pj_free (&copy) of the result takes
             its ordered list from the FREEORD-COPY conjunct below, never from this one. *)
          (* UP TO PERMUTATION (the kit owner's final ruling; the ordered form was never available) *)
          (Permutation (map (fun b => snd b + cf_head) Dw) (PresetReqAtNoMiss.tblk tv) ->
             Permutation (map (fun b => snd b + cf_head) Do)
               (PresetReqAtNoMiss.tblk (PjTree.JObj (PjTree.pj_set_model ms kname tv)))) /\
          (* THE RESULT'S OWN FREE ORDER (FREEORD-COPY, the kit owner's ASK 2, 2026-10-29): pj_free's order list
             of the object AFTER the set carries the model's fo of the SAME result term, IN ORDER. A caller that
             frees the result - check_round_trip's pj_free (&copy), whose model event is HBulk (fo (copy_set ms)) -
             cannot place its free history from the block Permutation above: iface_room_pos reads PresetRunQ.hfrees_q
             (the model's frees that enter the quarantine) in order, and YGcfFrees' quarantine is the suffix in free
             order, so a multiset says nothing about where a free lands. THE SHAPE is this text's entry premise, at the
             result.
             WHY IT ALSO TAKES val's OWN ORDERED LIST, and the bare form is FALSE (the kit owner's measurement, the
             one that forced CAP; PRH_Reader.v:219-224, vm_compute-checked): a size PERMUTATION identifies no
             block, so `Permutation (map (snd + cf_head) Dw) (tblk tv)` leaves val's blocks free to carry each
             other's sizes - the witness there satisfies pj_nodeR and the permutation with cap = 1 where
             ncap 1 = 8, and fo's arrz is at ncap, so map (snd + cf_head) of its order list is NOT fo. val's
             ordered list is what fixes each block, and this arm's proof is then fo's compositionality
             (PresetFreeFo.fo_obj: fo (JObj ms) = concat (map fom ms) ++ arrz true (capf 0 0 |ms|), fom m =
             fo (snd m) ++ [kblk (fst m)]) slot by slot: |ms| is unchanged here, the arrays are untouched, and the
             only slot that moves is i, from fo vi to fo tv.
             THE CALLER NEEDS NOTHING NEW: check_round_trip's val is pj_string's node, a JStr with ONE block, and
             for a one-block tree the permutation above IS the ordered equation (PRH_PjOrder.pfo_leaf gives the
             order list). *)
          (cf_head = PresetReqAt.HEAD ->
           (forall nv, (PjTree.depth tv <= nv)%nat ->
              exists Fw, pj_foR segs (rdW W mem) (prh_lin Lam) nv w Dw Fw /\
                map (fun b => snd b + cf_head) Fw = PresetReqAt.fo tv) ->
           forall nn, (PjTree.depth (PjTree.JObj (PjTree.pj_set_model ms kname tv)) <= nn)%nat ->
             exists F, pj_foR segs (rdW W' mem') (prh_lin Lam') nn o Do F /\
               map (fun b => snd b + cf_head) F =
                 PresetReqAt.fo (PjTree.JObj (PjTree.pj_set_model ms kname tv))))
         \/
         (* absent, every allocation taken: appended *)
         (~ In kname (map fst ms) /\
          ~ (cnt <= fail < cnt + Z.of_nat (length (prhPj_set_trace n cap kname))) /\
          c = length (prhPj_set_trace n cap kname) /\ (forall i, (i < c)%nat -> nth i ok true = true) /\
          res = 0 /\ peak' = Z.max peak (Ledger.lsum Lam') /\
          (exists Dold Dnew Dr a, Permutation D (Dold ++ Dr) /\
             Permutation Do (Dnew ++ (a, Z.of_nat (length kname) + 1) :: Dr ++ Dw) /\
             (forall a' k', In (a', k') (Dnew ++ [(a, Z.of_nat (length kname) + 1)]) ->
                In (a', k') Dold \/ ~ In (a' - cf_head, k' + cf_head) (ablocks B ly S)) /\
             (n < cap /\ Dold = [] /\ Dnew = [] \/
              n = cap /\ Dold = kids_blkR kids cap ++ keys_blkR 6 keys cap /\
                exists k' y', Dnew = [(k', 56 * cap2R cap); (y', 8 * cap2R cap)])) /\
          pj_nodeR segs (rdW W' mem') (prh_lin Lam') o (PjTree.JObj (PjTree.pj_set_model ms kname tv)) Do /\
          (* THE BLOCK LIST of the result, UNDER three pure facts: the arrays at grow's capacity (the
             model's capf, PresetReqAt.set_evs' grow_ev), D's keys and values in order, then the key's strdup
             block and Dw. FALSE WITHOUT them, a FINDING reported to the owner (the pj walk, 2026-10-29): Dw's sizes as on
             the arm above; kname = [34] gives the strdup block (a, 2), 2 + 16 = 18, where the writer's key block
             kblk [34] = 1 + |ech 34| + 16 = 19; and at ms = [] (cap = 0) the entry's tblk equality is [] = [] and
             does not force cf_head = HEAD. check_round_trip supplies all three (cf_head = 16 at CfParams_preset;
             Dw as above; MOD_KEY has no special character). *)
          (* UP TO PERMUTATION (the kit owner's final ruling; the ordered form was never available) *)
          (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) Dw) (PresetReqAtNoMiss.tblk tv) ->
             length (flat_map PjRoundTrip.ech kname) = length kname ->
             Permutation (map (fun b => snd b + cf_head) Do)
               (PresetReqAtNoMiss.tblk (PjTree.JObj (PjTree.pj_set_model ms kname tv)))) /\
          (* THE RESULT'S OWN FREE ORDER (FREEORD-COPY, the kit owner's ASK 2, 2026-10-29), the appended case.
             Same shape and same reason as the present-key arm's: a caller that frees the result needs the ORDER,
             which the block Permutation above cannot give. It takes val's own ordered list (the CAP witness,
             PRH_Reader.v:219-224, refutes the bare form) and the key's plain-escape fact, which this arm's block
             conjunct already takes - the strdup block is (a, |kname| + 1) while the model's key block is
             kblk kname = |flat_map ech kname| + 1 + HEAD, and the two meet only there.
             WHY THE ARRAYS MATCH WITHOUT A NEW FACT: fo's capacity for the result is
             PresetReqAt.ncap (|ms| + 1) = PjRoundTrip.gcap |ms| (ncap |ms|), and the entry premise's ordered list
             forces the entry arrays to ncap |ms|; n < cap is the not-full case, where gcap keeps the capacity and
             this arm keeps the arrays (Dold = Dnew = []), and n = cap is the full case, where gcap doubles and
             this arm's Dnew is exactly (56 * cap2R cap, 8 * cap2R cap). The two agree in both, so no model fact
             about the grown arrays is owed. *)
          (cf_head = PresetReqAt.HEAD ->
           (forall nv, (PjTree.depth tv <= nv)%nat ->
              exists Fw, pj_foR segs (rdW W mem) (prh_lin Lam) nv w Dw Fw /\
                map (fun b => snd b + cf_head) Fw = PresetReqAt.fo tv) ->
           length (flat_map PjRoundTrip.ech kname) = length kname ->
           forall nn, (PjTree.depth (PjTree.JObj (PjTree.pj_set_model ms kname tv)) <= nn)%nat ->
             exists F, pj_foR segs (rdW W' mem') (prh_lin Lam') nn o Do F /\
               map (fun b => snd b + cf_head) F =
                 PresetReqAt.fo (PjTree.JObj (PjTree.pj_set_model ms kname tv))))
         \/
         (* absent, the c-th allocation failed (chosen or refused): val freed, the growth so far kept, -1 *)
         (~ In kname (map fst ms) /\
          (1 <= c <= length (prhPj_set_trace n cap kname))%nat /\ nth (c - 1) ok true = false /\
          (forall i, (i < c - 1)%nat -> nth i ok true = true) /\
          res = -1 /\
          (* THE REFUSAL PEAK (#102, PRH_Base.v prh_refused_peak), the live counts read off prhPj_set_trace (the kids
             realloc after disown, the keys realloc after the kids grant, the strdup). COUNTEREXAMPLE to `peak' = Z.max
             peak (Ledger.lsum Lam' + Ledger.lsum Dw)` alone: n < cap, kname = [97], c = 1, ok = [false], cnt <> fail,
             peak = Ledger.lsum Lam: the strdup (2) is refused and g_peak = Ledger.lsum Lam + 2, while Lam' ++ Dw holds
             exactly Ledger.lsum Lam.
             THE TERM IS THE CALLEE'S OWN EXPRESSION, CHECKED (the kit owner's check order 2026-10-29, case (a)
             of it): on the STRDUP refusal (c = length (prhPj_set_trace n cap kname), every earlier call of the arm
             granted) prhPj_set_refused_peak_strdup above EVALUATES this term to
             `Z.min SIZE_MAXZ (Ledger.lsum Lam2 + Z.of_nat (length kname) + 1)` with Lam2 the ledger after the
             granted grows (Ledger.lsum Lam + the grows' net bytes, nothing when n < cap), which is fuzz_strdup's
             refused() expression VERBATIM; and the arm's first term is Z.max peak (Ledger.lsum Lam2) = peak2,
             because Ledger.lsum Lam' + Ledger.lsum Dw = Ledger.lsum Lam2 by this arm's own Dold / Dnew / Dr
             permutations. So the whole is `Z.max peak2 (Z.min SIZE_MAXZ (Ledger.lsum Lam2 + |kname| + 1))` and the
             kit keeps ONE definition, PRH_Base.prh_refused_peak; no second peak form is stated. THE RULE: at a
             refusal the `ran` half (prh_oks's g_ran_out clause, correct at the tip and untouched) and the `peak`
             half are SEPARATE obligations, both keyed on the CALLEE. *)
          peak' = Z.max (Z.max peak (Ledger.lsum Lam' + Ledger.lsum Dw))
            (prh_refused_peak ok cnt fail c
               (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds (prhPj_set_trace n cap kname)))) /\
          (exists Dold Dnew Dr, Permutation D (Dold ++ Dr) /\ Permutation Do (Dnew ++ Dr) /\
             prhPj_new ly S Dnew /\
             (c = 1%nat /\ Dold = [] /\ Dnew = [] \/
              n = cap /\ c = 2%nat /\ Dold = kids_blkR kids cap /\
                (exists k', Dnew = [(k', 56 * cap2R cap)]) \/
              n = cap /\ c = 3%nat /\ Dold = kids_blkR kids cap ++ keys_blkR 6 keys cap /\
                exists k' y', Dnew = [(k', 56 * cap2R cap); (y', 8 * cap2R cap)])) /\
          (* AT THE TREE'S OWN DEPTH (the kit owner's goal from Crt102Rewrite, 2026-10-29): a refused pj_set has not
             grown the tree - ms is unchanged and only the kids / keys arrays may have moved - so its freeable shape
             has depth (JObj ms), the same discipline as the success arms' pj_nodeR (pj_nodeR -> pj_fdR (depth t)).
             It was `pj_freeableR`, an existential over the depth, which a consumer that needs pj_fdR at a fixed
             depth (check_round_trip's crt_at_J at DOC_D) cannot specialise. The other arms are unchanged. *)
          pj_fdR segs (rdW W' mem') (prh_lin Lam') (PjTree.depth (PjTree.JObj ms)) o Do /\
          (c = length (prhPj_set_trace n cap kname) ->
             pj_nodeR segs (rdW W' mem') (prh_lin Lam') o (PjTree.JObj ms) Do)) ))).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tpj_set_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. tpsP_Q IS the text's post (tpsP_Q_check fails to build if
   the two ever differ); tpsP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition tpsP_A1 (W : world segs) (mem : word -> option byte) (o w : Z) (ms : list (list Z * PjTree.jv)) (tv :
    PjTree.jv) (D Dw : list (Z * Z)) (kids : Z) (kname : list Z) (Lam : list (Z * Z)) (peak : Z) (W' : world segs)
    (mem' : word -> option byte) (Lam' : list (Z * Z)) (peak' res : Z) (c : nat) (Do : list (Z * Z)) : Prop :=
  In kname (map fst ms) /\ c = 0%nat /\ res = 0 /\ peak' = peak /\ (exists i vi Di Dr, nth_error ms i = Some (kname,
      vi) /\ (forall j nm u, (j < i)%nat -> nth_error ms j = Some (nm, u) -> nm <> kname) /\ pj_nodeR segs (rdW W mem)
      (prh_lin Lam) (kids + 56 * Z.of_nat i) vi Di /\ Permutation D (Di ++ Dr) /\ Permutation Do (Dr ++ Dw)) /\
      pj_nodeR segs (rdW W' mem') (prh_lin Lam') o (PjTree.JObj (PjTree.pj_set_model ms kname tv)) Do /\ (Permutation
      (map (fun b => snd b + cf_head) Dw) (PresetReqAtNoMiss.tblk tv) -> Permutation (map (fun b => snd b + cf_head)
      Do) (PresetReqAtNoMiss.tblk (PjTree.JObj (PjTree.pj_set_model ms kname tv)))) /\ (cf_head = PresetReqAt.HEAD ->
      (forall nv, (PjTree.depth tv <= nv)%nat -> exists Fw, pj_foR segs (rdW W mem) (prh_lin Lam) nv w Dw Fw /\ map
      (fun b => snd b + cf_head) Fw = PresetReqAt.fo tv) -> forall nn, (PjTree.depth (PjTree.JObj (PjTree.pj_set_model
      ms kname tv)) <= nn)%nat -> exists F, pj_foR segs (rdW W' mem') (prh_lin Lam') nn o Do F /\ map (fun b => snd b +
      cf_head) F = PresetReqAt.fo (PjTree.JObj (PjTree.pj_set_model ms kname tv))).

Definition tpsP_A2 (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (o w : Z) (ms : list (list
    Z * PjTree.jv)) (tv : PjTree.jv) (D Dw : list (Z * Z)) (kids keys n cap : Z) (kname : list Z) (Lam : list (Z * Z))
    (peak cnt fail : Z) (W' : world segs) (mem' : word -> option byte) (Lam' : list (Z * Z)) (peak' res : Z) (c : nat)
    (ok : list bool) (Do : list (Z * Z)) : Prop :=
  ~ In kname (map fst ms) /\ ~ (cnt <= fail < cnt + Z.of_nat (length (prhPj_set_trace n cap kname))) /\ c = length
      (prhPj_set_trace n cap kname) /\ (forall i, (i < c)%nat -> nth i ok true = true) /\ res = 0 /\ peak' = Z.max peak
      (Ledger.lsum Lam') /\ (exists Dold Dnew Dr a, Permutation D (Dold ++ Dr) /\ Permutation Do (Dnew ++ (a, Z.of_nat
      (length kname) + 1) :: Dr ++ Dw) /\ (forall a' k', In (a', k') (Dnew ++ [(a, Z.of_nat (length kname) + 1)]) -> In
      (a', k') Dold \/ ~ In (a' - cf_head, k' + cf_head) (ablocks B ly S)) /\ (n < cap /\ Dold = [] /\ Dnew = [] \/ n =
      cap /\ Dold = kids_blkR kids cap ++ keys_blkR 6 keys cap /\ exists k' y', Dnew = [(k', 56 * cap2R cap); (y', 8 *
      cap2R cap)])) /\ pj_nodeR segs (rdW W' mem') (prh_lin Lam') o (PjTree.JObj (PjTree.pj_set_model ms kname tv)) Do
      /\ (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) Dw) (PresetReqAtNoMiss.tblk tv) ->
      length (flat_map PjRoundTrip.ech kname) = length kname -> Permutation (map (fun b => snd b + cf_head) Do)
      (PresetReqAtNoMiss.tblk (PjTree.JObj (PjTree.pj_set_model ms kname tv)))) /\ (cf_head = PresetReqAt.HEAD ->
      (forall nv, (PjTree.depth tv <= nv)%nat -> exists Fw, pj_foR segs (rdW W mem) (prh_lin Lam) nv w Dw Fw /\ map
      (fun b => snd b + cf_head) Fw = PresetReqAt.fo tv) -> length (flat_map PjRoundTrip.ech kname) = length kname ->
      forall nn, (PjTree.depth (PjTree.JObj (PjTree.pj_set_model ms kname tv)) <= nn)%nat -> exists F, pj_foR segs (rdW
      W' mem') (prh_lin Lam') nn o Do F /\ map (fun b => snd b + cf_head) F = PresetReqAt.fo (PjTree.JObj
      (PjTree.pj_set_model ms kname tv))).

Definition tpsP_A3 (ly : alayout) (S : astate) (o : Z) (ms : list (list Z * PjTree.jv)) (D Dw : list (Z * Z)) (kids
    keys n cap : Z) (kname : list Z) (Lam : list (Z * Z)) (peak cnt fail : Z) (W' : world segs) (mem' : word -> option
    byte) (Lam' : list (Z * Z)) (peak' res : Z) (c : nat) (ok : list bool) (Do : list (Z * Z)) : Prop :=
  ~ In kname (map fst ms) /\ (1 <= c <= length (prhPj_set_trace n cap kname))%nat /\ nth (c - 1) ok true = false /\
      (forall i, (i < c - 1)%nat -> nth i ok true = true) /\ res = -1 /\ peak' = Z.max (Z.max peak (Ledger.lsum Lam' +
      Ledger.lsum Dw)) (prh_refused_peak ok cnt fail c (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds (prhPj_set_trace n
      cap kname)))) /\ (exists Dold Dnew Dr, Permutation D (Dold ++ Dr) /\ Permutation Do (Dnew ++ Dr) /\ prhPj_new ly
      S Dnew /\ (c = 1%nat /\ Dold = [] /\ Dnew = [] \/ n = cap /\ c = 2%nat /\ Dold = kids_blkR kids cap /\ (exists
      k', Dnew = [(k', 56 * cap2R cap)]) \/ n = cap /\ c = 3%nat /\ Dold = kids_blkR kids cap ++ keys_blkR 6 keys cap
      /\ exists k' y', Dnew = [(k', 56 * cap2R cap); (y', 8 * cap2R cap)])) /\ pj_fdR segs (rdW W' mem') (prh_lin Lam')
      (PjTree.depth (PjTree.JObj ms)) o Do /\ (c = length (prhPj_set_trace n cap kname) -> pj_nodeR segs (rdW W' mem')
      (prh_lin Lam') o (PjTree.JObj ms) Do).

Definition tpsP_Q (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z)
    (most own : Z) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (o w : Z) (ms : list (list
    Z * PjTree.jv)) (tv : PjTree.jv) (D Dw : list (Z * Z)) (kids keys n cap : Z) (kname : list Z) (Lam : list (Z * Z))
    (peak cnt fail ran : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  room_live_cf S' /\ exists Lam' peak' fail' ran' res (c : nat) (ok : list bool) Lr Do, getr regs' 10 = w64 res /\
      prh_ledger B ly' S' Hp' W' mem' Lam' peak' (cnt + Z.of_nat c) fail' ran' most own /\ prh_oks ok cnt fail c
      (prh_ev_reqs (prhPj_set_trace n cap kname)) most ran ran' /\ ReaderRes.fail_after cnt fail c fail' /\ Permutation
      Lam (D ++ Dw ++ Lr) /\ Permutation Lam' (Do ++ Lr) /\ prhPj_blocks ly S Lam ly' S' Lam' /\ pj_zeroR segs (rdW W'
      mem') w /\ (res = 0 -> exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os (rp_i + length
      (prhPj_set_evs ms kname n cap))%nat rp_H0 hist' S') /\ ((fail < cnt \/ cnt + Z.of_nat (length (prhPj_set_trace n
      cap kname)) <= fail) -> prh_granted ok cnt fail c -> res = 0) /\ ((fail < cnt \/ cnt + Z.of_nat (length
      (prhPj_set_trace n cap kname)) <= fail) -> res = 0) /\ (tpsP_A1 W mem o w ms tv D Dw kids kname Lam peak W' mem'
      Lam' peak' res c Do \/ tpsP_A2 ly S W mem o w ms tv D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam'
      peak' res c ok Do \/ tpsP_A3 ly S o ms D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok
      Do).

Lemma tpsP_Q_check : forall (CTX0 : list (list Z)) (dd : nat), tpj_set_specX CTX0 dd -> tpj_set_specX CTX0 dd.
Proof.
  intros CTX0 dd H. unfold tpj_set_specX in *.
  intros rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch d o k w ms tv D Dw num str kids keys n cap
      kname Lam peak cnt fail ran HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18
      HP19 HP20 HP21 HP22 HP23 HP24 HP25 HP26 HP27 HP28 HP29 HP30 HP31 HP32 HP33.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (tpsP_Q rp_x rp_os rp_i rp_H0 most
      own ly S W mem o w ms tv D Dw kids keys n cap kname Lam peak cnt fail ran) end.
  exact (H rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch d o k w ms tv D Dw num str kids keys n cap
      kname Lam peak cnt fail ran HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18
      HP19 HP20 HP21 HP22 HP23 HP24 HP25 HP26 HP27 HP28 HP29 HP30 HP31 HP32 HP33).
Qed.

Record tpsP_R (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z) (most
    own : Z) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (o w : Z) (ms : list (list Z *
    PjTree.jv)) (tv : PjTree.jv) (D Dw : list (Z * Z)) (kids keys n cap : Z) (kname : list Z) (Lam : list (Z * Z))
    (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem'
    : word -> option byte) (Lam' : list (Z * Z)) (peak' fail' ran' res : Z) (c : nat) (ok : list bool) (Lr Do : list (Z
    * Z)) : Prop := {
  tpsP_room : room_live_cf S';
  tpsP_ret : getr regs' 10 = w64 res;
  tpsP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' peak' (cnt + Z.of_nat c) fail' ran' most own;
  tpsP_oks : prh_oks ok cnt fail c (prh_ev_reqs (prhPj_set_trace n cap kname)) most ran ran';
  tpsP_fail : ReaderRes.fail_after cnt fail c fail';
  tpsP_lam : Permutation Lam (D ++ Dw ++ Lr);
  tpsP_lam_out : Permutation Lam' (Do ++ Lr);
  tpsP_blocks : prhPj_blocks ly S Lam ly' S' Lam';
  tpsP_zero : pj_zeroR segs (rdW W' mem') w;
  tpsP_pos : (res = 0 -> exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os (rp_i + length
      (prhPj_set_evs ms kname n cap))%nat rp_H0 hist' S');
  tpsP_granted : ((fail < cnt \/ cnt + Z.of_nat (length (prhPj_set_trace n cap kname)) <= fail) -> prh_granted ok cnt
      fail c -> res = 0);
  tpsP_outside : ((fail < cnt \/ cnt + Z.of_nat (length (prhPj_set_trace n cap kname)) <= fail) -> res = 0);
  tpsP_arm : (tpsP_A1 W mem o w ms tv D Dw kids kname Lam peak W' mem' Lam' peak' res c Do \/ tpsP_A2 ly S W mem o w ms
      tv D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok Do \/ tpsP_A3 ly S o ms D Dw kids
      keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok Do) }.

Lemma tpsP_R_of : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 :
    list Z) (most own : Z) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (o w : Z) (ms :
    list (list Z * PjTree.jv)) (tv : PjTree.jv) (D Dw : list (Z * Z)) (kids keys n cap : Z) (kname : list Z) (Lam :
    list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap
    5 word) (mem' : word -> option byte) (md' : Model),
  tpsP_Q rp_x rp_os rp_i rp_H0 most own ly S W mem o w ms tv D Dw kids keys n cap kname Lam peak cnt fail ran ly' S'
      Hp' W' regs' mem' md' ->
  exists Lam' peak' fail' ran' res c ok Lr Do, tpsP_R rp_x rp_os rp_i rp_H0 most own ly S W mem o w ms tv D Dw kids
      keys n cap kname Lam peak cnt fail ran ly' S' Hp' W' regs' mem' Lam' peak' fail' ran' res c ok Lr Do.
Proof.
  intros rp_x rp_os rp_i rp_H0 most own ly S W mem o w ms tv D Dw kids keys n cap kname Lam peak cnt fail ran ly' S'
      Hp' W' regs' mem' md' H. destruct H as (H0 & Lam' & peak' & fail' & ran' & res & c & ok & Lr & Do & H1 & H2 & H3
      & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  exists Lam', peak', fail', ran', res, c, ok, Lr, Do.
  exact {| tpsP_room := H0; tpsP_ret := H1; tpsP_ledger := H2; tpsP_oks := H3; tpsP_fail := H4; tpsP_lam := H5;
      tpsP_lam_out := H6; tpsP_blocks := H7; tpsP_zero := H8; tpsP_pos := H9; tpsP_granted := H10; tpsP_outside := H11;
      tpsP_arm := H12 |}.
Qed.

Lemma tpsP_Q_of_R : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 :
    list Z) (most own : Z) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (o w : Z) (ms :
    list (list Z * PjTree.jv)) (tv : PjTree.jv) (D Dw : list (Z * Z)) (kids keys n cap : Z) (kname : list Z) (Lam :
    list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap
    5 word) (mem' : word -> option byte) (md' : Model) (Lam' : list (Z * Z)) (peak' fail' ran' res : Z) (c : nat) (ok :
    list bool) (Lr Do : list (Z * Z)),
  tpsP_R rp_x rp_os rp_i rp_H0 most own ly S W mem o w ms tv D Dw kids keys n cap kname Lam peak cnt fail ran ly' S'
      Hp' W' regs' mem' Lam' peak' fail' ran' res c ok Lr Do ->
  tpsP_Q rp_x rp_os rp_i rp_H0 most own ly S W mem o w ms tv D Dw kids keys n cap kname Lam peak cnt fail ran ly' S'
      Hp' W' regs' mem' md'.
Proof.
  intros rp_x rp_os rp_i rp_H0 most own ly S W mem o w ms tv D Dw kids keys n cap kname Lam peak cnt fail ran ly' S'
      Hp' W' regs' mem' md' Lam' peak' fail' ran' res c ok Lr Do HR.
  refine (conj (tpsP_room HR) _).
  exists Lam', peak', fail', ran', res, c, ok, Lr, Do.
  exact (conj (tpsP_ret HR) (conj (tpsP_ledger HR) (conj (tpsP_oks HR) (conj (tpsP_fail HR) (conj (tpsP_lam HR) (conj
      (tpsP_lam_out HR) (conj (tpsP_blocks HR) (conj (tpsP_zero HR) (conj (tpsP_pos HR) (conj (tpsP_granted HR) (conj
      (tpsP_outside HR) (tpsP_arm HR)))))))))))).
Qed.

Record tpsP_R1 (W : world segs) (mem : word -> option byte) (o w : Z) (ms : list (list Z * PjTree.jv)) (tv : PjTree.jv)
    (D Dw : list (Z * Z)) (kids : Z) (kname : list Z) (Lam : list (Z * Z)) (peak : Z) (W' : world segs) (mem' : word ->
    option byte) (Lam' : list (Z * Z)) (peak' res : Z) (c : nat) (Do : list (Z * Z)) : Prop := {
  tpsP1_present : In kname (map fst ms);
  tpsP1_c : c = 0%nat;
  tpsP1_res0 : res = 0;
  tpsP1_peak : peak' = peak;
  tpsP1_slot : (exists i vi Di Dr, nth_error ms i = Some (kname, vi) /\ (forall j nm u, (j < i)%nat -> nth_error ms j =
      Some (nm, u) -> nm <> kname) /\ pj_nodeR segs (rdW W mem) (prh_lin Lam) (kids + 56 * Z.of_nat i) vi Di /\
      Permutation D (Di ++ Dr) /\ Permutation Do (Dr ++ Dw));
  tpsP1_node : pj_nodeR segs (rdW W' mem') (prh_lin Lam') o (PjTree.JObj (PjTree.pj_set_model ms kname tv)) Do;
  tpsP1_tblk : (Permutation (map (fun b => snd b + cf_head) Dw) (PresetReqAtNoMiss.tblk tv) -> Permutation (map (fun b
      => snd b + cf_head) Do) (PresetReqAtNoMiss.tblk (PjTree.JObj (PjTree.pj_set_model ms kname tv))));
  tpsP1_freeord : (cf_head = PresetReqAt.HEAD -> (forall nv, (PjTree.depth tv <= nv)%nat -> exists Fw, pj_foR segs (rdW
      W mem) (prh_lin Lam) nv w Dw Fw /\ map (fun b => snd b + cf_head) Fw = PresetReqAt.fo tv) -> forall nn,
      (PjTree.depth (PjTree.JObj (PjTree.pj_set_model ms kname tv)) <= nn)%nat -> exists F, pj_foR segs (rdW W' mem')
      (prh_lin Lam') nn o Do F /\ map (fun b => snd b + cf_head) F = PresetReqAt.fo (PjTree.JObj (PjTree.pj_set_model
      ms kname tv))) }.

Lemma tpsP_R1_of : forall (W : world segs) (mem : word -> option byte) (o w : Z) (ms : list (list Z * PjTree.jv)) (tv :
    PjTree.jv) (D Dw : list (Z * Z)) (kids : Z) (kname : list Z) (Lam : list (Z * Z)) (peak : Z) (W' : world segs)
    (mem' : word -> option byte) (Lam' : list (Z * Z)) (peak' res : Z) (c : nat) (Do : list (Z * Z)),
  tpsP_A1 W mem o w ms tv D Dw kids kname Lam peak W' mem' Lam' peak' res c Do ->
  tpsP_R1 W mem o w ms tv D Dw kids kname Lam peak W' mem' Lam' peak' res c Do.
Proof.
  intros W mem o w ms tv D Dw kids kname Lam peak W' mem' Lam' peak' res c Do H. destruct H as (H0 & H1 & H2 & H3 & H4
      & H5 & H6 & H7).
  exact {| tpsP1_present := H0; tpsP1_c := H1; tpsP1_res0 := H2; tpsP1_peak := H3; tpsP1_slot := H4; tpsP1_node := H5;
      tpsP1_tblk := H6; tpsP1_freeord := H7 |}.
Qed.

Lemma tpsP_A1_of_R : forall (W : world segs) (mem : word -> option byte) (o w : Z) (ms : list (list Z * PjTree.jv)) (tv
    : PjTree.jv) (D Dw : list (Z * Z)) (kids : Z) (kname : list Z) (Lam : list (Z * Z)) (peak : Z) (W' : world segs)
    (mem' : word -> option byte) (Lam' : list (Z * Z)) (peak' res : Z) (c : nat) (Do : list (Z * Z)),
  tpsP_R1 W mem o w ms tv D Dw kids kname Lam peak W' mem' Lam' peak' res c Do ->
  tpsP_A1 W mem o w ms tv D Dw kids kname Lam peak W' mem' Lam' peak' res c Do.
Proof.
  intros W mem o w ms tv D Dw kids kname Lam peak W' mem' Lam' peak' res c Do HR.
  exact (conj (tpsP1_present HR) (conj (tpsP1_c HR) (conj (tpsP1_res0 HR) (conj (tpsP1_peak HR) (conj (tpsP1_slot HR)
      (conj (tpsP1_node HR) (conj (tpsP1_tblk HR) (tpsP1_freeord HR)))))))).
Qed.

Record tpsP_R2 (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (o w : Z) (ms : list (list Z *
    PjTree.jv)) (tv : PjTree.jv) (D Dw : list (Z * Z)) (kids keys n cap : Z) (kname : list Z) (Lam : list (Z * Z))
    (peak cnt fail : Z) (W' : world segs) (mem' : word -> option byte) (Lam' : list (Z * Z)) (peak' res : Z) (c : nat)
    (ok : list bool) (Do : list (Z * Z)) : Prop := {
  tpsP2_absent : ~ In kname (map fst ms);
  tpsP2_window : ~ (cnt <= fail < cnt + Z.of_nat (length (prhPj_set_trace n cap kname)));
  tpsP2_c : c = length (prhPj_set_trace n cap kname);
  tpsP2_oks : (forall i, (i < c)%nat -> nth i ok true = true);
  tpsP2_res0 : res = 0;
  tpsP2_peak : peak' = Z.max peak (Ledger.lsum Lam');
  tpsP2_grow : (exists Dold Dnew Dr a, Permutation D (Dold ++ Dr) /\ Permutation Do (Dnew ++ (a, Z.of_nat (length
      kname) + 1) :: Dr ++ Dw) /\ (forall a' k', In (a', k') (Dnew ++ [(a, Z.of_nat (length kname) + 1)]) -> In (a',
      k') Dold \/ ~ In (a' - cf_head, k' + cf_head) (ablocks B ly S)) /\ (n < cap /\ Dold = [] /\ Dnew = [] \/ n = cap
      /\ Dold = kids_blkR kids cap ++ keys_blkR 6 keys cap /\ exists k' y', Dnew = [(k', 56 * cap2R cap); (y', 8 *
      cap2R cap)]));
  tpsP2_node : pj_nodeR segs (rdW W' mem') (prh_lin Lam') o (PjTree.JObj (PjTree.pj_set_model ms kname tv)) Do;
  tpsP2_tblk : (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) Dw) (PresetReqAtNoMiss.tblk
      tv) -> length (flat_map PjRoundTrip.ech kname) = length kname -> Permutation (map (fun b => snd b + cf_head) Do)
      (PresetReqAtNoMiss.tblk (PjTree.JObj (PjTree.pj_set_model ms kname tv))));
  tpsP2_freeord : (cf_head = PresetReqAt.HEAD -> (forall nv, (PjTree.depth tv <= nv)%nat -> exists Fw, pj_foR segs (rdW
      W mem) (prh_lin Lam) nv w Dw Fw /\ map (fun b => snd b + cf_head) Fw = PresetReqAt.fo tv) -> length (flat_map
      PjRoundTrip.ech kname) = length kname -> forall nn, (PjTree.depth (PjTree.JObj (PjTree.pj_set_model ms kname tv))
      <= nn)%nat -> exists F, pj_foR segs (rdW W' mem') (prh_lin Lam') nn o Do F /\ map (fun b => snd b + cf_head) F =
      PresetReqAt.fo (PjTree.JObj (PjTree.pj_set_model ms kname tv))) }.

Lemma tpsP_R2_of : forall (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (o w : Z) (ms : list
    (list Z * PjTree.jv)) (tv : PjTree.jv) (D Dw : list (Z * Z)) (kids keys n cap : Z) (kname : list Z) (Lam : list (Z
    * Z)) (peak cnt fail : Z) (W' : world segs) (mem' : word -> option byte) (Lam' : list (Z * Z)) (peak' res : Z) (c :
    nat) (ok : list bool) (Do : list (Z * Z)),
  tpsP_A2 ly S W mem o w ms tv D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok Do ->
  tpsP_R2 ly S W mem o w ms tv D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok Do.
Proof.
  intros ly S W mem o w ms tv D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok Do H. destruct H
      as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  exact {| tpsP2_absent := H0; tpsP2_window := H1; tpsP2_c := H2; tpsP2_oks := H3; tpsP2_res0 := H4; tpsP2_peak := H5;
      tpsP2_grow := H6; tpsP2_node := H7; tpsP2_tblk := H8; tpsP2_freeord := H9 |}.
Qed.

Lemma tpsP_A2_of_R : forall (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (o w : Z) (ms :
    list (list Z * PjTree.jv)) (tv : PjTree.jv) (D Dw : list (Z * Z)) (kids keys n cap : Z) (kname : list Z) (Lam :
    list (Z * Z)) (peak cnt fail : Z) (W' : world segs) (mem' : word -> option byte) (Lam' : list (Z * Z)) (peak' res :
    Z) (c : nat) (ok : list bool) (Do : list (Z * Z)),
  tpsP_R2 ly S W mem o w ms tv D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok Do ->
  tpsP_A2 ly S W mem o w ms tv D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok Do.
Proof.
  intros ly S W mem o w ms tv D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok Do HR.
  exact (conj (tpsP2_absent HR) (conj (tpsP2_window HR) (conj (tpsP2_c HR) (conj (tpsP2_oks HR) (conj (tpsP2_res0 HR)
      (conj (tpsP2_peak HR) (conj (tpsP2_grow HR) (conj (tpsP2_node HR) (conj (tpsP2_tblk HR) (tpsP2_freeord
      HR)))))))))).
Qed.

Record tpsP_R3 (ly : alayout) (S : astate) (o : Z) (ms : list (list Z * PjTree.jv)) (D Dw : list (Z * Z)) (kids keys n
    cap : Z) (kname : list Z) (Lam : list (Z * Z)) (peak cnt fail : Z) (W' : world segs) (mem' : word -> option byte)
    (Lam' : list (Z * Z)) (peak' res : Z) (c : nat) (ok : list bool) (Do : list (Z * Z)) : Prop := {
  tpsP3_absent : ~ In kname (map fst ms);
  tpsP3_c_range : (1 <= c <= length (prhPj_set_trace n cap kname))%nat;
  tpsP3_refused : nth (c - 1) ok true = false;
  tpsP3_oks : (forall i, (i < c - 1)%nat -> nth i ok true = true);
  tpsP3_res_m1 : res = -1;
  tpsP3_peak : peak' = Z.max (Z.max peak (Ledger.lsum Lam' + Ledger.lsum Dw)) (prh_refused_peak ok cnt fail c (map
      (Z.add (Ledger.lsum Lam)) (prh_ev_helds (prhPj_set_trace n cap kname))));
  tpsP3_grow : (exists Dold Dnew Dr, Permutation D (Dold ++ Dr) /\ Permutation Do (Dnew ++ Dr) /\ prhPj_new ly S Dnew
      /\ (c = 1%nat /\ Dold = [] /\ Dnew = [] \/ n = cap /\ c = 2%nat /\ Dold = kids_blkR kids cap /\ (exists k', Dnew
      = [(k', 56 * cap2R cap)]) \/ n = cap /\ c = 3%nat /\ Dold = kids_blkR kids cap ++ keys_blkR 6 keys cap /\ exists
      k' y', Dnew = [(k', 56 * cap2R cap); (y', 8 * cap2R cap)]));
  tpsP3_fd : pj_fdR segs (rdW W' mem') (prh_lin Lam') (PjTree.depth (PjTree.JObj ms)) o Do;
  tpsP3_node : (c = length (prhPj_set_trace n cap kname) -> pj_nodeR segs (rdW W' mem') (prh_lin Lam') o (PjTree.JObj
      ms) Do) }.

Lemma tpsP_R3_of : forall (ly : alayout) (S : astate) (o : Z) (ms : list (list Z * PjTree.jv)) (D Dw : list (Z * Z))
    (kids keys n cap : Z) (kname : list Z) (Lam : list (Z * Z)) (peak cnt fail : Z) (W' : world segs) (mem' : word ->
    option byte) (Lam' : list (Z * Z)) (peak' res : Z) (c : nat) (ok : list bool) (Do : list (Z * Z)),
  tpsP_A3 ly S o ms D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok Do ->
  tpsP_R3 ly S o ms D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok Do.
Proof.
  intros ly S o ms D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok Do H. destruct H as (H0 &
      H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  exact {| tpsP3_absent := H0; tpsP3_c_range := H1; tpsP3_refused := H2; tpsP3_oks := H3; tpsP3_res_m1 := H4;
      tpsP3_peak := H5; tpsP3_grow := H6; tpsP3_fd := H7; tpsP3_node := H8 |}.
Qed.

Lemma tpsP_A3_of_R : forall (ly : alayout) (S : astate) (o : Z) (ms : list (list Z * PjTree.jv)) (D Dw : list (Z * Z))
    (kids keys n cap : Z) (kname : list Z) (Lam : list (Z * Z)) (peak cnt fail : Z) (W' : world segs) (mem' : word ->
    option byte) (Lam' : list (Z * Z)) (peak' res : Z) (c : nat) (ok : list bool) (Do : list (Z * Z)),
  tpsP_R3 ly S o ms D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok Do ->
  tpsP_A3 ly S o ms D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok Do.
Proof.
  intros ly S o ms D Dw kids keys n cap kname Lam peak cnt fail W' mem' Lam' peak' res c ok Do HR.
  exact (conj (tpsP3_absent HR) (conj (tpsP3_c_range HR) (conj (tpsP3_refused HR) (conj (tpsP3_oks HR) (conj
      (tpsP3_res_m1 HR) (conj (tpsP3_peak HR) (conj (tpsP3_grow HR) (conj (tpsP3_fd HR) (tpsP3_node HR))))))))).
Qed.

Local Unset Implicit Arguments.

(* pj_string (:406-411; plain pj_string_c.v:26-56): memset (v, 0, 56), type = PJ_STRING (4), str = strdup (s ? s : "").
   The outcome is fuzz_strdup's (prh_alloc_post at len + 1, refusal arm included): success -> 0 and v the string node
   over the new block; failure (chosen or refused) -> -1, v's header type 4 and every other byte 0.
   FAMILY: ROUND-TRIP (the rewrite), ENTRY-keyed list (the header): the rp_* binders, the position and the run
   premise at entry; it calls fuzz_strdup (post-form). *)
Definition tpj_string_specX (CTX0 : list (list Z)) : Prop :=
  forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch d v s (cs : list Z) Lam peak cnt fail ran most own,
  fpre B ARx STK_pj_string ly S Hp W regs mem md ch -> prh_univ_closure B CTX0 -> room_live_cf S ->
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* THE RUN HAS AT MOST 4 CALLS: A17's prefix bound needs it where this text pays fuzz_strdup's
     hull budget from its position (lib/A/PresetHullPay.v hull_budget_of_room_pos) *)
  (length rp_os <= 4)%nat ->
  (* THE RUN'S STRTOD MODEL IS KEYED (HP_sm; tpj_set_specX's note): ReaderRes.jr_strtod where rp_sm stood *)
  (* THE CALL'S ALLOCATIONS ARE CONSUMER ALLOCATIONS OF THE RUN (the kit owner's ruling 2026-10-29, the NAMED
     entry premise of the ENTRY-KEYED texts, here as in the three check texts). With the entry position and the run
     premise, P8 (PresetCfnA.preset_no_refusal; a NULL of malloc_cf is primary-only, YG0dcf.malloc_cf_null_post) and
     the engine's granted paths (PRH_Base.prh_rpost_granted over amreal, YG0d.v:73-92) exclude a REAL refusal at the
     call's one allocation (the strdup: fuzz_strdup's outcome clause, PRH_FnAlloc), so the post states the refusal arm
     DEAD (DEAD-PJSTRING). Supplied by the caller (check_round_trip's rewrite) from its own prh_cons_from
     (PRH_Base.prh_cons_from_app_iff splits its window). *)
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i (length (prhPj_string_evs (Z.of_nat (length cs)) cnt fail)) ->
  getr regs 10 = w64 v -> getr regs 11 = w64 s ->
  (* v is below alloc_ceiling (the image-B pj walker's finding against a3bdeca3920): pj_string holds v in s0 at its
     `jal fuzz_strdup` (B 0x8722c `mv s0, a0`, the call at B 0x87270), so strdup's fpre needs the chain from s0 = v;
     prhPj_slot's fourth case puts v in the caller window on the real stack, which would make that chain an fpchain
     reading stack words above sp + d that no premise makes present. Below the ceiling, achain's bad_next cuts it at
     once. This completes the set of four: pj_free, pj_parse, pj_set and pj_string, the same bound for the same
     reason. *)
  fwin ly W regs mem d -> prhPj_slot STK_pj_string d ly S Lam W regs mem v -> v < YM05.alloc_ceiling ->
  (* THE HEAD IS AT LEAST ONE WORD WIDE (the image-B pj walker's finding from the image-B pj_string walk): with cf_head < 8 and v
     starting a harness block, pj_string's 56-byte memset of the node overwrites the block's head word and breaks
     the ledger. Preset's cf_head is 16, so the instance discharges it by the allocator-model owner's preset_head_wide; the GENERIC
     text states it because it is the thing other units instantiate. The kit's one spelling, PRH_Base.v's
     prh_head_wide := 8 <= cf_head. *)
  prh_head_wide ->
  (s = 0 /\ cs = [] \/
   s <> 0 /\ cstr_ok W mem s cs /\ kept_at B Lam s (Z.of_nat (length cs) + 1) /\
   (s + Z.of_nat (length cs) + 1 <= v \/ v + 56 <= s)) ->
  Z.of_nat (length cs) + 1 + cf_head < cf_malloc_max ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (* PER-CALL, SO GUARDED BY ITS CALL'S SUCCESS FLAG (the unit owner's peak-bytes-102 signing, 2026-10-29; the same
     shape as the tx rows' `f0 = 0 ->` guard and as TX-RUNAT-F0): the bytes this call adds are owed only on the path
     where the allocation HAPPENS, that is at cnt <> fail. The live-bytes owner proves the entry sums (M1 + M2 + M6, statement
     owned by the S1 owner); the kit's half is the guard and nothing else. *)
  (cnt <> fail -> blocks_bytes S + LIVE_pj_string (Z.of_nat (length cs)) <= LIVE_MAX) ->
  (* ITS RUN EVENT, as an entry premise: the strdup's HMal, or nothing when the harness chose this allocation to
     fail (prhPj_string_evs; the model's set_evs head, supplied by prhPj_string_evs_supply) *)
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (prhPj_string_evs (Z.of_nat (length cs)) cnt fail) ->
  SRr segs W (cfg_at segs (pa_sigma AS_pj_string) regs mem md)
    (fpostWm B ARx SK STK_pj_string d [(v, v + 56)] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\
       exists a, prh_alloc_post B (Z.of_nat (length cs) + 1) ly S Hp W Lam peak cnt fail ran most own a ly' S' Hp' W' mem' /\
       (* DEAD-PJSTRING (the refusal arm DEAD under prh_cons_from, above; three supports: PRH_Base's ENTRY-KEYED
          note): a = 0 follows the chosen failure
          (cnt = fail) or a REAL refusal; prh_cons_from excludes the refusal, so with no chosen failure at this call
          (cnt <> fail, the pick condition of PRH_FnAlloc.tfuzz_malloc_specX's outcome clause) the strdup GRANTED. The
          chosen failure is NOT a refusal and prh_cons_from does not exclude it (its event list is then empty), so the
          conjunct is stated under cnt <> fail and claims no more; the a = 0 disjunct of prh_alloc_post stays. *)
       (cnt <> fail -> a <> 0) /\
       (* THE EXACT ADVANCE (the position sweep): the strdup's event when it took one (a <> 0), and none when the
          harness chose this allocation to fail (cnt = fail: failing() returns NULL without calling the
          allocator, and the model has no event either). The third case, a = 0 with cnt <> fail, is a REFUSAL:
          the model's list has the HMal and the instance made it not, so no position of the model's run
          describes S'; a refusal is excluded once, globally, by the driver (P8's preset_no_refusal). *)
       (a <> 0 \/ cnt = fail ->
          exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os
            (rp_i + length (prhPj_string_evs (Z.of_nat (length cs)) cnt fail))%nat rp_H0 hist' S') /\
       (a <> 0 -> getr regs' 10 = w64 0 /\
          pj_nodeR segs (rdW W' mem') (prh_lin ((a, Z.of_nat (length cs) + 1) :: Lam)) v (PjTree.JStr cs)
            [(a, Z.of_nat (length cs) + 1)]) /\
       (a = 0 -> getr regs' 10 = w64 (-1) /\ pj_rwR segs (rdW W' mem') v /\
          bytes_at W' mem' v ([4; 0; 0; 0] ++ repeat 0 52) /\
          pj_fdR segs (rdW W' mem') (prh_lin Lam) 0 v []))).

End c.
