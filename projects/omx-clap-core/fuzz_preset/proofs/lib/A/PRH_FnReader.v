(* This file carries the kit's text of the re-hiding move for its two crossing texts
   (`PRIMED-SHAPES.md (sha256 9e4880d18317; internal record)` sec. 2.11, 2.H4): tparse_string_specX concludes SRr' segs RZ_cf and keeps fpostWbm, which is
   AFTER-FREE-ONLY and already at wle' (PRH_Base.v); tgrow_specX concludes SRr' segs RZ_cf with the post
   fpostWmR .. (wle' segs RZ_cf) (fpostWm is SHARED; its refusal evidence was already world-free). tgrP_Q_check
   matches the primed conclusion. The unit owner's ruling C2 (2026-10-31 04:19Z) struck the scratch
   notice that stood here, by a comment-only edit that keeps the header at 7 lines, so every line after it keeps its
   number and the line numbers other files cite below the header still hold. *)
(* fuzz_preset, program part (the kit's reader texts): the ASan contract TEXTS of six functions of the JSON reader of
   src/preset_file.c (omx-clap-core 246923f04ac0): hex4, put_utf8, literal, parse_string, grow, and skip_ws (out of line
   in image B only). parse_value and parse_items are NOT here: the kit owner ruled that the recursive-reader slice's author writes
   their texts, with lib/A/PRH_Reader.v.
   FORM: cgif's per-function form as PRH_FnAlloc.v states it: fpre (YCbqG's afn_pre_x + the read-only view), argument
   registers, the alloc.c ledger (PRH_Base.v prh_ledger), and SRr to the return address (SRr' segs RZ_cf at
   parse_string and grow). IMAGE-PARAMETRIC: entries are pa_sigma AS_<fn>, frames STK_<fn>; no image number.
   WRITES INTO THE CALLER'S REAL STACK. hex4's out (&lo / &cp: parse_string's own frame, A sp + 36 at 0x87d28) and the
   reader's struct pj_in (pj_parse's frame: A `mv a0, sp` 0x85e60, B `addi a0, sp, 8` 0x86330) lie above the callee's
   entry sp, where the plain journal forbids a write. Those texts take the kit's CALLER-WINDOW form (PRH_Base.v fwin /
   fpostW, the Pj part's form of the fm port's FMH_Fn.v readings_spec): the journal runs at (STK_<fn> + e) (spZ regs + e), the caller
   granting the e bytes above the entry sp that hold the written cells; the written caller cells go IN FP, and every
   other byte of [sp, sp + e) keeps its value. At e = 0 fpostW is fpost. The caller picks e so that the window ends
   inside its own (pj_parse: e reaching its frame; parse_string for hex4: e = its frame size, 144 in A).
   A write into a node (literal's v, grow's v) may land in a live harness block, another live allocator block or a
   live fake-stack frame, or in the extension (prhReader_at); all go in FP. In the asan images the harness's struct pj
   locals are fake-frame bytes (LLVMFuzzerTestOneInput / check_* take __asan_stack_malloc_N frames).
   FUNCTIONAL CONTENT: preset's released plain contracts lib/Prog/{hex4,put_utf8,literal,parse_string,grow}_c.v,
   restated; skip_ws has no plain contract of its own (it is inlined in the plain image) and is restated from the
   source :36-40 and the model's PjGrammar.skip. The plain room machinery (rf_ok / rf_room) becomes the live room
   blocks_bytes S + LIVE_<fn> <= LIVE_MAX and the request bound LIVE_<fn> < cf_malloc_max (cf_head is alloc.c's HEAD);
   each allocation outcome adds the class-full allocator's REFUSAL arm (PRH_FnAlloc.v prh_alloc_post (2),
   tfuzz_realloc_specX's third arm): for the reader an ordinary failure, with g_ran_out = 1.
   REUSE (no lemma cited): the reader memory predicates are the kit's lib/A/PRH_Reader.v (the recursive-reader author's; pj_in_okR,
   rest_atR, pj_hdrR, pj_apartR, pj_cbytesR over mrestrict (w_H W) mem, the text a list Z), shared with the
   parse_value / parse_items and pj_* texts; the PURE spec layer is machine-state-free (PjGrammar: scan, decode, hex4,
   utf8, skip, prefixb; Ledger.lsum); grow's slot shapes are PRH_Reader.v's cap2R / kids_blkR / keys_blkR /
   pj_slots_atR (ReaderRes.v:74-79, PjStruct.v:109-112 restated there). No plain lib/Prog memory-predicate file
   (PjIn, PjStruct) and no released lib/Prog program file is Required.
   NAMED GAPS:
   (G2) hex4's out is stated on the caller's real stack only (in the extension), the program's one use; the plain's
        "any writable o" is narrowed to it. q (struct pj_in) likewise: only pj_parse makes one, on its real stack.
   (G3) a text the reader reads after a call (parse_string: after fuzz_malloc; literal: bcmp after strlen) or keeps in
        its post (skip_ws) is kept_at (a live harness block's user bytes, or a read-only registered global) or inside a
        live allocator block whose base is NOT a hidden head (prhReader_home). MEASURED, which side each caller's text
        falls on: the fuzzer input is a whole non-harness allocator block, or A_EMPTY with size 0 (PresetCfnA.v:858);
        parse_noting's three texts are fuzz_copy copies taken with the malloc wrapper (check_no_overread, A 0x81a90 /
        0x81ad4 / 0x81b28):
        non-harness blocks; round_trip_text's and check_round_trip's texts are pj_write buffers (fuzz_realloc): harness
        blocks in Lam. So the home does not use the generic "AR keeps a live block's shadow" law, FALSE of a harness
        block's hidden head; it DEPENDS ON the cf shadow law: shadow 0 on a block's user range [a + cf_head,
        a + req_size n) (the allocator-model owner's AR_head_shadow_cf, derived from its fields) and on the first cf_head bytes when the
        base is not in Hp (YG0dcf.v:614-618). A text on the real stack (the plain text_ok's `spZ regs <= text`) is
        not covered.
   (G4) grow's keys-refusal arm carries the refusal leaf at an existential call state (the state after the kids
        realloc, which the text does not name).
   (G5) skip_ws is a B-only function (A inlines it): the text is stated image-parametrically, as town_specX is, and
        only image B's walk uses it.
   (G6) runtime calls: literal's strlen over the word (cstr_ok) and bcmp over len bytes of the text and of the word
        (both addressable). Their texts: YGcallMxmn.v:1175 astrlen_realizes_xro, YGcallMx.v:130 abcmp_realizes_x; nothing else.
        THE WORD IS NOT kept_at (dropped, the kit owner's ruling): literal reads it only through strlen and then bcmp,
        with no program or allocator call between them (both keep the shadow), and the leaf-lemma author proved literal on both
        images without it. Its premises are cstr_ok and the leaf-lemma author's leaf word premises (origin 4e25a816d2c,
        lib/Prog/literal_xs.v:45 tliteral_specX), copied over rdW W mem with STK_literal for its LIT_STK (both are the
        frame 80 plus 2 * ESTACK): the bytes cw ++ 0 :: slack at w, no NUL in cw, the slack reaching the next 8-byte
        boundary, the 2 ^ 63 bound, and the word with its slack outside literal's stack window; so this text implies
        the leaf's. Background measurement (no premise rests on it): "true", "false", "null" at A .rodata 0x21460 /
        0x21480 / 0x214a0 each have an asan_globals descriptor of length + 1 bytes (5 / 6 / 5), size_with_redzone 32 (redzone 27 / 26 / 27), as do image
        B's at the same addresses (pyelftools over pau-preset-102's unstripped fuzz_preset.asan / .asan-ubsan). A walk
        discharges the word's cstr_ok by PRH_Base.cstr_ok_ro, its image premise decided by YGcallRoStr.ro_str_check /
        ro_str_check_ok (vm_compute, as S8aWord.v ev_lit_img_A does for ex_value's three literals at A').
   room: room_live_cf (PRH_Base.v, owned by the allocator-model owner), room_cf at none; margins removed (the kit owner's ruling (B)).
   parse_string and grow take room_live_cf S on entry and give room_live_cf S' in every arm; the two give-back
   conjuncts each had (RK_free + kr, RK_realloc + kr) are dropped, room_live_cf S' already holding in those arms.
   Their allocator calls (parse_string's malloc, grow's reallocs) are not at their callers' entry-state allocator
   call, so they state no primary room: it comes from P8's preset_room through the driver. hex4, put_utf8, literal and
   skip_ws make no allocator call: their posts carry room_live_cf S -> room_live_cf S'.
   THE FREE'S TRACE (MEASURED): parse_string keeps q, the struct pj_in pointer, in s0 (A `mv s0, a0` 0x87990, B
   0x88134; s0 not written again before the epilogue) through its one `jal fuzz_free` (A 0x87e4c, B 0x885e0; return
   site pi_ret_sites F_parse_string RT_fuzz_free), and fuzz_free tail-calls the free wrapper with that ra, so the
   chain at the call is NOT empty: it is the frame chain read from q, a pointer into pj_parse's frame, whose words lie
   in the callers' frames above parse_string's sp and are data (in image B q - 8 is pj_parse's never-written sp + 0).
   The free's trace over every such chain is the closure's (PRH_Base.prh_univ_closure clause 4b at any chain word,
   4a at image A's code word); the empty-chain form In [pc0; r] does not apply.
   allocator traces: prh_univ_closure (PRH_Base.v), dropped prh_malloc_univ (parse_string, grow), the realloc pair
   In [cf_pc_realloc_ra0] / In [cf_pc_realloc_ra0; pi_ret_realloc] (grow) and parse_string's membership premise
   In (raZ regs :: spine ch) CTX; prh_free_univ_at (parse_string's free over the chain from q) is no longer taken: its
   chain's first word is a DATA word on B', held only by clause 4b's wild arm.
   CALLER REQUIREMENT (not a gap): the caller cells written above the entry sp (q's p field, hex4's out, a node in the
   extension) are in FP, as fpostW asks; a caller composing such a call with YCbqG's ajournal_x_sub (aed5d9ab225)
   names those cells in its own FP, or they lie in its own new fake frame or in a block it made (pj_parse names its
   struct pj_in, parse_string its out slot).
   The ASan owner's statement classes: (R1) every caller buffer a post keeps lies in a live block (the text: prhReader_home,
   which skip_ws now also takes; grow's old kids / keys: harness blocks) or in the caller's frame disjoint from every
   byte the function writes (q's other fields, v's other bytes: disjointness premises); (R2) literal's interceptors
   (strlen, bcmp) do not read the AddrHashMap meta region (that is the stdio interceptors' FILE metadata, cgif
   AE2f.v:208-211 meta_pre for fflush / fclose), so no asrc_meta_inv premise.
   Statements only.
   THE HULL BUDGET (route (b) of the allocator hull premise; lib/Spec/PresetHullBudget.v,
   PRH_FnAlloc.v's header): parse_string and grow call the allocator texts with no position, so each takes
   `hull_budget S Eg` over its ALL-GRANTED events Eg (the list its room counts name) and pays its callees' budgets
   from it; each post states `hull_used S S' Eg` with the same Eg.
   FAMILY (the kit owner's condition 4, 2026-10-29 ~17:25Z): every text in this file is READING-CHAIN / LEAF:
   POST-IMPLICATION form, no entry position, no entry run premise. hex4, put_utf8, literal and skip_ws make no
   allocator call and state no position; parse_string and grow state the position transfer in each post arm. They
   call only post-form texts (this file's four leaves and PRH_FnAlloc.v's fuzz_malloc / fuzz_free / fuzz_realloc).
   The writer / tx / round-trip / crcs / as_written texts (ENTRY-keyed list plus the rp_on entry spelling) may call
   them, as may every post-form text.
   THE MODEL-RUN POSITION, POST-IMPLICATION FORM (the kit owner's YES with five conditions, 2026-10-29 ~17:25Z): no
   text here takes a position of the model run or the run's events at entry. Each post arm of parse_string and grow
   states the transfer as an implication over the run (PresetRoomPos.iface_room_pos, lib/Spec/PresetRoomPos.v, the
   one home; PRH_Base.prh_run_at):
     forall sm x os i H0 hist, iface_room_pos sm x os i H0 hist S -> prh_run_at sm x os i E ->
       exists hist', iface_room_pos sm x os (i + length E) H0 hist' S'
   with E the arm's OWN events: this file's list function (prhPs_evs, prhPg_evs) applied to the INSTANCE's outcomes
   on that arm ([] when no allocator call is made, [false] for a NULL, [true] for a block, [true; false] and
   [true; true] for grow's two reallocs). The advance is EXACT (i + length E, never <=); a NULL arm has E = [] and
   states the implication as the identity on the position. ONLY the position is under the implication: the return
   value, the memory, the ledger, the blocks and the live requests are unconditional. The bare pair
   `exists rp_i' rp_hist', (rp_i <= rp_i')%nat /\ iface_room_pos .. rp_i' .. rp_hist' S'`, which this header once
   called load-bearing, is FALSE (PRH_Base.prh_run_at's note: three measurements). The ENTRY-keyed form these two
   texts had until this restatement (iface_room_pos at rp_i and prh_run_at rp_i of the list under the binder rp_ok,
   both at entry) is gone; walks written against it carry AGREE-PREFIX below.
   THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS; the kit owner's ruling ~18:5xZ): parse_string's and
   grow's posts bind no outcome list (each arm is one outcome), so the rule is stated in each REFUSED arm as its
   exclusion: no model run and position whose next events are the ALL-GRANTED list (prhPs_evs .. [] / prhPg_evs ..
   []), its allocations CONSUMER events (PRH_Base.prh_cons_from), meets that arm. A caller at such a run then has a
   granted arm (E = the granted list by prhPs_evs_arm / prhPg_evs_arm) or a chosen-failure arm, which its own
   g_fail_at excludes.
   THE MODEL'S GRANT LIST (F1 of the position census, its record, the internal file CENSUS.md). Inside check_no_overread's readings the
   model REFUSES for real (PresetRun.okof o: okk j refuses the j-th allocation, and a refused grant makes no event,
   PresetReqAt.rd_hev (EFail _) = []), and that refusal is NOT the harness's chosen failure (a reading runs with
   g_fail_at = SIZE_MAX). So no text derives the model's grants from cnt / fail (the slice walker's template premise
   `fst (take ok) = negb (cnt =? fail)` did, and is false on that path). In the post-implication form:
   - NO BINDER: no text binds the model's grant list. E is keyed on the INSTANCE's outcomes on the arm (parse_string,
     grow) or on the outcomes ok and trace tr the post binds (parse_value, parse_items: E = PresetReqAt.rd_hevs tr).
   - NO AGREEMENT: the caller applies the implication AFTER the call, at a model run and position it picks to match
     the instance's outcomes, so no post names an agreement between the model's grants and the instance's (the reader walk's
     M2 case, the model refusing where the instance grants, does not arise: the caller does not pick such a run).
   - SUPPLY (condition 3), the caller's list at the call is the arm's E: prhPs_evs_of_value / prhPs_evs_of_name /
     prhPs_evs_supply (the caller's list under its own outcomes ok gives prhPs_evs x ok), then prhPs_evs_arm (that is
     the arm's list when ok's one grant is the instance's); prhPg_evs_of_items / prhPg_evs_supply, then
     prhPg_evs_arm, for grow; prhReader_run_at_mid for parse_value / parse_items (the caller's list is rd_hevs of its
     trace, with the callee's trace inside it). prhPs_evs_model / prhPg_evs_model: the lists are the model's own
     (rd_hevs of the grammar function's trace) when cf_head = PresetReqAt.HEAD. Inside a walk the leaves' own
     implications take their one-event lists from the arm's list by PRH_Base.prh_run_at_one / prh_run_at_app_iff
     (prhPs_evs_mal / _fr, prhPg_evs_kids / _keys).
   THE GRANT LIST'S FALSE ENTRIES ARE OF TWO KINDS (the kit owner's wording on the free-caller walker's correction, 2026-10-29). rp_ok
   is the model's grant list. (1) okof o_k in the three P1 readings is a real ALLOCATOR REFUSAL, not the chosen failure
   (:127-131 above). (2) okk (pick x took) in check_reject_clean_starved IS the model's list for the harness's
   fuzz_alloc_fail (pick) - the CHOSEN FAILURE, not a refusal (PRH_FnCheck.v ck_crcs_evs :322-323; PresetReqAt.v
   :182-183 okk, :340-341 starved_parse). In NEITHER case does the kit prove that the instance's cnt = fail falls on
   that entry, so a chosen-failure arm must not assume `nth j rp_ok true = negb (cnt =? fail)`. These are facts of the
   MODEL and hold whether or not a text binds the list. At this tip the question does not arise: the post-implication
   form binds no grant list (:118-120 'The ENTRY-keyed form .. is gone', :132 'NO BINDER'), and tgrow /
   tparse_string key E on the MACHINE outcome on both their chosen-failure and refused arms, with E = [] and no
   advance: tgrow's kids arms :1286-1301 and :1303-1360 (the keys arms below them alike), tparse_string's
   :620-635 and :637-666.
   THE LIVE COUNTS AT THE INNER CALLS (the K1-batch walk-kit lead's ruling R1 as amended, 2026-10-29, on the kit owner's (b)): the
   leaves' own premises `sec_cnt S <= LSEC + DRV` (fuzz_malloc, fuzz_realloc) and `ccnt24 S <= L24 + DRV` (also
   fuzz_free) at each INNER call state came from the entry position (the driver-contract owner's counts_of_room_pos_rl). They are now
   position-free premises of parse_string and grow, which REPLACE counts_of_room_pos_rl at the inner calls: the PEAK
   of each count along the text's ALL-GRANTED events Eg (the list function at ok = []), from the entry's live
   requests:
     Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) Eg) <= LSEC + DRV
     Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) Eg)
       <= L24 + DRV
   An instance with refusals makes a prefix of Eg before it stops allocating, so the one premise covers every
   outcome (PresetRun.pkR_prefix). The list is counts_of_room_pos's (lib/Spec/PresetRoomCounts.v), its predicates are these up to
   conversion, and the bridge to the leaves' sec_cnt / ccnt24 is CONVERSION: CfRoomLivePreset.rs_live_blocks is
   reflexivity, sec_cnt filters rl_sec_req (PresetLiveSec.sec_req's body, negb PresetRoom.is_primary), ccnt24 is
   PresetRoom.ccnt kBatchClass (the filter of in_cls 24, kBatchClass = 24), and PresetReqAt.cnt is the length of a
   filter. The counts read requests with the instance's cf_head (prhPs_evs, prhPg_evs) or the model's HEAD
   (PresetReqAt.rd_hevs, PRH_FnParse.v); the two agree at preset's CfParams (cf_head = PresetReqAt.HEAD = 16), as
   the position itself does. Each post arm gives the caller its chaining fact, EXACT: the live
   requests after the call are the entry's moved by the arm's E,
     Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
       (YGcfRoom.room_of_cf S)) E)
   (it follows from the arm's own blocks facts: an equality, an append, or prhReader_swap), so a caller splits its
   own peak premise with PresetRun.pkR_app. A caller holding the run's position derives the premise from P8 (owner of
   that derivation: the caller's walk); after a REAL refusal the ledger-side bound is the P8 owner's open half, not
   derived here.
   THE OPEN CORRESPONDENCE (owned by the owner of P8 and the run model; NOT assumed by any text here): the
   allocator's real outcome at each harness allocation follows the model's grant list (a refusal in reading k exactly
   where okof o_k refuses, no refusal anywhere else). No kit statement uses it (`git grep -w okof` over lib/A and
   lib/Spec/PresetRoomPos*.v at kit 5f43593d98f6: hits in this header only). It is what a caller still needs to
   CHOOSE the model run that matches the instance's outcomes (the post-implication form's late choice above). Its
   second half at CONSUMER positions (no refusal at an allocation hcons flags true) is no longer open for these
   texts: it is each text's outcome clause (THE OUTCOME above), derived from P8 and the engine's grant, not assumed.
   The first half (where a P1 reading refuses) stays the caller's choice of os.
   AGREE-PREFIX, THE ONE SPELLING of what a walk against the OLD entry-keyed texts carries (the kit owner's ruling,
   2026-10-29; the correspondence above is the P8 owner's): `prhReader_agree ok rp_ok k` (this file), with ok = the
   instance outcomes of the allocator calls the walk has made SO FAR in this function (the earlier callees' posts'
   outcomes, appended in call order) and k = their number - the PREFIX form, forall j < k, nth j ok true =
   nth j rp_ok true. Why it was needed (the image-B parse_items walk, image B parse_items' member loop, grow at 0x87b74 then
   parse_string at 0x87c0c): an entry-keyed callee's entry position and run premise are stated at an index the
   caller knows only on the arm where the instance's outcomes agree with rp_ok; when a realloc SUCCEEDS while
   nth 0 rp_ok true = false, the model makes no event and "the instance holds a block the model never counted", so
   no index exists. The texts of this file and of PRH_FnParse.v NO LONGER USE IT: in the post-implication form the
   caller chooses the model run after the call to match the instance's outcomes, so that case disappears at the
   reader's own calls. The Definition stays for the walks on the old texts; it becomes a citation the day
   the P8 owner proves the correspondence.
   INTERIM, PENDING MEASUREMENT ON THE BATCH TEXTS (the unit owner's ruling through the kit owner, 2026-10-30, which
   REVERSES an earlier "A' needs no prefix" reading): the one result claiming this premise is unnecessary was
   measured against an EARLIER VERSION OF THE TEXTS, not against our texts. The recursive-reader author's A' parse_items master 28657ce2d2a4 is
   built on PRH_FnParse.v 94232293d483, which STILL HAS DW (9 uses) and has no pj_ncapR / pj_foR at all (ours: no DW;
   pj_foR :404, pj_ncapR :411); its rd_ledger_move already takes most and gt and carries prh_refused_peak on every arm, as ours
   (:188-197, :385). So that result says nothing about these texts (the B' walker measured the difference). The recursive-reader author
   re-measures on the DW-free text and reports with its INTEGRATED route-of-record sha - a scratch green is not a
   lane result. The B' walker adds no prefix to its B' lane and stops to measure if a step seems to need one. The
   Definition and this entry are STRUCK only when both images are measured on the BATCH texts.
   *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Charge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun PresetRoom
  PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
(* the re-hiding move's SRr' and wle' (YA0nH) and preset's zone (YGcfRehidePost.RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the reader's shapes (the caller-window form itself is the kit's fwin / fpostW) ---- *)

(* where n bytes at p that the function writes may lie: a live harness block's user bytes, a live allocator block that
   is not a harness block, a live fake-stack frame, or the granted extension; the written bytes go in FP in every case
   (plain rplace's pj_place, ReaderRes.v:189-195, with the fake frame for the asan image's escaped locals) *)
Definition prhReader_at (ly : alayout) (S : astate) (Lam : list (Z * Z)) (regs : bvmap 5 word) (e p n : Z) : Prop :=
  (exists a k, In (a, k) Lam /\ a <= p /\ p + n <= a + k) \/
  (exists b m, In (b, m) (ablocks B ly S) /\ ~ In (b + cf_head, m - cf_head) Lam /\ b <= p /\ p + n <= b + m) \/
  (exists cid pos, In (cid, pos) (frames S) /\
     frame_addr ly cid pos <= p /\ p + n <= frame_addr ly cid pos + fs_frame_bytes cid) \/
  (spZ regs <= p /\ p + n <= spZ regs + e).

(* where a text the function reads after a call lives, with its shadow facts (G3): a live harness block's user bytes
   or a registered read-only global (kept_at), or a live allocator block whose base is not a hidden head *)
Definition prhReader_home (ly : alayout) (S : astate) (Hp : list Z) (Lam : list (Z * Z)) (p n : Z) : Prop :=
  kept_at B Lam p n \/ (exists b m, In (b, m) (ablocks B ly S) /\ ~ In b Hp /\ b <= p /\ p + n <= b + m).

(* a new block's bytes are addressable (the shadow facts prh_alloc_post's SUCCESS arm gives) *)
Definition prhReader_vis (W : world segs) (mem : word -> option byte) (a n : Z) : Prop :=
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) a n).

(* harness blocks (user address, user size) as allocator blocks and as hidden heads *)
Definition prhReader_ab (D : list (Z * Z)) : list (Z * Z) := map (fun ak => (fst ak - cf_head, snd ak + cf_head)) D.
Definition prhReader_hd (D : list (Z * Z)) : list Z := map (fun ak => fst ak - cf_head) D.

(* the harness blocks Dold were replaced by Dnew (fuzz_realloc's SUCCESS arm, PRH_FnAlloc.v:720-736; fuzz_malloc's,
   PRH_FnAlloc.v:250-257, when the old pointer is NULL and Dold = []): the allocator blocks, the hidden heads and the
   ledger list follow, each up to order *)
Definition prhReader_swap (ly : alayout) (S : astate) (Hp : list Z) (Lam : list (Z * Z))
  (ly' : alayout) (S' : astate) (Hp' : list Z) (Lam' : list (Z * Z)) (Dold Dnew : list (Z * Z)) : Prop :=
  (exists bl, Permutation (ablocks B ly S) (prhReader_ab Dold ++ bl) /\
     Permutation (ablocks B ly' S') (prhReader_ab Dnew ++ bl)) /\
  (exists hl, Permutation Hp (prhReader_hd Dold ++ hl) /\ Permutation Hp' (prhReader_hd Dnew ++ hl)) /\
  (exists Lam0, Permutation Lam (Dold ++ Lam0) /\ Permutation Lam' (Dnew ++ Lam0)).

(* ---- the leaves ---- *)

(* hex4 (preset_file.c:66-87): reads p[0..4) left to right, stopping at the first byte that is not a hex digit; on four
   digits stores the value at out and returns 0, else returns -1 with nothing stored (plain hex4_c.v:26-44; the model is
   PjGrammar.hex4, the same function over Z bytes). out is a slot of the caller's frame (G2), the extension; B's UBSan
   checks (p non-null and not wrapping, out 4-aligned) hold under the premises. No call, no block, no static. *)
Definition thex4_specX : Prop :=
  forall ly S Hp W regs mem md ch e p o (bs : list Z) Lam peak cnt fail ran most own,
  fpre B ARx STK_hex4 ly S Hp W regs mem md ch ->
  getr regs 10 = w64 p -> getr regs 11 = w64 o ->
  length bs = 4%nat -> src_rd W mem p bs ->
  fwin ly W regs mem e ->
  spZ regs <= o -> o + 4 <= spZ regs + e -> o mod 4 = 0 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF o 4 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_hex4) regs mem md)
    (fpostWm B ARx SK STK_hex4 e [(o, o + 4)] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       match PjGrammar.hex4 bs with
       | Some h => getr regs' 10 = w64 0 /\ val_mem segs (rdW W' mem') o 4%nat h
       | None =>
           getr regs' 10 = w64 (-1) /\
           (forall a, o <= a < o + 4 -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a)
       end)).

(* put_utf8 (preset_file.c:89-114): stores the UTF-8 encoding of cp at o and returns its length (plain put_utf8_c.v:19-36;
   PjGrammar.utf8 is the same encoding over Z). Its one caller, parse_string, hands o inside out, the harness block it
   took: the footprint is the encoding's bytes. *)
Definition tput_utf8_specX : Prop :=
  forall ly S Hp W regs mem md ch o cp Lam peak cnt fail ran most own,
  fpre B ARx STK_put_utf8 ly S Hp W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 11 = w64 cp -> 0 < cp <= 1114111 ->
  (exists a k, In (a, k) Lam /\ a <= o /\ o + Z.of_nat (length (PjGrammar.utf8 cp)) <= a + k) ->
  wdest_ok B STK_put_utf8 ly S W regs mem o (Z.of_nat (length (PjGrammar.utf8 cp))) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_put_utf8) regs mem md)
    (fpostm B ARx SK STK_put_utf8 [(o, o + Z.of_nat (length (PjGrammar.utf8 cp)))] regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       getr regs' 10 = w64 (Z.of_nat (length (PjGrammar.utf8 cp))) /\ bytes_at W' mem' o (PjGrammar.utf8 cp) /\
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own)).

(* literal (preset_file.c:266-275): len = strlen (word) (the strlen wrapper); if end - p >= len and bcmp (p, word, len)
   = 0 (the bcmp wrapper): in->p += len, v->type = type, return 0; else -1 with nothing stored (plain literal_c.v:15-44;
   the hit is PjGrammar.prefixb, the model's `lit` test). Writes: q's p field (the extension, G2) and v's type, 4 bytes
   (v is the node, prhReader_at). word is one of the three .rodata literals; strlen, then bcmp read it (G6): cstr_ok and
   the leaf-lemma author's word premises (the bytes with their slack), not kept_at; the text is home (G3). B's UBSan checks (q and v
   8-aligned and non-null, p + len not wrapping) hold under the premises. *)
Definition tliteral_specX : Prop :=
  forall ly S Hp W regs mem md ch e q text len p d (tb : list Z) w (cw slack : list Z) ty v Lam peak cnt fail ran most own,
  fpre B ARx STK_literal ly S Hp W regs mem md ch ->
  getr regs 10 = w64 q -> getr regs 11 = w64 w -> getr regs 12 = w64 ty -> getr regs 13 = w64 v ->
  pj_in_okR segs (rdW W mem) q text len p d tb ->
  fwin ly W regs mem e -> spZ regs <= q -> q + 24 <= spZ regs + e ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 24 ->
  src_rd W mem text tb -> prhReader_home ly S Hp Lam text len ->
  cstr_ok W mem w cw ->
  w + Z.of_nat (length cw) + 1 + Z.of_nat (length slack) <= 2 ^ 63 ->
  garr8 segs (rdW W mem) w (cw ++ 0 :: slack) ->
  ~ In 0 cw -> (- (w + Z.of_nat (length cw) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (spZ regs <= w \/ w + Z.of_nat (length cw) + 1 + Z.of_nat (length slack) <= spZ regs - STK_literal) ->
  0 <= ty <= 2 ->
  v <> 0 -> v mod 8 = 0 -> prhReader_at ly S Lam regs e v 4 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 4 ->
  (v + 4 <= q \/ q + 24 <= v) -> (v + 4 <= text \/ text + len <= v) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_literal) regs mem md)
    (fpostWm B ARx SK STK_literal e [(q, q + 8); (v, v + 4)] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       if PjGrammar.prefixb cw (rest_atR tb text p) then
         getr regs' 10 = w64 0 /\
         pj_in_okR segs (rdW W' mem') q text len (p + Z.of_nat (length cw)) d tb /\
         val_mem segs (rdW W' mem') v 4%nat ty
       else
         getr regs' 10 = w64 (-1) /\
         pj_in_okR segs (rdW W' mem') q text len p d tb /\
         (forall a, q <= a < q + 8 \/ v <= a < v + 4 -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a))).

(* skip_ws (preset_file.c:36-40; out of line in image B only, B 0x86948; inlined in image A, G5): while p < end and *p
   is ' ', '\t', '\n' or '\r', p++, the p field stored at each step (the model's PjGrammar.skip). Writes: q's p field
   only (the extension, G2). B's UBSan checks (q 8-aligned, p non-null, p + 1 not wrapping) hold under pj_in_ok. No
   call, no block, no static. *)
Definition tskip_ws_specX : Prop :=
  forall ly S Hp W regs mem md ch e q text len p d (tb : list Z) Lam peak cnt fail ran most own,
  fpre B ARx STK_skip_ws ly S Hp W regs mem md ch ->
  getr regs 10 = w64 q ->
  pj_in_okR segs (rdW W mem) q text len p d tb ->
  fwin ly W regs mem e -> spZ regs <= q -> q + 24 <= spZ regs + e ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 24 ->
  src_rd W mem text tb -> prhReader_home ly S Hp Lam text len ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_skip_ws) regs mem md)
    (fpostWm B ARx SK STK_skip_ws e [(q, q + 8)] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       pj_in_okR segs (rdW W' mem') q text len
         (text + len - Z.of_nat (length (PjGrammar.skip (rest_atR tb text p)))) d tb)).

(* ---- the allocating functions ---- *)

(* parse_string's live room: the one block it takes, Q + 1 bytes and the head (plain parse_string_c.v:39-40,
   rf_room F b (Q + 17) with HEAD = 16) *)
Definition LIVE_parse_string (Q : nat) : Z := Z.of_nat Q + 1 + cf_head.

(* ---- THE RUN EVENTS OF THE READER (the position sweep in the post-implication form: the header). One home:
   the slice walker's lib/A/Prog/S4_PsBase.v (blob ddfbf3f650fe, commit 322e57164236) proved
   ps_evs, parse_string_room_evs_supply and ps_room_evs_mal / _fr over its entry record; they are taken here over the
   text's own binders, with the grant keyed on an outcome list ok instead of the harness's `cnt =? fail` (F1): on an
   arm of tparse_string_specX's / tgrow_specX's post, ok is the INSTANCE's outcomes on that arm; in the supply lemmas
   it is the caller's own outcomes. So S4_PsBase's ps_evs D is prhPs_evs (ps_x D) applied to an outcome list, and its
   interim premise parse_string_room_evs is now the run premise of tparse_string_specX's post implication. ---- *)

(* AGREE-PREFIX (the header): the instance's outcomes ok AGREE with the model's grant list g on the first k
   allocator calls. Carried by walks against the OLD entry-keyed texts; no text in this file or in PRH_FnParse.v uses
   it since the post-implication restatement (nth's default true is PjGrammar.take's: [] grants) *)
Definition prhReader_agree (ok g : list bool) (k : nat) : Prop :=
  forall j, (j < k)%nat -> nth j ok true = nth j g true.

(* a bound computation's trace starts with the first computation's *)
Lemma prhReader_jbind_pre : forall (A0 B0 : Type) (m : PjGrammar.M A0) (k : A0 -> PjGrammar.M B0) ok,
  exists t, snd (fst (PjGrammar.jbind m k ok)) = snd (fst (m ok)) ++ t.
Proof.
  intros A0 B0 m k ok. unfold PjGrammar.jbind. destruct (m ok) as [[[a|] t] ok1].
  - destruct (k a ok1) as [[r t'] ok2]. exists t'. reflexivity.
  - exists []. rewrite app_nil_r. reflexivity.
Qed.

(* a caller's run premise over a trace gives the premise over any prefix of it *)
Lemma prhReader_run_at_pre : forall sm x os i (t1 t2 : list PjGrammar.ev),
  prh_run_at sm x os i (PresetReqAt.rd_hevs (t1 ++ t2)) -> prh_run_at sm x os i (PresetReqAt.rd_hevs t1).
Proof.
  intros sm x os i t1 t2 H. unfold PresetReqAt.rd_hevs in H. rewrite flat_map_app in H.
  exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H)).
Qed.

(* THE SUPPLY OF A READING-CHAIN CALLEE WHOSE E IS rd_hevs OF ITS POST-BOUND TRACE (parse_value, parse_items): a
   caller's run premise over its own trace t1 ++ t2 ++ t3, the callee's trace t2 after the earlier callees' t1, gives
   the callee's run premise at the position the earlier callees' exact advances name *)
Lemma prhReader_run_at_mid : forall sm x os i (t1 t2 t3 : list PjGrammar.ev),
  prh_run_at sm x os i (PresetReqAt.rd_hevs (t1 ++ t2 ++ t3)) ->
  prh_run_at sm x os (i + length (PresetReqAt.rd_hevs t1))%nat (PresetReqAt.rd_hevs t2).
Proof.
  intros sm x os i t1 t2 t3 H. unfold PresetReqAt.rd_hevs in *. rewrite !flat_map_app in H.
  pose proof (proj2 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H)) as H2.
  exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H2)).
Qed.

(* parse_string's events over the text x after the opening quote, under the outcome list ok: the fuzz_malloc of a
   closed quote's Q + 1 bytes when ok grants it, then on a bad escape the fuzz_free of that block; nothing when the
   quote is not closed or ok refuses (a refused grant makes no event; [] grants every call) *)
Definition prhPs_evs (x : list Z) (ok : list bool) : list PresetReqAt.hev :=
  match PjGrammar.scan x with
  | None => []
  | Some Q =>
      if nth 0 ok true then
        PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head) ::
        match PjGrammar.decode x with
        | None => [PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head)]
        | Some _ => []
        end
      else []
  end.

(* IT IS THE MODEL'S LIST: the events of PjGrammar.jr_string's trace under ok (PresetReqAt.rd_hev: EAlloc n ->
   HMal (n + HEAD), EFail -> none, EFree n -> HFr (n + HEAD)), the model's HEAD being the instance's cf_head *)
Lemma prhPs_evs_model : forall x ok, cf_head = PresetReqAt.HEAD ->
  prhPs_evs x ok = PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_string x ok))).
Proof.
  intros x ok Hhd. unfold prhPs_evs, PjGrammar.jr_string.
  destruct (PjGrammar.scan x) as [q|]; [|reflexivity].
  unfold PjGrammar.jbind, PjGrammar.jalloc.
  replace (PjGrammar.take ok) with (nth 0 ok true, tl ok) by (destruct ok; reflexivity).
  destruct (nth 0 ok true); [|reflexivity].
  destruct (PjGrammar.decode x) as [sr|];
    cbn [PjGrammar.jret PjGrammar.jfree PjGrammar.jrefuse fst snd app PresetReqAt.rd_hevs flat_map PresetReqAt.rd_hev];
    rewrite Hhd, Nat2Z.inj_succ; repeat f_equal; lia.
Qed.

(* THE SUPPLY (anti-vacuity): a caller whose run premise covers jr_string's trace under its own outcomes ok, followed
   by anything, has the run premise at prhPs_evs x ok; prhPs_evs_arm turns that into the arm's list *)
Lemma prhPs_evs_supply : forall sm x0 os i x ok (t : list PjGrammar.ev), cf_head = PresetReqAt.HEAD ->
  prh_run_at sm x0 os i (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_string x ok)) ++ t)) ->
  prh_run_at sm x0 os i (prhPs_evs x ok).
Proof.
  intros sm x0 os i x ok t Hhd H. rewrite (prhPs_evs_model x ok Hhd). exact (prhReader_run_at_pre _ _ _ _ _ _ H).
Qed.

(* ... from parse_value's own list (a string value: skip x = 34 :: y, the quote; PjGrammar.jrv's string arm) ... *)
Lemma prhPs_evs_of_value : forall sm x0 os i smr d x y ok, cf_head = PresetReqAt.HEAD ->
  PjGrammar.skip x = 34 :: y ->
  prh_run_at sm x0 os i (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value smr d x ok)))) ->
  prh_run_at sm x0 os i (prhPs_evs y ok).
Proof.
  intros sm x0 os i smr d x y ok Hhd Hs H. unfold PjGrammar.jr_value in H. cbn [PjGrammar.jrv] in H.
  rewrite Hs in H. cbv beta iota in H. change (34 =? 123) with false in H. change (34 =? 91) with false in H.
  change (34 =? 34) with true in H. cbv beta iota in H.
  match type of H with
  | context [PjGrammar.jbind (PjGrammar.jr_string y) ?k ok] =>
      destruct (prhReader_jbind_pre _ _ (PjGrammar.jr_string y) k ok) as [t Ht]; rewrite Ht in H
  end.
  exact (prhPs_evs_supply _ _ _ _ _ _ _ Hhd H).
Qed.

(* ... and from parse_items' (an object's key: PjGrammar.jr_name true y with skip y = 34 :: z, the quote) *)
Lemma prhPs_evs_of_name : forall sm x0 os i y z ok, cf_head = PresetReqAt.HEAD ->
  PjGrammar.skip y = 34 :: z ->
  prh_run_at sm x0 os i (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_name true y ok)))) ->
  prh_run_at sm x0 os i (prhPs_evs z ok).
Proof.
  intros sm x0 os i y z ok Hhd Hs H. unfold PjGrammar.jr_name in H. cbv beta iota in H. rewrite Hs in H.
  cbv beta iota in H. change (34 =? 34) with true in H. cbv beta iota in H.
  match type of H with
  | context [PjGrammar.jbind (PjGrammar.jr_string z) ?k ok] =>
      destruct (prhReader_jbind_pre _ _ (PjGrammar.jr_string z) k ok) as [t Ht]; rewrite Ht in H
  end.
  exact (prhPs_evs_supply _ _ _ _ _ _ _ Hhd H).
Qed.

(* ... which IS the arm's list: the caller's outcomes ok and the arm's okA ([] / [false] / [true], the instance's)
   give the same list when they agree on the one grant, or when there is no closing quote (no call) *)
Lemma prhPs_evs_arm : forall x ok okA,
  PjGrammar.scan x = None \/ nth 0 ok true = nth 0 okA true -> prhPs_evs x ok = prhPs_evs x okA.
Proof.
  intros x ok okA [H|H]; unfold prhPs_evs; [rewrite H; reflexivity|].
  destruct (PjGrammar.scan x); [rewrite H|]; reflexivity.
Qed.

(* what the walk reads off the arm's run premise (the hypothesis of its post implication): the run's event at the
   fuzz_malloc (the run premise of fuzz_malloc's own post implication, [HMal ..] at i, by prh_run_at_one) and at the
   bad escape's fuzz_free ([HFr ..] at S i), when ok grants the malloc (S4_PsBase's ps_room_evs_mal / ps_room_evs_fr) *)
Lemma prhPs_evs_mal : forall sm x0 os i x ok Q, prh_run_at sm x0 os i (prhPs_evs x ok) ->
  PjGrammar.scan x = Some Q -> nth 0 ok true = true ->
  nth_error (PresetRun.hruns sm x0 os) i = Some (PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)).
Proof.
  intros sm x0 os i x ok Q H HS Hg. unfold prhPs_evs in H. rewrite HS, Hg in H.
  assert (E : forall a (l : list PresetReqAt.hev), a :: l = [a] ++ l) by reflexivity.
  rewrite E in H. apply prh_run_at_one. exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H)).
Qed.
Lemma prhPs_evs_fr : forall sm x0 os i x ok Q, prh_run_at sm x0 os i (prhPs_evs x ok) ->
  PjGrammar.scan x = Some Q -> nth 0 ok true = true -> PjGrammar.decode x = None ->
  nth_error (PresetRun.hruns sm x0 os) (Datatypes.S i) = Some (PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head)).
Proof.
  intros sm x0 os i x ok Q H HS Hg HD. unfold prhPs_evs in H. rewrite HS, Hg, HD in H.
  assert (E : forall a b : PresetReqAt.hev, [a; b] = [a] ++ [b]) by reflexivity.
  rewrite E in H. apply prh_run_at_one. pose proof (proj2 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H)) as H2.
  cbn [length] in H2. rewrite Nat.add_1_r in H2. exact H2.
Qed.

(* parse_string (preset_file.c:117-181), the opening quote at p: scan to the closing quote (PjGrammar.scan over the
   text after p); none: NULL with no call. Else out = fuzz_malloc (Q + 1): NULL (the chosen failure, or the allocator's
   REFUSAL) returns NULL; then decode into out (hex4, put_utf8): a bad escape frees out (fuzz_free) and returns
   NULL; else the string's bytes and a NUL in out, in->p after the closing quote, return out (plain
   parse_string_c.v:27-69; PjGrammar.decode, pj_cbytesR). Writes: q's p field (the extension, G2: FP) and
   the new block. The text is read after the fuzz_malloc call: home (G3). *)
Definition tparse_string_specX (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall most own,
  forall ly S Hp W regs mem md ch e q text len p d (tb : list Z) Lam peak cnt fail ran,
  fpre B ARx STK_parse_string ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 ->
  (* THE CURSOR CHAIN at the call state (G-Pj9; PRH_Base.v prh_s0 / prh_cur_low, the closure's clauses 4a / 4b).
     parse_string's entry state IS its caller's call state, and parse_string
     writes only q's p field, its own frame below its sp and the new block, never a word of q's chain (the gap
     bound below), so these entry-view premises hold at its fuzz_malloc (A 0x87a14) and fuzz_free (A 0x87e4c) calls:
     - the chain from s0 = prh_s0 F_parse_string q exists (its callee's afn_pre_x needs it: the S4 walk's parse_string scan);
     - its next frame word is below alloc_ceiling, so the free's trace is the pc0-filtered prh_trace pc_free_ra0 r []
       or prh_trace pc_free_ra0 r [w], w the first ra word, and the closure holds it at every w (clause 4b; the
       membership premise on w, prh_cur_ok, is REMOVED with the run-word lists);
     - the gap bound (the S4 walk's counterexample at q = sp + 8: the call view at 0x87a14 reads word (sp), then
       nfp = the saved entry ra, which nothing bounds below the stack); callers meet it (A: q >= sp + 160 from
       parse_value; q = pj_parse's sp (A) / sp + 8 (B) from deeper frames).
     REFUTED, and NOT to be re-proposed: the same facts stated at the ENTRY of parse_string's caller parse_value
     (the image-B parse_value walk's witness, image B: q = sp0 + 8 with sp0 parse_value's entry sp; the chain's next-frame slot sp0 - 8 is
     parse_value's own ra slot, written by its prologue `sd ra, 152(sp)` at B 0x86384, outside rd_fp), and the
     rd'-quantified chain over the reader's footprint (the image-B parse_items walk / the image-B parse_value walk). The callee's text states them at its own
     entry, the call state. *)
  (exists ch, achain ly (aview segs (w_H W) mem) (spZ regs - pi_frame F_parse_string) (prh_s0 F_parse_string q) ch) ->
  prh_cur_low W mem F_parse_string q ->
  (* THE CURSOR SET CW (PRH_Base.prh_cw_ok), IN THE SLOT prh_cur_ok VACATED when the run-word lists went: the trace
     this function's own free makes (A 0x87e50 / B 0x885e4) is in CW, or its word is the code word of pj_parse's
     `jal parse_value` (image A', where the trace is FIXED and costs no room). With prh_cur_low above, that trace
     is exactly [pc0; r; w]. *)
  prh_cw_ok B CW W mem F_parse_string q ->
  spZ regs + 16 <= q ->
  room_live_cf S ->
  (* THE WILD BUDGET (the room count of P''): this function's one wild site is that free, whose trace is in CW, so
     the room is stated against the SET CW with NO fresh slot. Its fuzz_malloc is a fixed-trace site (s0 = the
     cursor, and the malloc wrapper's trace is the closure's literal). *)
  YCbqGwild.wild_room (as_universe B) CW 0 (st_depot S) ->
  (* THE LIVE COUNTS AT THE INNER CALLS (the header; they replace counts_of_room_pos_rl): the secondary and class-24
     counts at every state along the ALL-GRANTED events prhPs_evs .. [] (the fuzz_malloc's state and, on a bad
     escape, the fuzz_free's), from the entry's live requests. Position-free; no cnt / fail guard *)
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (prhPs_evs (rest_atR tb text (p + 1)) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (prhPs_evs (rest_atR tb text (p + 1)) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* THE HULL BUDGET (the header): room for the all-granted events, fuzz_malloc's and the bad escape's fuzz_free *)
  PresetHullBudget.hull_budget S (prhPs_evs (rest_atR tb text (p + 1)) []) ->
  getr regs 10 = w64 q ->
  pj_in_okR segs (rdW W mem) q text len p d tb ->
  p < text + len -> nth_error tb (Z.to_nat (p - text)) = Some 34 ->
  fwin ly W regs mem e -> spZ regs <= q -> q + 24 <= spZ regs + e ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 24 ->
  src_rd W mem text tb -> prhReader_home ly S Hp Lam text len ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  cnt + 1 < 2 ^ 64 - 1 ->
  (* THE REQUEST BOUND AND THE LIVE ROOM AT EACH EVENT of parse_string's own all-granted run, prhPs_evs .. [] (the
     list the count premises above use; PRH_Base.prh_live_evs), tgrow_specX's shape (the kit owner's ruling 2026-10-30,
     completing the live-event walk's per-event restatement). The live half REPLACES the entry sum
     `blocks_bytes S + LIVE_parse_string Q <= LIVE_MAX`, which had NO SOURCE once the restatement landed: the
     caller's rd_room gives only the per-event room, and room_live_cf is the abstract class. Events: the fuzz_malloc
     of Q + 1 + cf_head bytes, then on a bad escape the fuzz_free of that block (request 0). The request half STAYS:
     fuzz_malloc's text asks `n + cf_head < cf_malloc_max` unguarded (PRH_FnAlloc.v:295), and cf_malloc_max =
     402653184 is far below LIVE_MAX = 2 ^ 34, so the live half does not give it. Callers (the image-B parse_items walk /
     the image-B parse_value walk) discharge the live half by PItems_posb.pi_evs_ok_call. *)
  (forall Q, PjGrammar.scan (rest_atR tb text (p + 1)) = Some Q -> LIVE_parse_string Q < cf_malloc_max) /\
  prh_live_evs S (prhPs_evs (rest_atR tb text (p + 1)) []) ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.11); fpostWbm is already at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_parse_string) regs mem md)
    (fpostWbm B ARx SK (YCbqGwild.wbudget CW 0) STK_parse_string e [(q, q + 8)] regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' =>
       exists res, getr regs' 10 = w64 res /\ room_live_cf S' /\
       (* THE HULL USE (the header): at most the entry budget's list *)
       PresetHullBudget.hull_used S S' (prhPs_evs (rest_atR tb text (p + 1)) []) /\
       (* the live room handed on to the caller's next call (the items-element walk's finding): the bytes this call may add to
          blocks_bytes over its granted trace, heads included (PRH_Charge.prh_held) *)
       blocks_bytes S' <= blocks_bytes S + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (rest_atR tb text (p + 1))) /\
       match PjGrammar.scan (rest_atR tb text (p + 1)) with
       | None =>
           res = 0 /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
           prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
           pj_in_okR segs (rdW W' mem') q text len p d tb /\
           (* no allocator call (outcomes []): the live requests are kept, and the position with them (E = []) *)
           Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
             (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPs_evs (rest_atR tb text (p + 1)) [])) /\
           (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
              (H0 : list Z) (hist : list YG00.chunk),
              PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
              PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p + 1)) []) ->
              exists hist', PresetRoomPos.iface_room_pos sm x os
                (i + length (prhPs_evs (rest_atR tb text (p + 1)) []))%nat H0 hist' S')
       | Some Q =>
          (* the chosen failure. ITS BYTES ARE EXACTLY KEPT (the recursive-reader author's form, the kit owner's Option 1): the top-level
             bound is over the GRANTED trace, and on this arm fuzz_malloc makes no allocator call at all, so the
             actual trace is empty and a caller re-establishing its own live room needs the equality, not the bound *)
          (cnt = fail /\ res = 0 /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
           blocks_bytes S' = blocks_bytes S /\
           prh_ledger B ly' S' Hp' W' mem' Lam peak (cnt + 1) SIZE_MAXZ ran most own /\
           pj_in_okR segs (rdW W' mem') q text len p d tb /\
           (* fuzz_malloc's NULL (outcomes [false]): no event, E = [], the position kept *)
           Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
             (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPs_evs (rest_atR tb text (p + 1)) [false])) /\
           (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
              (H0 : list Z) (hist : list YG00.chunk),
              PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
              PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p + 1)) [false]) ->
              exists hist', PresetRoomPos.iface_room_pos sm x os
                (i + length (prhPs_evs (rest_atR tb text (p + 1)) [false]))%nat H0 hist' S'))
          \/
          (* the allocator's refusal: a refused malloc_cf leaves the blocks unchanged, so the same equality holds *)
          (cnt <> fail /\ res = 0 /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
           blocks_bytes S' = blocks_bytes S /\
           (exists regsc memc mdc Wc cc,
              YG0dcf.malloc_cf_null_post segs B ly S Hp W regsc memc mdc (Z.of_nat Q + 1 + cf_head) (PNull, S') Wc cc) /\
           rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\
           (* THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS), as this REFUSED arm's exclusion: no
              model run and position whose next events are the ALL-GRANTED ones (prhPs_evs .. []), its malloc a
              CONSUMER event, meets this arm - P8 and the engine's grant exclude the NULL there *)
           (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
              (H0 : list Z) (hist : list YG00.chunk),
              PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
              PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p + 1)) []) ->
              PRH_Base.prh_cons_from sm x os i (length (prhPs_evs (rest_atR tb text (p + 1)) [])) -> False) /\
           (* THE LEDGER IS fuzz_malloc's REFUSAL ARM VERBATIM (PRH_FnAlloc.v prh_alloc_post arm 2 at
              n = Z.of_nat Q + 1; the kit owner's ruling, 2026-10-29 ~19:4xZ). COUNTEREXAMPLE to the old
              `Lam peak (cnt + 1) fail 1 most own`: Lam = [], peak = 0, the string ab (Q = 2, n = 3), cnt <> fail, the
              malloc refused: g_peak = 3, not 0; with most = 2 and ran = 0, g_ran_out stays 0, not 1. *)
           prh_ledger B ly' S' Hp' W' mem' Lam (Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam + (Z.of_nat Q + 1))))
             ((cnt + 1) mod 2 ^ 64) fail (if Z.of_nat Q + 1 <=? most then 1 else ran) most own /\
           pj_in_okR segs (rdW W' mem') q text len p d tb /\
           (* the refused malloc (outcomes [false]): no event, E = [], the position kept *)
           Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
             (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPs_evs (rest_atR tb text (p + 1)) [false])) /\
           (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
              (H0 : list Z) (hist : list YG00.chunk),
              PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
              PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p + 1)) [false]) ->
              exists hist', PresetRoomPos.iface_room_pos sm x os
                (i + length (prhPs_evs (rest_atR tb text (p + 1)) [false]))%nat H0 hist' S'))
           \/
           (* a bad escape: out taken and given back *)
           (cnt <> fail /\ res = 0 /\ PjGrammar.decode (rest_atR tb text (p + 1)) = None /\
            Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
            prh_ledger B ly' S' Hp' W' mem' Lam (Z.max peak (Ledger.lsum Lam + (Z.of_nat Q + 1))) (cnt + 1) fail ran most own /\
            pj_in_okR segs (rdW W' mem') q text len p d tb /\
            (* THE EXACT ADVANCE (outcomes [true]): E = the malloc's event and the free's, [HMal ..; HFr ..] *)
            Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
              (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPs_evs (rest_atR tb text (p + 1)) [true])) /\
            (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
               (H0 : list Z) (hist : list YG00.chunk),
               PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
               PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p + 1)) [true]) ->
               exists hist', PresetRoomPos.iface_room_pos sm x os
                 (i + length (prhPs_evs (rest_atR tb text (p + 1)) [true]))%nat H0 hist' S'))
           \/
           (* the string, in a new harness block of Q + 1 bytes *)
           (cnt <> fail /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\
            exists s r, PjGrammar.decode (rest_atR tb text (p + 1)) = Some (s, r) /\
            Hp' = (res - cf_head) :: Hp /\
            ablocks B ly' S' = ablocks B ly S ++ [(res - cf_head, Z.of_nat Q + 1 + cf_head)] /\
            prhReader_vis W' mem' res (Z.of_nat Q + 1) /\
            pj_cbytesR segs (rdW W' mem') res s /\
            prh_ledger B ly' S' Hp' W' mem' ((res, Z.of_nat Q + 1) :: Lam)
              (Z.max peak (Ledger.lsum Lam + (Z.of_nat Q + 1))) (cnt + 1) fail ran most own /\
            pj_in_okR segs (rdW W' mem') q text len (p + Z.of_nat Q + 2) d tb /\
            (* THE EXACT ADVANCE (outcomes [true]): E = the malloc's event, [HMal ..] *)
            Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
              (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPs_evs (rest_atR tb text (p + 1)) [true])) /\
            (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
               (H0 : list Z) (hist : list YG00.chunk),
               PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
               PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p + 1)) [true]) ->
               exists hist', PresetRoomPos.iface_room_pos sm x os
                 (i + length (prhPs_evs (rest_atR tb text (p + 1)) [true]))%nat H0 hist' S'))
       end)).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tparse_string_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. tpstP_Q IS the text's post (tpstP_Q_check fails to build if
   the two ever differ); tpstP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition tpstP_ANone (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb : list Z) (Lam
    : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word
    -> option byte) (res : Z) : Prop :=
  res = 0 /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran
      most own /\ pj_in_okR segs (rdW W' mem') q text len p d tb /\ Permutation (PresetRoom.rs_live
      (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPs_evs
      (rest_atR tb text (p + 1)) [])) /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option
      nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0
      hist S -> PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p + 1)) []) -> exists hist',
      PresetRoomPos.iface_room_pos sm x os (i + length (prhPs_evs (rest_atR tb text (p + 1)) []))%nat H0 hist' S').

Definition tpstP_ASome1 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb : list Z)
    (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' :
    word -> option byte) (res : Z) : Prop :=
  cnt = fail /\ res = 0 /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\ blocks_bytes S' = blocks_bytes S /\
      prh_ledger B ly' S' Hp' W' mem' Lam peak (cnt + 1) SIZE_MAXZ ran most own /\ pj_in_okR segs (rdW W' mem') q text
      len p d tb /\ Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from
      (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPs_evs (rest_atR tb text (p + 1)) [false])) /\ (forall (sm :
      list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist :
      list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (prhPs_evs
      (rest_atR tb text (p + 1)) [false]) -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPs_evs
      (rest_atR tb text (p + 1)) [false]))%nat H0 hist' S').

Definition tpstP_ASome2 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (q text len p d : Z)
    (tb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world
    segs) (mem' : word -> option byte) (res : Z) (Q : nat) : Prop :=
  cnt <> fail /\ res = 0 /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\ blocks_bytes S' = blocks_bytes S /\
      (exists regsc memc mdc Wc cc, YG0dcf.malloc_cf_null_post segs B ly S Hp W regsc memc mdc (Z.of_nat Q + 1 +
      cf_head) (PNull, S') Wc cc) /\ rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ (forall (sm : list Z -> Z * Z)
      (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
      PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p
      + 1)) []) -> PRH_Base.prh_cons_from sm x os i (length (prhPs_evs (rest_atR tb text (p + 1)) [])) -> False) /\
      prh_ledger B ly' S' Hp' W' mem' Lam (Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam + (Z.of_nat Q + 1)))) ((cnt +
      1) mod 2 ^ 64) fail (if Z.of_nat Q + 1 <=? most then 1 else ran) most own /\ pj_in_okR segs (rdW W' mem') q text
      len p d tb /\ Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from
      (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPs_evs (rest_atR tb text (p + 1)) [false])) /\ (forall (sm :
      list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist :
      list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (prhPs_evs
      (rest_atR tb text (p + 1)) [false]) -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPs_evs
      (rest_atR tb text (p + 1)) [false]))%nat H0 hist' S').

Definition tpstP_ASome3 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb : list Z)
    (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' :
    word -> option byte) (res : Z) (Q : nat) : Prop :=
  cnt <> fail /\ res = 0 /\ PjGrammar.decode (rest_atR tb text (p + 1)) = None /\ Hp' = Hp /\ ablocks B ly' S' =
      ablocks B ly S /\ prh_ledger B ly' S' Hp' W' mem' Lam (Z.max peak (Ledger.lsum Lam + (Z.of_nat Q + 1))) (cnt + 1)
      fail ran most own /\ pj_in_okR segs (rdW W' mem') q text len p d tb /\ Permutation (PresetRoom.rs_live
      (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPs_evs
      (rest_atR tb text (p + 1)) [true])) /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat *
      option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os
      i H0 hist S -> PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p + 1)) [true]) -> exists hist',
      PresetRoomPos.iface_room_pos sm x os (i + length (prhPs_evs (rest_atR tb text (p + 1)) [true]))%nat H0 hist' S').

Definition tpstP_ASome4 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb : list Z)
    (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' :
    word -> option byte) (res : Z) (Q : nat) : Prop :=
  cnt <> fail /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\ exists s r, PjGrammar.decode (rest_atR tb text (p + 1)) =
      Some (s, r) /\ Hp' = (res - cf_head) :: Hp /\ ablocks B ly' S' = ablocks B ly S ++ [(res - cf_head, Z.of_nat Q +
      1 + cf_head)] /\ prhReader_vis W' mem' res (Z.of_nat Q + 1) /\ pj_cbytesR segs (rdW W' mem') res s /\ prh_ledger
      B ly' S' Hp' W' mem' ((res, Z.of_nat Q + 1) :: Lam) (Z.max peak (Ledger.lsum Lam + (Z.of_nat Q + 1))) (cnt + 1)
      fail ran most own /\ pj_in_okR segs (rdW W' mem') q text len (p + Z.of_nat Q + 2) d tb /\ Permutation
      (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf
      S)) (prhPs_evs (rest_atR tb text (p + 1)) [true])) /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os : list
      (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
      PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p
      + 1)) [true]) -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPs_evs (rest_atR tb text (p +
      1)) [true]))%nat H0 hist' S').

Definition tpstP_Q (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (q text len p d : Z) (tb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  exists res, getr regs' 10 = w64 res /\ room_live_cf S' /\ PresetHullBudget.hull_used S S' (prhPs_evs (rest_atR tb
      text (p + 1)) []) /\ blocks_bytes S' <= blocks_bytes S + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (rest_atR
      tb text (p + 1))) /\ match PjGrammar.scan (rest_atR tb text (p + 1)) with | None => tpstP_ANone most own ly S Hp
      q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res | Some Q => tpstP_ASome1 most own ly S Hp q text
      len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res \/ tpstP_ASome2 most own ly S Hp W q text len p d tb Lam
      peak cnt fail ran ly' S' Hp' W' mem' res Q \/ tpstP_ASome3 most own ly S Hp q text len p d tb Lam peak cnt fail
      ran ly' S' Hp' W' mem' res Q \/ tpstP_ASome4 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp'
      W' mem' res Q end.

Lemma tpstP_Q_check : forall (CTX0 CW : list (list Z)), tparse_string_specX CTX0 CW -> tparse_string_specX CTX0 CW.
Proof.
  intros CTX0 CW H. unfold tparse_string_specX in *.
  intros most own ly S Hp W regs mem md ch e q text len p d tb Lam peak cnt fail ran HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7
      HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (tpstP_Q most own ly S Hp W q text
      len p d tb Lam peak cnt fail ran) end.
  exact (H most own ly S Hp W regs mem md ch e q text len p d tb Lam peak cnt fail ran HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7
      HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23).
Qed.

Record tpstP_R (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (q text len p d : Z) (tb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (res : Z) : Prop := {
  tpstP_ret : getr regs' 10 = w64 res;
  tpstP_room : room_live_cf S';
  tpstP_hull : PresetHullBudget.hull_used S S' (prhPs_evs (rest_atR tb text (p + 1)) []);
  tpstP_bytes_le : blocks_bytes S' <= blocks_bytes S + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (rest_atR tb text
      (p + 1)));
  tpstP_arm : match PjGrammar.scan (rest_atR tb text (p + 1)) with | None => tpstP_ANone most own ly S Hp q text len p
      d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res | Some Q => tpstP_ASome1 most own ly S Hp q text len p d tb Lam
      peak cnt fail ran ly' S' Hp' W' mem' res \/ tpstP_ASome2 most own ly S Hp W q text len p d tb Lam peak cnt fail
      ran ly' S' Hp' W' mem' res Q \/ tpstP_ASome3 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp'
      W' mem' res Q \/ tpstP_ASome4 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q
      end }.

Lemma tpstP_R_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (q text len p d :
    Z) (tb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  tpstP_Q most own ly S Hp W q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' ->
  exists res, tpstP_R most own ly S Hp W q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' res.
Proof.
  intros most own ly S Hp W q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' H. destruct H as (res
      & H0 & H1 & H2 & H3 & H4).
  exists res.
  exact {| tpstP_ret := H0; tpstP_room := H1; tpstP_hull := H2; tpstP_bytes_le := H3; tpstP_arm := H4 |}.
Qed.

Lemma tpstP_Q_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (q text len p d :
    Z) (tb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (res : Z),
  tpstP_R most own ly S Hp W q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' res ->
  tpstP_Q most own ly S Hp W q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md'.
Proof.
  intros most own ly S Hp W q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' res HR.
  exists res.
  exact (conj (tpstP_ret HR) (conj (tpstP_room HR) (conj (tpstP_hull HR) (conj (tpstP_bytes_le HR) (tpstP_arm HR))))).
Qed.

Record tpstP_RNone (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb : list Z) (Lam :
    list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word
    -> option byte) (res : Z) : Prop := {
  tpstPn_res0 : res = 0;
  tpstPn_hp : Hp' = Hp;
  tpstPn_ablocks : ablocks B ly' S' = ablocks B ly S;
  tpstPn_ledger : prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own;
  tpstPn_in_ok : pj_in_okR segs (rdW W' mem') q text len p d tb;
  tpstPn_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
      (YGcfRoom.room_of_cf S)) (prhPs_evs (rest_atR tb text (p + 1)) []));
  tpstPn_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
      (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at
      sm x os i (prhPs_evs (rest_atR tb text (p + 1)) []) -> exists hist', PresetRoomPos.iface_room_pos sm x os (i +
      length (prhPs_evs (rest_atR tb text (p + 1)) []))%nat H0 hist' S') }.

Lemma tpstP_RNone_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb : list
    Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (mem' : word -> option byte) (res : Z),
  tpstP_ANone most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res ->
  tpstP_RNone most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res.
Proof.
  intros most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res H. destruct H as (H0 & H1 & H2
      & H3 & H4 & H5 & H6).
  exact {| tpstPn_res0 := H0; tpstPn_hp := H1; tpstPn_ablocks := H2; tpstPn_ledger := H3; tpstPn_in_ok := H4;
      tpstPn_live := H5; tpstPn_pos := H6 |}.
Qed.

Lemma tpstP_ANone_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (mem' : word -> option byte) (res : Z),
  tpstP_RNone most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res ->
  tpstP_ANone most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res.
Proof.
  intros most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res HR.
  exact (conj (tpstPn_res0 HR) (conj (tpstPn_hp HR) (conj (tpstPn_ablocks HR) (conj (tpstPn_ledger HR) (conj
      (tpstPn_in_ok HR) (conj (tpstPn_live HR) (tpstPn_pos HR))))))).
Qed.

Record tpstP_RSome1 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb : list Z) (Lam :
    list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word
    -> option byte) (res : Z) : Prop := {
  tpstPs1_chosen : cnt = fail;
  tpstPs1_res0 : res = 0;
  tpstPs1_hp : Hp' = Hp;
  tpstPs1_ablocks : ablocks B ly' S' = ablocks B ly S;
  tpstPs1_bytes : blocks_bytes S' = blocks_bytes S;
  tpstPs1_ledger : prh_ledger B ly' S' Hp' W' mem' Lam peak (cnt + 1) SIZE_MAXZ ran most own;
  tpstPs1_in_ok : pj_in_okR segs (rdW W' mem') q text len p d tb;
  tpstPs1_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
      (YGcfRoom.room_of_cf S)) (prhPs_evs (rest_atR tb text (p + 1)) [false]));
  tpstPs1_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
      nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
      PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p + 1)) [false]) -> exists hist',
      PresetRoomPos.iface_room_pos sm x os (i + length (prhPs_evs (rest_atR tb text (p + 1)) [false]))%nat H0 hist' S')
      }.

Lemma tpstP_RSome1_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb : list
    Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (mem' : word -> option byte) (res : Z),
  tpstP_ASome1 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res ->
  tpstP_RSome1 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res.
Proof.
  intros most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res H. destruct H as (H0 & H1 & H2
      & H3 & H4 & H5 & H6 & H7 & H8).
  exact {| tpstPs1_chosen := H0; tpstPs1_res0 := H1; tpstPs1_hp := H2; tpstPs1_ablocks := H3; tpstPs1_bytes := H4;
      tpstPs1_ledger := H5; tpstPs1_in_ok := H6; tpstPs1_live := H7; tpstPs1_pos := H8 |}.
Qed.

Lemma tpstP_ASome1_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (mem' : word -> option byte) (res : Z),
  tpstP_RSome1 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res ->
  tpstP_ASome1 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res.
Proof.
  intros most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res HR.
  exact (conj (tpstPs1_chosen HR) (conj (tpstPs1_res0 HR) (conj (tpstPs1_hp HR) (conj (tpstPs1_ablocks HR) (conj
      (tpstPs1_bytes HR) (conj (tpstPs1_ledger HR) (conj (tpstPs1_in_ok HR) (conj (tpstPs1_live HR) (tpstPs1_pos
      HR))))))))).
Qed.

Record tpstP_RSome2 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (q text len p d : Z) (tb
    : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world
    segs) (mem' : word -> option byte) (res : Z) (Q : nat) : Prop := {
  tpstPs2_notchosen : cnt <> fail;
  tpstPs2_res0 : res = 0;
  tpstPs2_hp : Hp' = Hp;
  tpstPs2_ablocks : ablocks B ly' S' = ablocks B ly S;
  tpstPs2_bytes : blocks_bytes S' = blocks_bytes S;
  tpstPs2_evidence : (exists regsc memc mdc Wc cc, YG0dcf.malloc_cf_null_post segs B ly S Hp W regsc memc mdc (Z.of_nat
      Q + 1 + cf_head) (PNull, S') Wc cc);
  tpstPs2_errno : rd32 (aview segs (w_H W') mem') (as_errno B) 12;
  tpstPs2_outcome : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
      nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
      PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p + 1)) []) -> PRH_Base.prh_cons_from sm x os i
      (length (prhPs_evs (rest_atR tb text (p + 1)) [])) -> False);
  tpstPs2_ledger : prh_ledger B ly' S' Hp' W' mem' Lam (Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam + (Z.of_nat Q +
      1)))) ((cnt + 1) mod 2 ^ 64) fail (if Z.of_nat Q + 1 <=? most then 1 else ran) most own;
  tpstPs2_in_ok : pj_in_okR segs (rdW W' mem') q text len p d tb;
  tpstPs2_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
      (YGcfRoom.room_of_cf S)) (prhPs_evs (rest_atR tb text (p + 1)) [false]));
  tpstPs2_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
      nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
      PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p + 1)) [false]) -> exists hist',
      PresetRoomPos.iface_room_pos sm x os (i + length (prhPs_evs (rest_atR tb text (p + 1)) [false]))%nat H0 hist' S')
      }.

Lemma tpstP_RSome2_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (q text len p
    d : Z) (tb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W'
    : world segs) (mem' : word -> option byte) (res : Z) (Q : nat),
  tpstP_ASome2 most own ly S Hp W q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q ->
  tpstP_RSome2 most own ly S Hp W q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q.
Proof.
  intros most own ly S Hp W q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q H. destruct H as (H0 & H1
      & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  exact {| tpstPs2_notchosen := H0; tpstPs2_res0 := H1; tpstPs2_hp := H2; tpstPs2_ablocks := H3; tpstPs2_bytes := H4;
      tpstPs2_evidence := H5; tpstPs2_errno := H6; tpstPs2_outcome := H7; tpstPs2_ledger := H8; tpstPs2_in_ok := H9;
      tpstPs2_live := H10; tpstPs2_pos := H11 |}.
Qed.

Lemma tpstP_ASome2_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (q text len
    p d : Z) (tb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z)
    (W' : world segs) (mem' : word -> option byte) (res : Z) (Q : nat),
  tpstP_RSome2 most own ly S Hp W q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q ->
  tpstP_ASome2 most own ly S Hp W q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q.
Proof.
  intros most own ly S Hp W q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q HR.
  exact (conj (tpstPs2_notchosen HR) (conj (tpstPs2_res0 HR) (conj (tpstPs2_hp HR) (conj (tpstPs2_ablocks HR) (conj
      (tpstPs2_bytes HR) (conj (tpstPs2_evidence HR) (conj (tpstPs2_errno HR) (conj (tpstPs2_outcome HR) (conj
      (tpstPs2_ledger HR) (conj (tpstPs2_in_ok HR) (conj (tpstPs2_live HR) (tpstPs2_pos HR)))))))))))).
Qed.

Record tpstP_RSome3 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb : list Z) (Lam :
    list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word
    -> option byte) (res : Z) (Q : nat) : Prop := {
  tpstPs3_notchosen : cnt <> fail;
  tpstPs3_res0 : res = 0;
  tpstPs3_bad : PjGrammar.decode (rest_atR tb text (p + 1)) = None;
  tpstPs3_hp : Hp' = Hp;
  tpstPs3_ablocks : ablocks B ly' S' = ablocks B ly S;
  tpstPs3_ledger : prh_ledger B ly' S' Hp' W' mem' Lam (Z.max peak (Ledger.lsum Lam + (Z.of_nat Q + 1))) (cnt + 1) fail
      ran most own;
  tpstPs3_in_ok : pj_in_okR segs (rdW W' mem') q text len p d tb;
  tpstPs3_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
      (YGcfRoom.room_of_cf S)) (prhPs_evs (rest_atR tb text (p + 1)) [true]));
  tpstPs3_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
      nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
      PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p + 1)) [true]) -> exists hist',
      PresetRoomPos.iface_room_pos sm x os (i + length (prhPs_evs (rest_atR tb text (p + 1)) [true]))%nat H0 hist' S')
      }.

Lemma tpstP_RSome3_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb : list
    Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (mem' : word -> option byte) (res : Z) (Q : nat),
  tpstP_ASome3 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q ->
  tpstP_RSome3 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q.
Proof.
  intros most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q H. destruct H as (H0 & H1 &
      H2 & H3 & H4 & H5 & H6 & H7 & H8).
  exact {| tpstPs3_notchosen := H0; tpstPs3_res0 := H1; tpstPs3_bad := H2; tpstPs3_hp := H3; tpstPs3_ablocks := H4;
      tpstPs3_ledger := H5; tpstPs3_in_ok := H6; tpstPs3_live := H7; tpstPs3_pos := H8 |}.
Qed.

Lemma tpstP_ASome3_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (mem' : word -> option byte) (res : Z) (Q : nat),
  tpstP_RSome3 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q ->
  tpstP_ASome3 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q.
Proof.
  intros most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q HR.
  exact (conj (tpstPs3_notchosen HR) (conj (tpstPs3_res0 HR) (conj (tpstPs3_bad HR) (conj (tpstPs3_hp HR) (conj
      (tpstPs3_ablocks HR) (conj (tpstPs3_ledger HR) (conj (tpstPs3_in_ok HR) (conj (tpstPs3_live HR) (tpstPs3_pos
      HR))))))))).
Qed.

Record tpstP_RSome4 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb : list Z) (Lam :
    list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word
    -> option byte) (res : Z) (Q : nat) (s r : list Z) : Prop := {
  tpstPs4_notchosen : cnt <> fail;
  tpstPs4_res_min : 4096 + cf_head <= res;
  tpstPs4_res_align : res mod 16 = 0;
  tpstPs4_decode : PjGrammar.decode (rest_atR tb text (p + 1)) = Some (s, r);
  tpstPs4_hp : Hp' = (res - cf_head) :: Hp;
  tpstPs4_ablocks : ablocks B ly' S' = ablocks B ly S ++ [(res - cf_head, Z.of_nat Q + 1 + cf_head)];
  tpstPs4_vis : prhReader_vis W' mem' res (Z.of_nat Q + 1);
  tpstPs4_cbytes : pj_cbytesR segs (rdW W' mem') res s;
  tpstPs4_ledger : prh_ledger B ly' S' Hp' W' mem' ((res, Z.of_nat Q + 1) :: Lam) (Z.max peak (Ledger.lsum Lam +
      (Z.of_nat Q + 1))) (cnt + 1) fail ran most own;
  tpstPs4_in_ok : pj_in_okR segs (rdW W' mem') q text len (p + Z.of_nat Q + 2) d tb;
  tpstPs4_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
      (YGcfRoom.room_of_cf S)) (prhPs_evs (rest_atR tb text (p + 1)) [true]));
  tpstPs4_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
      nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
      PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p + 1)) [true]) -> exists hist',
      PresetRoomPos.iface_room_pos sm x os (i + length (prhPs_evs (rest_atR tb text (p + 1)) [true]))%nat H0 hist' S')
      }.

Lemma tpstP_RSome4_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb : list
    Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (mem' : word -> option byte) (res : Z) (Q : nat),
  tpstP_ASome4 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q ->
  exists s r, tpstP_RSome4 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q s r.
Proof.
  intros most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q H. destruct H as (H0 & H1 &
      H2 & s & r & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  exists s, r.
  exact {| tpstPs4_notchosen := H0; tpstPs4_res_min := H1; tpstPs4_res_align := H2; tpstPs4_decode := H3; tpstPs4_hp :=
      H4; tpstPs4_ablocks := H5; tpstPs4_vis := H6; tpstPs4_cbytes := H7; tpstPs4_ledger := H8; tpstPs4_in_ok := H9;
      tpstPs4_live := H10; tpstPs4_pos := H11 |}.
Qed.

Lemma tpstP_ASome4_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (q text len p d : Z) (tb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (mem' : word -> option byte) (res : Z) (Q : nat) (s r : list Z),
  tpstP_RSome4 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q s r ->
  tpstP_ASome4 most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q.
Proof.
  intros most own ly S Hp q text len p d tb Lam peak cnt fail ran ly' S' Hp' W' mem' res Q s r HR.
  refine (conj (tpstPs4_notchosen HR) (conj (tpstPs4_res_min HR) (conj (tpstPs4_res_align HR) _))).
  exists s, r.
  exact (conj (tpstPs4_decode HR) (conj (tpstPs4_hp HR) (conj (tpstPs4_ablocks HR) (conj (tpstPs4_vis HR) (conj
      (tpstPs4_cbytes HR) (conj (tpstPs4_ledger HR) (conj (tpstPs4_in_ok HR) (conj (tpstPs4_live HR) (tpstPs4_pos
      HR))))))))).
Qed.

Local Unset Implicit Arguments.

(* the two requests of grow's step: the kids realloc's new block with its head, and for an object (ty = 6) the keys
   realloc's (plain grow_c.v:46-48: rf_room for 56 * cap2 cap + 16, then for 8 * cap2 cap + 16 after the first; an
   array makes only the first, PjGrammar.v:225-226). The items-element walk's form, verbatim. PRH_FnPj.LIVE_pj_set's budget
   uses it; tgrow_specX's own live room is per event since 2026-10-30 (its note) *)
Definition LIVE_grow (ty cap : Z) : Z := 56 * cap2R cap + cf_head + (if ty =? 6 then 8 * cap2R cap + cf_head else 0).

(* grow's events (PjGrammar.grow o n cap under the outcome list ok, F1): none when n < cap; else the kids realloc's
   when ok grants it, then for an object the keys realloc's when ok grants that too; a refused grant makes no event
   and ends the function ([] grants every call). One realloc of an array of k-byte slots from cap to cap2R cap: a
   cap-0 node's array is NULL, so fuzz_realloc (NULL, ..) is a malloc (the model's EGrow 0 _, PresetReqAt.rd_hev).
   THE CHOSEN-FAILURE SKIP (the kit owner's item): tgrow_specX's arm `cnt = fail` (the kids realloc is the chosen
   failure) has outcomes [false], so E = []; its arm `cnt + 1 = fail` (the keys realloc is) has [true; false], so
   E = [the kids realloc's event] *)
Definition prhPg_ev (k cap : Z) : PresetReqAt.hev :=
  if cap =? 0 then PresetReqAt.HMal (k * cap2R cap + cf_head)
  else PresetReqAt.HRe (k * cap + cf_head) (k * cap2R cap + cf_head).
Definition prhPg_evs (o : bool) (n cap : Z) (ok : list bool) : list PresetReqAt.hev :=
  if n <? cap then []
  else if nth 0 ok true then prhPg_ev 56 cap :: (if o && nth 1 ok true then [prhPg_ev 8 cap] else [])
  else [].

(* one realloc's event is the model's *)
Lemma prhPg_ev_model : forall k c : nat, (0 < k)%nat -> cf_head = PresetReqAt.HEAD ->
  PresetReqAt.rd_hev (PjGrammar.EGrow (k * c)%nat (k * (if Nat.eqb c 0 then 8 else 2 * c))%nat) =
  [prhPg_ev (Z.of_nat k) (Z.of_nat c)].
Proof.
  intros k c Hk Hhd. unfold prhPg_ev, cap2R. rewrite Hhd. destruct c as [|c].
  - rewrite Nat.mul_0_r. cbn [Nat.eqb PresetReqAt.rd_hev Z.of_nat Z.eqb]. rewrite Nat2Z.inj_mul. reflexivity.
  - assert (Hp : (0 < k * Datatypes.S c)%nat) by (apply Nat.mul_pos_pos; lia).
    cbn [Nat.eqb]. destruct (k * Datatypes.S c)%nat as [|m] eqn:Em; [lia|].
    cbn [PresetReqAt.rd_hev]. rewrite <- Em.
    replace (Z.of_nat (Datatypes.S c) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite !Nat2Z.inj_mul. reflexivity.
Qed.

(* IT IS THE MODEL'S LIST: the events of PjGrammar.grow's trace under ok, the model's HEAD being cf_head *)
Lemma prhPg_evs_model : forall o n cap ok, 0 <= n -> 0 <= cap -> cf_head = PresetReqAt.HEAD ->
  prhPg_evs o n cap ok = PresetReqAt.rd_hevs (snd (fst (PjGrammar.grow o (Z.to_nat n) (Z.to_nat cap) ok))).
Proof.
  intros o n cap ok Hn Hc Hhd. unfold prhPg_evs, PjGrammar.grow.
  destruct (Z.ltb_spec n cap) as [Hlt|Hge].
  - replace (Nat.ltb (Z.to_nat n) (Z.to_nat cap)) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
  - replace (Nat.ltb (Z.to_nat n) (Z.to_nat cap)) with false by (symmetry; apply Nat.ltb_ge; lia).
    remember (Z.to_nat cap) as c eqn:Ec. assert (Ecap : cap = Z.of_nat c) by lia. subst cap. clear Ec Hc Hge.
    unfold PjGrammar.jbind, PjGrammar.jrealloc.
    replace (PjGrammar.take ok) with (nth 0 ok true, tl ok) by (destruct ok; reflexivity).
    destruct (nth 0 ok true); [|reflexivity].
    destruct o; cbv beta iota zeta;
      [replace (PjGrammar.take (tl ok)) with (nth 1 ok true, tl (tl ok)) by (destruct ok as [|? [|? ?]]; reflexivity);
       destruct (nth 1 ok true)|];
      cbn [fst snd app andb PjGrammar.jret PresetReqAt.rd_hevs flat_map];
      rewrite ?app_nil_r, !prhPg_ev_model by first [lia | exact Hhd]; reflexivity.
Qed.

(* THE SUPPLY (anti-vacuity): a caller whose run premise covers grow's trace under its own outcomes ok, followed by
   anything, has the run premise at prhPg_evs o n cap ok; prhPg_evs_arm turns that into the arm's list ... *)
Lemma prhPg_evs_supply : forall sm x0 os i o n cap ok (t : list PjGrammar.ev),
  0 <= n -> 0 <= cap -> cf_head = PresetReqAt.HEAD ->
  prh_run_at sm x0 os i (PresetReqAt.rd_hevs (snd (fst (PjGrammar.grow o (Z.to_nat n) (Z.to_nat cap) ok)) ++ t)) ->
  prh_run_at sm x0 os i (prhPg_evs o n cap ok).
Proof.
  intros sm x0 os i o n cap ok t Hn Hc Hhd H. rewrite (prhPg_evs_model o n cap ok Hn Hc Hhd).
  exact (prhReader_run_at_pre _ _ _ _ _ _ H).
Qed.

(* ... in particular parse_items' own list: each turn of its member loop (PjGrammar.jrl) starts with grow *)
Lemma prhPg_evs_of_items : forall sm x0 os i smr f d o n cap acc y ok,
  0 <= n -> 0 <= cap -> cf_head = PresetReqAt.HEAD ->
  prh_run_at sm x0 os i
    (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jrl smr (Datatypes.S f) d o (Z.to_nat n) (Z.to_nat cap) acc y ok)))) ->
  prh_run_at sm x0 os i (prhPg_evs o n cap ok).
Proof.
  intros sm x0 os i smr f d o n cap acc y ok Hn Hc Hhd H. cbn [PjGrammar.jrl] in H.
  match type of H with
  | context [PjGrammar.jbind (PjGrammar.grow o (Z.to_nat n) (Z.to_nat cap)) ?k ok] =>
      destruct (prhReader_jbind_pre _ _ (PjGrammar.grow o (Z.to_nat n) (Z.to_nat cap)) k ok) as [t Ht];
      rewrite Ht in H
  end.
  exact (prhPg_evs_supply _ _ _ _ _ _ _ _ _ Hn Hc Hhd H).
Qed.

(* ... which IS the arm's list: the caller's outcomes ok and the arm's okA (the instance's: [], [false], [true],
   [true; false], [true; true]) give the same list when n < cap (no call), or when they agree on the kids grant and,
   for an object whose kids realloc was granted, on the keys grant *)
Lemma prhPg_evs_arm : forall o n cap ok okA,
  n < cap \/ (nth 0 ok true = nth 0 okA true /\ (nth 0 ok true = true -> o = true -> nth 1 ok true = nth 1 okA true)) ->
  prhPg_evs o n cap ok = prhPg_evs o n cap okA.
Proof.
  intros o n cap ok okA [Hlt | [H0 H1]]; unfold prhPg_evs.
  - replace (n <? cap) with true by (symmetry; apply Z.ltb_lt; exact Hlt). reflexivity.
  - destruct (n <? cap); [reflexivity|]. rewrite <- H0. destruct (nth 0 ok true) eqn:E0; [|reflexivity].
    destruct o; cbn [andb]; [rewrite (H1 eq_refl eq_refl)|]; reflexivity.
Qed.

(* what the walk reads off the arm's run premise (the hypothesis of its post implication): the run's event at the
   kids realloc (at i) and at an object's keys realloc (at S i), when ok grants them: the run premises of
   fuzz_realloc's own post implications ([HRe ..] or, from a NULL array, [HMal ..]), by prh_run_at_one *)
Lemma prhPg_evs_kids : forall sm x0 os i o n cap ok, prh_run_at sm x0 os i (prhPg_evs o n cap ok) ->
  cap <= n -> nth 0 ok true = true -> nth_error (PresetRun.hruns sm x0 os) i = Some (prhPg_ev 56 cap).
Proof.
  intros sm x0 os i o n cap ok H Hle Hg. unfold prhPg_evs in H.
  replace (n <? cap) with false in H by (symmetry; apply Z.ltb_ge; lia). rewrite Hg in H.
  assert (E : forall a (l : list PresetReqAt.hev), a :: l = [a] ++ l) by reflexivity.
  rewrite E in H. apply prh_run_at_one. exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H)).
Qed.
Lemma prhPg_evs_keys : forall sm x0 os i n cap ok, prh_run_at sm x0 os i (prhPg_evs true n cap ok) ->
  cap <= n -> nth 0 ok true = true -> nth 1 ok true = true ->
  nth_error (PresetRun.hruns sm x0 os) (Datatypes.S i) = Some (prhPg_ev 8 cap).
Proof.
  intros sm x0 os i n cap ok H Hle Hg Hg1. unfold prhPg_evs in H.
  replace (n <? cap) with false in H by (symmetry; apply Z.ltb_ge; lia). rewrite Hg, Hg1 in H. cbn [andb] in H.
  assert (E : forall a b : PresetReqAt.hev, [a; b] = [a] ++ [b]) by reflexivity.
  rewrite E in H. apply prh_run_at_one. pose proof (proj2 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H)) as H2.
  cbn [length] in H2. rewrite Nat.add_1_r in H2. exact H2.
Qed.

(* grow (preset_file.c:42-64): n < cap returns 0. Else cap' = cap ? 2 cap : 8 (cap2R); kids =
   fuzz_realloc (v->kids, 56 cap'): NULL returns -1; v->kids = kids; for an object keys = fuzz_realloc (v->keys,
   8 cap'): NULL returns -1 (v->kids already moved, v->cap not); v->keys = keys; v->cap = cap'; return 0 (plain
   grow_c.v:34-90, its five arms, plus the two REFUSAL arms). kb / yb are the old kids / keys bytes (every slot is in
   use when n = cap); a moved array keeps them at its start (tfuzz_realloc_specX's firstn (min k n)). Writes: v's kids,
   keys and cap fields (v is the node, prhReader_at), the old blocks (freed by a successful realloc): FP.
   B's UBSan checks (v 8-aligned and non-null) hold under the premises. 
   THE FORM ALREADY MEETS THE INVARIANT (the head-size census walker's arm-by-arm check on 9d33e3996f3a; the kit owner's three
   successive rulings on this text, 17:3xZ / 18:0xZ / 18:3xZ, superseded by it): each arm's list E and its advance are
   keyed on THE SAME THING, the arm's own machine outcome; nothing at entry asserts a model event, and cnt / fail
   appear in neither. RESIDUE, not this text's: if the MODEL emits grow's event where the MACHINE made none (a refusal
   OUTSIDE a P1 reading), the caller is left at i and cannot supply its next callee there - that case belongs to the
   global preset_no_refusal (PresetCfnA), and the chosen failure is modelled by the starved runs. *)
Definition tgrow_specX (CTX0 : list (list Z)) : Prop :=
  forall most own,
  forall ly S Hp W regs mem md ch e v ty num str kids keys n cap (kb yb : list Z) Lam peak cnt fail ran,
  fpre B ARx STK_grow ly S Hp W regs mem md ch -> prh_univ_closure B CTX0 ->
  (* THE CHAIN FROM grow's s0 (the kit owner's ruling, by analogy with parse_string's): grow sets s0 := v + 48 and keeps
     it across both fuzz_realloc calls (generated pi_s0cur F_grow = Some 48, MEASURED on both rebuilt pins: A 0x86a0c
     `addi s0, s1, 48` with s1 = a0 at 0x869f4; B 0x870b8 `addi s0, s1, 48` with s1 = a0 at 0x8708c; no later write
     before the epilogue), so each call's afn_pre_x needs a chain at v + 48. In three of prhReader_at's cases v + 48
     is below alloc_ceiling and achain_low gives it; in the caller's granted extension (spZ regs <= v) it is a real
     stack address, and the word the unwinder reads at v + 48 - 16 is the node's keys field, which pj_slots_atR
     leaves free when ty <> 6 (the S5a walk's counter-case). Stated at the entry view: the chain's first record reads
     v + 32 (keys) and v + 40, which grow writes only AFTER its last realloc (keys after the keys realloc; between the
     two calls it writes only kids at v + 24), and its own frame lies below its sp. *)
  (exists ch, achain ly (aview segs (w_H W) mem) (spZ regs - pi_frame F_grow) (prh_s0 F_grow v) ch) ->
  room_live_cf S ->
  (* THE LIVE COUNTS AT THE INNER CALLS (the header; they replace counts_of_room_pos_rl): the secondary and class-24
     counts at every state along the ALL-GRANTED events prhPg_evs .. [] (the kids realloc's state and, for an
     object, the keys realloc's), from the entry's live requests. Position-free; no cnt / fail guard *)
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (prhPg_evs (ty =? 6) n cap [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (prhPg_evs (ty =? 6) n cap [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* THE HULL BUDGET (the header): room for the all-granted events, the kids and keys reallocs *)
  PresetHullBudget.hull_budget S (prhPg_evs (ty =? 6) n cap []) ->
  getr regs 10 = w64 v -> v <> 0 -> v mod 8 = 0 ->
  pj_hdrR segs (rdW W mem) v ty num str kids keys n cap ->
  pj_slots_atR (prh_lin Lam) ty kids keys n cap ->
  pj_apartR (kids_blkR kids cap ++ keys_blkR ty keys cap) v ->
  fwin ly W regs mem e -> prhReader_at ly S Lam regs e v 56 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 56 ->
  (n = cap -> bytes_at W mem kids kb /\ Z.of_nat (length kb) = 56 * cap /\
     (ty = 6 -> bytes_at W mem keys yb /\ Z.of_nat (length yb) = 8 * cap)) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  cnt + 2 < 2 ^ 64 - 1 ->
  (* THE REQUEST BOUND (the items-element walk's replacement, verbatim): the single largest request is the kids realloc (the
     keys one is smaller), not the two-block total (the peak-as-request class), and an array grows ONE block
     (PjGrammar.v:225-226).
     THE LIVE ROOM AT EACH EVENT of grow's own all-granted run, prhPg_evs (ty =? 6) n cap [] (the list the count
     premises above use; PRH_Base.prh_live_evs; the kit owner's entry-sum ruling 2026-10-30 00:36Z by its `date -u`,
     the third site of the one rule after the writer callees and rd_room, the K1-batch walk-kit lead's yes). It REPLACES
     `blocks_bytes S + LIVE_grow ty cap <= LIVE_MAX`, an ENTRY SUM OF BOTH reallocs' requests, which was SOUND BUT
     OVER-COUNTING: the kids realloc frees the old kids before the keys realloc. COUNTEREXAMPLE to deriving the sum
     from the per-event rd_room of parse_items (the live-event walk): an object at n = cap = 4, entry live L = LIVE_MAX - 464.
     The per-event room holds at BOTH events (kids: L + 448 + 16 = LIVE_MAX; keys: L - 240 + 464 + 80 = L + 304), but
     the sum needs L + 464 + 80 = LIVE_MAX + 80. THE NEW CONJUNCT IS WEAKER than the old at every caller (parse_items,
     pj_set): the old implies it (the kids event is the old sum minus the keys request; at the keys event the old kids
     block's removal only lowers the live bytes), equal for an array and at cap = 0, strictly weaker for an object at
     cap > 0 (the counterexample). So no caller of grow loses, and grow's walk gets exactly fuzz_realloc's live premise
     at each of its two calls. THE DISCHARGER IS PROVED: the live-bytes owner's entry_sum_ok / entry_sum_closed at the
     positioned event (lib/Spec/PresetLiveBytes.v:1751, :1827); parse_items supplies it from its own rd_room (grow's
     events are a segment of its rd_hevs gt, prhPg_ev_model at cf_head = HEAD). *)
  (n = cap -> 56 * cap2R cap + cf_head < cf_malloc_max /\ prh_live_evs S (prhPg_evs (ty =? 6) n cap [])) ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.H4): fpostWm is SHARED, so the post is its R
     form at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_grow) regs mem md)
    (fpostWmR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) STK_grow e
       ([(v + 24, v + 40); (v + 48, v + 56)] ++
        ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))
       regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\
       (* THE HULL USE (the header): at most the entry budget's list *)
       PresetHullBudget.hull_used S S' (prhPg_evs (ty =? 6) n cap []) /\
       (* the live room handed on to the caller's next call (the items-element walk's finding: parse_items calls grow, then
          parse_value, whose live room needs it): the bytes this call may add over its granted trace, heads included *)
       blocks_bytes S' <= blocks_bytes S + PRH_Charge.prh_held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap) /\
       ((* room left: nothing done *)
        (n < cap /\ getr regs' 10 = w64 0 /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
          (* NO ALLOCATOR CALL ON THIS ARM, so the bytes are EXACTLY kept (the kit owner's Option 1; the
             top-level bound above is over the GRANTED trace, which a caller cannot use to re-establish
             its own room) *)
          blocks_bytes S' = blocks_bytes S /\
         prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
         pj_hdrR segs (rdW W' mem') v ty num str kids keys n cap /\
         (* the slot blocks are in FP but NOTHING is written there on this arm (the kit owner's G1 ruling: the keep
            clause, not their removal from FP, so the member loop reads back the members already stored) *)
         (forall lo hi x, In (lo, hi) (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap))) ->
            lo <= x < hi -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) /\
         (* no allocator call (outcomes []): the live requests are kept, and the position with them (E = []) *)
         Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
           (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [])) /\
         (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
            (H0 : list Z) (hist : list YG00.chunk),
            PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
            PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap []) ->
            exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPg_evs (ty =? 6)%Z n cap []))%nat
              H0 hist' S'))
        \/
        (* the kids realloc is the chosen failure *)
        (n = cap /\ cnt = fail /\ getr regs' 10 = w64 (-1) /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
          (* the chosen failure makes no allocator call *)
          blocks_bytes S' = blocks_bytes S /\
         prh_ledger B ly' S' Hp' W' mem' Lam peak (cnt + 1) SIZE_MAXZ ran most own /\
         pj_hdrR segs (rdW W' mem') v ty num str kids keys n cap /\
         bytes_at W' mem' kids kb /\ (ty = 6 -> bytes_at W' mem' keys yb) /\
         (* fuzz_realloc's NULL (outcomes [false]): no event, E = [], the position kept *)
         Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
           (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [false])) /\
         (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
            (H0 : list Z) (hist : list YG00.chunk),
            PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
            PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [false]) ->
            exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPg_evs (ty =? 6)%Z n cap [false]))%nat
              H0 hist' S'))
        \/
        (* the kids realloc is refused *)
        (n = cap /\ cnt <> fail /\ getr regs' 10 = w64 (-1) /\ Permutation Hp' Hp /\
         ablocks B ly' S' = ablocks B ly S /\
          (* a refused malloc_cf leaves the blocks unchanged *)
          blocks_bytes S' = blocks_bytes S /\
         (* THE REFUSAL EVIDENCE, WORLD-FREE: blocks and chunks kept, the request from the primary, its class exhausted -
            what YG0dcf.malloc_cf_null_post at the kids call gives, without its world. The refused realloc's own post
            gives this form (YGcfRealloc.realloc_cf_refused_state) without reading the dead set at all; whether the
            refused arm's set is empty is open, and this form does not depend on the answer. *)
         (blocks S' = blocks S /\ st_chunks S' = st_chunks S /\ from_primary (56 * cap2R cap + cf_head) = true /\
          YG00cf.exh_mem_cf S' (chunk_class (56 * cap2R cap + cf_head)) = true) /\
         rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\
         (* THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS), as this REFUSED arm's exclusion: no model
            run and position whose next events are the ALL-GRANTED ones (prhPg_evs .. []), their reallocs CONSUMER
            events, meets this arm *)
         (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
            (H0 : list Z) (hist : list YG00.chunk),
            PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
            PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap []) ->
            PRH_Base.prh_cons_from sm x os i (length (prhPg_evs (ty =? 6) n cap [])) -> False) /\
         (* THE OUTCOME OF AN INJECTED READING (GUARDED; PRH_FnParse.tparse_value_specX's note), as this
            REFUSED arm's exclusion: no model run and position whose next events are grow's under the MODEL's grant list
            with the chosen failure at its call fail - cnt (PresetReqAt.okk), their reallocs CONSUMER events, with the
            chosen failure INSIDE grow's window, meets this arm. Only an OBJECT reaches it with the window open: fail =
            cnt + 1, the keys realloc chosen (an array's window is fail = cnt, which this arm's cnt <> fail closes), so
            the model's list is the kids realloc's event alone (prhPg_evs .. [true; false]) - the all-granted exclusion
            above cannot be used there, its two-event list not being the run's - and the kids realloc's OWN OUTCOME
            (tfuzz_realloc_specX: a CONSUMER event, cnt <> fail -> res <> 0) gives the grant. parse_items' walk needs it
            where its injected reading's chosen failure is a grow's keys realloc. The keys-refused arm below needs no
            such clause: its cnt <> fail and cnt + 1 <> fail close grow's window. *)
         (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
            (H0 : list Z) (hist : list YG00.chunk),
            PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
            PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap (PresetReqAt.okk (Z.to_nat (fail - cnt)))) ->
            PRH_Base.prh_cons_from sm x os i
              (length (prhPg_evs (ty =? 6) n cap (PresetReqAt.okk (Z.to_nat (fail - cnt))))) ->
            cnt <= fail < cnt + Z.of_nat (PjGrammar.calls (PRH_Charge.prhPg_gtrace (ty =? 6) n cap)) -> False) /\
         (* THE LEDGER IS fuzz_realloc's REFUSAL ARM VERBATIM at the kids call, n = 56 * cap2R cap (the kit owner's
            ruling, 2026-10-29 ~19:4xZ): cap = 0, kids = NULL, so fuzz_realloc (NULL, n) is fuzz_malloc's (prh_alloc_post
            arm 2, live + n); cap <> 0, tfuzz_realloc_specX's refused arm at k = 56 * cap (live - k + n: refused () runs
            after disown). COUNTEREXAMPLE to the old `Lam peak (cnt + 1) fail 1 most own`: ty = 6, cap = 8,
            peak = Ledger.lsum Lam, ran = 0, most < 896, the kids realloc refused: g_peak = peak + 448 and g_ran_out
            stays 0, where it said peak and 1. *)
         prh_ledger B ly' S' Hp' W' mem' Lam
           (if cap =? 0 then Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam + 56 * cap2R cap))
            else Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam - 56 * cap + 56 * cap2R cap)))
           ((cnt + 1) mod 2 ^ 64) fail (if 56 * cap2R cap <=? most then 1 else ran) most own /\
         pj_hdrR segs (rdW W' mem') v ty num str kids keys n cap /\
         bytes_at W' mem' kids kb /\ (ty = 6 -> bytes_at W' mem' keys yb) /\
         (* the refused realloc (outcomes [false]): no event, E = [], the position kept *)
         Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
           (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [false])) /\
         (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
            (H0 : list Z) (hist : list YG00.chunk),
            PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
            PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [false]) ->
            exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPg_evs (ty =? 6)%Z n cap [false]))%nat
              H0 hist' S'))
        \/
        (* an array: the kids moved *)
        (n = cap /\ cnt <> fail /\ ty <> 6 /\ getr regs' 10 = w64 0 /\
         exists k' Lam', 4096 + cf_head <= k' /\ k' mod 16 = 0 /\
           prhReader_swap ly S Hp Lam ly' S' Hp' Lam' (kids_blkR kids cap)
             [(k', 56 * cap2R cap)] /\
           prh_ledger B ly' S' Hp' W' mem' Lam' (Z.max peak (Ledger.lsum Lam')) (cnt + 1) fail ran most own /\
           (* the live user bytes moved by exactly the granted trace's net bytes (the items-element walk; the recursive-reader author's parse posts) *)
           Ledger.lsum Lam' = Ledger.lsum Lam + PjGrammar.held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap) /\
           bytes_at W' mem' k' kb /\ prhReader_vis W' mem' k' (56 * cap2R cap) /\
           pj_hdrR segs (rdW W' mem') v ty num str k' keys n (cap2R cap) /\
           pj_slots_atR (prh_lin Lam') ty k' keys n (cap2R cap) /\
           (* THE EXACT ADVANCE (outcomes [true]): E = the kids realloc's event *)
           Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
             (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [true])) /\
           (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
              (H0 : list Z) (hist : list YG00.chunk),
              PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
              PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [true]) ->
              exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPg_evs (ty =? 6)%Z n cap [true]))%nat
                H0 hist' S'))
        \/
        (* an object: the kids moved, the keys realloc is the chosen failure *)
        (n = cap /\ cnt <> fail /\ ty = 6 /\ cnt + 1 = fail /\ getr regs' 10 = w64 (-1) /\
         exists k' Lam', 4096 + cf_head <= k' /\ k' mod 16 = 0 /\
           prhReader_swap ly S Hp Lam ly' S' Hp' Lam' (kids_blkR kids cap)
             [(k', 56 * cap2R cap)] /\
           prh_ledger B ly' S' Hp' W' mem' Lam' (Z.max peak (Ledger.lsum Lam')) (cnt + 2) SIZE_MAXZ ran most own /\
           bytes_at W' mem' k' kb /\ prhReader_vis W' mem' k' (56 * cap2R cap) /\
           bytes_at W' mem' keys yb /\
           pj_hdrR segs (rdW W' mem') v ty num str k' keys n cap /\
           (* THE EXACT ADVANCE (outcomes [true; false]): E = the kids realloc's event; the keys realloc's NULL makes
              none (the chosen-failure skip) *)
           Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
             (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
                (prhPg_evs (ty =? 6) n cap [true; false])) /\
           (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
              (H0 : list Z) (hist : list YG00.chunk),
              PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
              PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [true; false]) ->
              exists hist', PresetRoomPos.iface_room_pos sm x os
                (i + length (prhPg_evs (ty =? 6)%Z n cap [true; false]))%nat H0 hist' S'))
        \/
        (* an object: the kids moved, the keys realloc is refused (G4) *)
        (n = cap /\ cnt <> fail /\ ty = 6 /\ cnt + 1 <> fail /\ getr regs' 10 = w64 (-1) /\
         exists k' Lam', 4096 + cf_head <= k' /\ k' mod 16 = 0 /\
           prhReader_swap ly S Hp Lam ly' S' Hp' Lam' (kids_blkR kids cap)
             [(k', 56 * cap2R cap)] /\
           (* THE REFUSAL EVIDENCE, WORLD-FREE (the kids arm's note): at the keys call's state S1 *)
           (exists S1, blocks S' = blocks S1 /\ st_chunks S' = st_chunks S1 /\
              from_primary (8 * cap2R cap + cf_head) = true /\
              YG00cf.exh_mem_cf S' (chunk_class (8 * cap2R cap + cf_head)) = true) /\
           rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\
           (* THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS), as this REFUSED arm's exclusion: no
              model run and position whose next events are the ALL-GRANTED ones (prhPg_evs .. [], the kids realloc's
              event then the keys realloc's), both CONSUMER events, meets this arm *)
           (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
              (H0 : list Z) (hist : list YG00.chunk),
              PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
              PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap []) ->
              PRH_Base.prh_cons_from sm x os i (length (prhPg_evs (ty =? 6) n cap [])) -> False) /\
           (* THE LEDGER IS fuzz_realloc's REFUSAL ARM VERBATIM at the keys call, n = 8 * cap2R cap, from the state the
              kids grant left as this text states it (the chosen-failure sibling's Lam', Z.max peak (Ledger.lsum Lam'),
              cnt + 1, ran): cap = 0, keys = NULL, prh_alloc_post arm 2; cap <> 0, the refused arm at k = 8 * cap.
              COUNTEREXAMPLE to the old `Lam' (Z.max peak (Ledger.lsum Lam')) (cnt + 2) fail 1 most own`: ty = 6,
              cap = 8, peak = Ledger.lsum Lam, ran = 0, most < 128, the kids realloc granted (Ledger.lsum Lam' =
              Ledger.lsum Lam + 448), the keys realloc refused: g_peak = Ledger.lsum Lam' + 64 and g_ran_out stays 0,
              where it said Ledger.lsum Lam' and 1. *)
           prh_ledger B ly' S' Hp' W' mem' Lam'
             (if cap =? 0 then Z.max (Z.max peak (Ledger.lsum Lam')) (Z.min SIZE_MAXZ (Ledger.lsum Lam' + 8 * cap2R cap))
              else Z.max (Z.max peak (Ledger.lsum Lam'))
                     (Z.min SIZE_MAXZ (Ledger.lsum Lam' - 8 * cap + 8 * cap2R cap)))
             ((cnt + 1 + 1) mod 2 ^ 64) fail (if 8 * cap2R cap <=? most then 1 else ran) most own /\
           bytes_at W' mem' k' kb /\ prhReader_vis W' mem' k' (56 * cap2R cap) /\
           bytes_at W' mem' keys yb /\
           pj_hdrR segs (rdW W' mem') v ty num str k' keys n cap /\
           (* THE EXACT ADVANCE (outcomes [true; false]): E = the kids realloc's event; the refused keys realloc
              makes none *)
           Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
             (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
                (prhPg_evs (ty =? 6) n cap [true; false])) /\
           (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
              (H0 : list Z) (hist : list YG00.chunk),
              PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
              PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [true; false]) ->
              exists hist', PresetRoomPos.iface_room_pos sm x os
                (i + length (prhPg_evs (ty =? 6)%Z n cap [true; false]))%nat H0 hist' S'))
        \/
        (* an object: the kids and the keys moved *)
        (n = cap /\ cnt <> fail /\ ty = 6 /\ cnt + 1 <> fail /\ getr regs' 10 = w64 0 /\
         exists k' y' Lam', 4096 + cf_head <= k' /\ k' mod 16 = 0 /\ 4096 + cf_head <= y' /\ y' mod 16 = 0 /\
           prhReader_swap ly S Hp Lam ly' S' Hp' Lam' (kids_blkR kids cap ++ keys_blkR ty keys cap)
             [(y', 8 * cap2R cap); (k', 56 * cap2R cap)] /\
           prh_ledger B ly' S' Hp' W' mem' Lam'
             (Z.max peak (Z.max (Ledger.lsum Lam + 56 * (cap2R cap - cap)) (Ledger.lsum Lam')))
             (cnt + 2) fail ran most own /\
           Ledger.lsum Lam' = Ledger.lsum Lam + PjGrammar.held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap) /\
           bytes_at W' mem' k' kb /\ prhReader_vis W' mem' k' (56 * cap2R cap) /\
           bytes_at W' mem' y' yb /\ prhReader_vis W' mem' y' (8 * cap2R cap) /\
           pj_hdrR segs (rdW W' mem') v ty num str k' y' n (cap2R cap) /\
           pj_slots_atR (prh_lin Lam') ty k' y' n (cap2R cap) /\
           (* THE EXACT ADVANCE (outcomes [true; true]): E = both reallocs' events *)
           Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
             (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
                (prhPg_evs (ty =? 6) n cap [true; true])) /\
           (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
              (H0 : list Z) (hist : list YG00.chunk),
              PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
              PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [true; true]) ->
              exists hist', PresetRoomPos.iface_room_pos sm x os
                (i + length (prhPg_evs (ty =? 6)%Z n cap [true; true]))%nat H0 hist' S'))))).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tgrow_specX's POST, NAMED (read the text's post through NAMED projections; destruct once, cite the
   lemma). ADDITIVE: the text above is unchanged. tgrP_Q IS the text's post (tgrP_Q_check fails to build if the two ever
   differ); tgrP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas build the post
   from them. A consumer that reads and builds the post through these is not broken by the NEXT appended conjunct. ====
       *)

Definition tgrP_A1 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option
    byte) (v ty num str kids keys n cap : Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate)
    (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  n < cap /\ getr regs' 10 = w64 0 /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\ blocks_bytes S' = blocks_bytes
    S /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\ pj_hdrR segs (rdW W' mem') v ty num str
    kids keys n cap /\ (forall lo hi x, In (lo, hi) (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty
    keys cap))) -> lo <= x < hi -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) /\ Permutation
    (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf
    S)) (prhPg_evs (ty =? 6) n cap [])) /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat *
    option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os
    i H0 hist S -> PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap []) -> exists hist',
    PresetRoomPos.iface_room_pos sm x os (i + length (prhPg_evs (ty =? 6)%Z n cap []))%nat H0 hist' S').

Definition tgrP_A2 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z) (kb yb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  n = cap /\ cnt = fail /\ getr regs' 10 = w64 (-1) /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\ blocks_bytes
    S' = blocks_bytes S /\ prh_ledger B ly' S' Hp' W' mem' Lam peak (cnt + 1) SIZE_MAXZ ran most own /\ pj_hdrR segs
    (rdW W' mem') v ty num str kids keys n cap /\ bytes_at W' mem' kids kb /\ (ty = 6 -> bytes_at W' mem' keys yb) /\
    Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
    (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [false])) /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os
    : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap
    [false]) -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPg_evs (ty =? 6)%Z n cap
    [false]))%nat H0 hist' S').

Definition tgrP_A3 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z) (kb yb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  n = cap /\ cnt <> fail /\ getr regs' 10 = w64 (-1) /\ Permutation Hp' Hp /\ ablocks B ly' S' = ablocks B ly S /\
    blocks_bytes S' = blocks_bytes S /\ (blocks S' = blocks S /\ st_chunks S' = st_chunks S /\ from_primary (56 *
    cap2R cap + cf_head) = true /\ YG00cf.exh_mem_cf S' (chunk_class (56 * cap2R cap + cf_head)) = true) /\ rd32
    (aview segs (w_H W') mem') (as_errno B) 12 /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat
    * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x
    os i H0 hist S -> PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap []) -> PRH_Base.prh_cons_from sm x os
    i (length (prhPg_evs (ty =? 6) n cap [])) -> False) /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os : list
    (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap
    (PresetReqAt.okk (Z.to_nat (fail - cnt)))) -> PRH_Base.prh_cons_from sm x os i (length (prhPg_evs (ty =? 6) n cap
    (PresetReqAt.okk (Z.to_nat (fail - cnt))))) -> cnt <= fail < cnt + Z.of_nat (PjGrammar.calls
    (PRH_Charge.prhPg_gtrace (ty =? 6) n cap)) -> False) /\ prh_ledger B ly' S' Hp' W' mem' Lam (if cap =? 0 then
    Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam + 56 * cap2R cap)) else Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam
    - 56 * cap + 56 * cap2R cap))) ((cnt + 1) mod 2 ^ 64) fail (if 56 * cap2R cap <=? most then 1 else ran) most own
    /\ pj_hdrR segs (rdW W' mem') v ty num str kids keys n cap /\ bytes_at W' mem' kids kb /\ (ty = 6 -> bytes_at W'
    mem' keys yb) /\ Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from
    (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [false])) /\ (forall (sm : list Z -> Z *
    Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list
    YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =?
    6) n cap [false]) -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPg_evs (ty =? 6)%Z n cap
    [false]))%nat H0 hist' S').

Definition tgrP_A4 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z) (kb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  n = cap /\ cnt <> fail /\ ty <> 6 /\ getr regs' 10 = w64 0 /\ exists k' Lam', 4096 + cf_head <= k' /\ k' mod 16 = 0
    /\ prhReader_swap ly S Hp Lam ly' S' Hp' Lam' (kids_blkR kids cap) [(k', 56 * cap2R cap)] /\ prh_ledger B ly' S'
    Hp' W' mem' Lam' (Z.max peak (Ledger.lsum Lam')) (cnt + 1) fail ran most own /\ Ledger.lsum Lam' = Ledger.lsum
    Lam + PjGrammar.held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap) /\ bytes_at W' mem' k' kb /\ prhReader_vis W' mem'
    k' (56 * cap2R cap) /\ pj_hdrR segs (rdW W' mem') v ty num str k' keys n (cap2R cap) /\ pj_slots_atR (prh_lin
    Lam') ty k' keys n (cap2R cap) /\ Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [true])) /\
    (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 :
    list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os
    i (prhPg_evs (ty =? 6) n cap [true]) -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPg_evs
    (ty =? 6)%Z n cap [true]))%nat H0 hist' S').

Definition tgrP_A5 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z) (kb yb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  n = cap /\ cnt <> fail /\ ty = 6 /\ cnt + 1 = fail /\ getr regs' 10 = w64 (-1) /\ exists k' Lam', 4096 + cf_head <=
    k' /\ k' mod 16 = 0 /\ prhReader_swap ly S Hp Lam ly' S' Hp' Lam' (kids_blkR kids cap) [(k', 56 * cap2R cap)] /\
    prh_ledger B ly' S' Hp' W' mem' Lam' (Z.max peak (Ledger.lsum Lam')) (cnt + 2) SIZE_MAXZ ran most own /\ bytes_at
    W' mem' k' kb /\ prhReader_vis W' mem' k' (56 * cap2R cap) /\ bytes_at W' mem' keys yb /\ pj_hdrR segs (rdW W'
    mem') v ty num str k' keys n cap /\ Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [true; false]))
    /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 :
    list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os
    i (prhPg_evs (ty =? 6) n cap [true; false]) -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length
    (prhPg_evs (ty =? 6)%Z n cap [true; false]))%nat H0 hist' S').

Definition tgrP_A6 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z) (kb yb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  n = cap /\ cnt <> fail /\ ty = 6 /\ cnt + 1 <> fail /\ getr regs' 10 = w64 (-1) /\ exists k' Lam', 4096 + cf_head
    <= k' /\ k' mod 16 = 0 /\ prhReader_swap ly S Hp Lam ly' S' Hp' Lam' (kids_blkR kids cap) [(k', 56 * cap2R cap)]
    /\ (exists S1, blocks S' = blocks S1 /\ st_chunks S' = st_chunks S1 /\ from_primary (8 * cap2R cap + cf_head) =
    true /\ YG00cf.exh_mem_cf S' (chunk_class (8 * cap2R cap + cf_head)) = true) /\ rd32 (aview segs (w_H W') mem')
    (as_errno B) 12 /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
    (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap []) -> PRH_Base.prh_cons_from sm x os i (length
    (prhPg_evs (ty =? 6) n cap [])) -> False) /\ prh_ledger B ly' S' Hp' W' mem' Lam' (if cap =? 0 then Z.max (Z.max
    peak (Ledger.lsum Lam')) (Z.min SIZE_MAXZ (Ledger.lsum Lam' + 8 * cap2R cap)) else Z.max (Z.max peak (Ledger.lsum
    Lam')) (Z.min SIZE_MAXZ (Ledger.lsum Lam' - 8 * cap + 8 * cap2R cap))) ((cnt + 1 + 1) mod 2 ^ 64) fail (if 8 *
    cap2R cap <=? most then 1 else ran) most own /\ bytes_at W' mem' k' kb /\ prhReader_vis W' mem' k' (56 * cap2R
    cap) /\ bytes_at W' mem' keys yb /\ pj_hdrR segs (rdW W' mem') v ty num str k' keys n cap /\ Permutation
    (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf
    S)) (prhPg_evs (ty =? 6) n cap [true; false])) /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option
    nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm
    x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [true; false]) -> exists hist',
    PresetRoomPos.iface_room_pos sm x os (i + length (prhPg_evs (ty =? 6)%Z n cap [true; false]))%nat H0 hist' S').

Definition tgrP_A7 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z) (kb yb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  n = cap /\ cnt <> fail /\ ty = 6 /\ cnt + 1 <> fail /\ getr regs' 10 = w64 0 /\ exists k' y' Lam', 4096 + cf_head
    <= k' /\ k' mod 16 = 0 /\ 4096 + cf_head <= y' /\ y' mod 16 = 0 /\ prhReader_swap ly S Hp Lam ly' S' Hp' Lam'
    (kids_blkR kids cap ++ keys_blkR ty keys cap) [(y', 8 * cap2R cap); (k', 56 * cap2R cap)] /\ prh_ledger B ly' S'
    Hp' W' mem' Lam' (Z.max peak (Z.max (Ledger.lsum Lam + 56 * (cap2R cap - cap)) (Ledger.lsum Lam'))) (cnt + 2)
    fail ran most own /\ Ledger.lsum Lam' = Ledger.lsum Lam + PjGrammar.held (PRH_Charge.prhPg_gtrace (ty =? 6) n
    cap) /\ bytes_at W' mem' k' kb /\ prhReader_vis W' mem' k' (56 * cap2R cap) /\ bytes_at W' mem' y' yb /\
    prhReader_vis W' mem' y' (8 * cap2R cap) /\ pj_hdrR segs (rdW W' mem') v ty num str k' y' n (cap2R cap) /\
    pj_slots_atR (prh_lin Lam') ty k' y' n (cap2R cap) /\ Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [true; true])) /\
    (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 :
    list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os
    i (prhPg_evs (ty =? 6) n cap [true; true]) -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length
    (prhPg_evs (ty =? 6)%Z n cap [true; true]))%nat H0 hist' S').

Definition tgrP_Q (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte)
    (v ty num str kids keys n cap : Z) (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  room_live_cf S' /\ PresetHullBudget.hull_used S S' (prhPg_evs (ty =? 6) n cap []) /\ blocks_bytes S' <= blocks_bytes
    S + PRH_Charge.prh_held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap) /\ (tgrP_A1 most own ly S Hp W mem v ty num str
    kids keys n cap Lam peak cnt fail ran ly' S' Hp' W' regs'
    mem' \/ tgrP_A2 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs'
    mem' \/ tgrP_A3 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs'
    mem' \/ tgrP_A4 most own ly S Hp v ty num str kids keys n cap kb Lam peak cnt fail ran ly' S' Hp' W' regs' mem'
    \/ tgrP_A5 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' \/
    tgrP_A6 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' \/
    tgrP_A7 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem').

Lemma tgrP_Q_check : forall (CTX0 : list (list Z)), tgrow_specX CTX0 -> tgrow_specX CTX0.
Proof.
  intros CTX0 H. unfold tgrow_specX in *.
  intros most own ly S Hp W regs mem md ch e v ty num str kids keys n cap kb yb Lam peak cnt fail ran.
  specialize (H most own ly S Hp W regs mem md ch e v ty num str kids keys n cap kb yb Lam peak cnt fail ran).
  (* the conclusion is SRr' (the re-hiding move), so the post is found under SRr' *)
  lazymatch type of H with context [SRr' _ _ _ _ (?F ?Q)] => change Q with (tgrP_Q most own ly S Hp W mem v ty num str
      kids keys n cap kb yb Lam peak cnt fail ran) in H end.
  exact H.
Qed.

Record tgrP_R (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (v
    ty num str kids keys n cap : Z) (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' :
    astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := {
  tgrP_room : room_live_cf S';
  tgrP_hull : PresetHullBudget.hull_used S S' (prhPg_evs (ty =? 6) n cap []);
  tgrP_bytes : blocks_bytes S' <= blocks_bytes S + PRH_Charge.prh_held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap);
  tgrP_arms : (tgrP_A1 most own ly S Hp W mem v ty num str kids keys n cap Lam peak cnt fail ran ly' S' Hp' W' regs'
    mem' \/ tgrP_A2 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs'
    mem' \/ tgrP_A3 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs'
    mem' \/ tgrP_A4 most own ly S Hp v ty num str kids keys n cap kb Lam peak cnt fail ran ly' S' Hp' W' regs' mem'
    \/ tgrP_A5 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' \/
    tgrP_A6 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' \/
    tgrP_A7 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem') }.

Lemma tgrP_R_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word ->
    option byte) (v ty num str kids keys n cap : Z) (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly'
    : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md'
    : Model),
  tgrP_Q most own ly S Hp W mem v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' ->
  tgrP_R most own ly S Hp W mem v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem'.
Proof.
  intros most own ly S Hp W mem v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md'
      H. destruct H as (H0 & Hh & H1 & H2).
  exact {| tgrP_room := H0; tgrP_hull := Hh; tgrP_bytes := H1; tgrP_arms := H2 |}.
Qed.

Lemma tgrP_Q_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word ->
    option byte) (v ty num str kids keys n cap : Z) (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly'
    : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md'
    : Model),
  tgrP_R most own ly S Hp W mem v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ->
  tgrP_Q most own ly S Hp W mem v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md'.
Proof.
  intros most own ly S Hp W mem v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md'
      HR.
  exact (conj (tgrP_room HR) (conj (tgrP_hull HR) (conj (tgrP_bytes HR) (tgrP_arms HR)))).
Qed.


Record tgrP_R1 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (v
    ty num str kids keys n cap : Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' :
    list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := {
  tgrP1_lt : n < cap;
  tgrP1_ret : getr regs' 10 = w64 0;
  tgrP1_hp : Hp' = Hp;
  tgrP1_ablocks : ablocks B ly' S' = ablocks B ly S;
  tgrP1_bytes : blocks_bytes S' = blocks_bytes S;
  tgrP1_ledger : prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own;
  tgrP1_hdr : pj_hdrR segs (rdW W' mem') v ty num str kids keys n cap;
  tgrP1_keep : (forall lo hi x, In (lo, hi) (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))
    -> lo <= x < hi -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x);
  tgrP1_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
    (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap []));
  tgrP1_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap []) -> exists hist', PresetRoomPos.iface_room_pos sm x
    os (i + length (prhPg_evs (ty =? 6)%Z n cap []))%nat H0 hist' S') }.

Lemma tgrP_R1_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word ->
    option byte) (v ty num str kids keys n cap : Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' :
    astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte),
  tgrP_A1 most own ly S Hp W mem v ty num str kids keys n cap Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ->
  tgrP_R1 most own ly S Hp W mem v ty num str kids keys n cap Lam peak cnt fail ran ly' S' Hp' W' regs' mem'.
Proof.
  intros most own ly S Hp W mem v ty num str kids keys n cap Lam peak cnt fail ran ly' S' Hp' W' regs' mem' H. destruct
      H as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  exact {| tgrP1_lt := H0; tgrP1_ret := H1; tgrP1_hp := H2; tgrP1_ablocks := H3; tgrP1_bytes := H4; tgrP1_ledger := H5;
      tgrP1_hdr := H6; tgrP1_keep := H7; tgrP1_live := H8; tgrP1_pos := H9 |}.
Qed.

Lemma tgrP_A1_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word ->
    option byte) (v ty num str kids keys n cap : Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' :
    astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte),
  tgrP_R1 most own ly S Hp W mem v ty num str kids keys n cap Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ->
  tgrP_A1 most own ly S Hp W mem v ty num str kids keys n cap Lam peak cnt fail ran ly' S' Hp' W' regs' mem'.
Proof.
  intros most own ly S Hp W mem v ty num str kids keys n cap Lam peak cnt fail ran ly' S' Hp' W' regs' mem' HR.
  exact (conj (tgrP1_lt HR) (conj (tgrP1_ret HR) (conj (tgrP1_hp HR) (conj (tgrP1_ablocks HR) (conj (tgrP1_bytes HR)
      (conj (tgrP1_ledger HR) (conj (tgrP1_hdr HR) (conj (tgrP1_keep HR) (conj (tgrP1_live HR) (tgrP1_pos HR)))))))))).
Qed.


Record tgrP_R2 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z) (kb yb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := {
  tgrP2_eq : n = cap;
  tgrP2_chosen : cnt = fail;
  tgrP2_ret : getr regs' 10 = w64 (-1);
  tgrP2_hp : Hp' = Hp;
  tgrP2_ablocks : ablocks B ly' S' = ablocks B ly S;
  tgrP2_bytes : blocks_bytes S' = blocks_bytes S;
  tgrP2_ledger : prh_ledger B ly' S' Hp' W' mem' Lam peak (cnt + 1) SIZE_MAXZ ran most own;
  tgrP2_hdr : pj_hdrR segs (rdW W' mem') v ty num str kids keys n cap;
  tgrP2_kb : bytes_at W' mem' kids kb;
  tgrP2_yb : (ty = 6 -> bytes_at W' mem' keys yb);
  tgrP2_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
    (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [false]));
  tgrP2_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [false]) -> exists hist', PresetRoomPos.iface_room_pos
    sm x os (i + length (prhPg_evs (ty =? 6)%Z n cap [false]))%nat H0 hist' S') }.

Lemma tgrP_R2_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z)
    (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte),
  tgrP_A2 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ->
  tgrP_R2 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem'.
Proof.
  intros most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' H. destruct
      H as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  exact {| tgrP2_eq := H0; tgrP2_chosen := H1; tgrP2_ret := H2; tgrP2_hp := H3; tgrP2_ablocks := H4; tgrP2_bytes := H5;
      tgrP2_ledger := H6; tgrP2_hdr := H7; tgrP2_kb := H8; tgrP2_yb := H9; tgrP2_live := H10; tgrP2_pos := H11 |}.
Qed.

Lemma tgrP_A2_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z)
    (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte),
  tgrP_R2 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ->
  tgrP_A2 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem'.
Proof.
  intros most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' HR.
  exact (conj (tgrP2_eq HR) (conj (tgrP2_chosen HR) (conj (tgrP2_ret HR) (conj (tgrP2_hp HR) (conj (tgrP2_ablocks HR)
      (conj (tgrP2_bytes HR) (conj (tgrP2_ledger HR) (conj (tgrP2_hdr HR) (conj (tgrP2_kb HR) (conj (tgrP2_yb HR) (conj
      (tgrP2_live HR) (tgrP2_pos HR)))))))))))).
Qed.


Record tgrP_R3 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z) (kb yb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := {
  tgrP3_eq : n = cap;
  tgrP3_notchosen : cnt <> fail;
  tgrP3_ret : getr regs' 10 = w64 (-1);
  tgrP3_hp : Permutation Hp' Hp;
  tgrP3_ablocks : ablocks B ly' S' = ablocks B ly S;
  tgrP3_bytes : blocks_bytes S' = blocks_bytes S;
  tgrP3_evidence : (blocks S' = blocks S /\ st_chunks S' = st_chunks S /\ from_primary (56 * cap2R cap + cf_head) =
    true /\ YG00cf.exh_mem_cf S' (chunk_class (56 * cap2R cap + cf_head)) = true);
  tgrP3_errno : rd32 (aview segs (w_H W') mem') (as_errno B) 12;
  tgrP3_outcome : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap []) -> PRH_Base.prh_cons_from sm x os i (length
    (prhPg_evs (ty =? 6) n cap [])) -> False);
  tgrP3_injected : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i
    : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap (PresetReqAt.okk (Z.to_nat (fail - cnt)))) ->
    PRH_Base.prh_cons_from sm x os i (length (prhPg_evs (ty =? 6) n cap (PresetReqAt.okk (Z.to_nat (fail - cnt)))))
    -> cnt <= fail < cnt + Z.of_nat (PjGrammar.calls (PRH_Charge.prhPg_gtrace (ty =? 6) n cap)) -> False);
  tgrP3_ledger : prh_ledger B ly' S' Hp' W' mem' Lam (if cap =? 0 then Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam +
    56 * cap2R cap)) else Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam - 56 * cap + 56 * cap2R cap))) ((cnt + 1) mod
    2 ^ 64) fail (if 56 * cap2R cap <=? most then 1 else ran) most own;
  tgrP3_hdr : pj_hdrR segs (rdW W' mem') v ty num str kids keys n cap;
  tgrP3_kb : bytes_at W' mem' kids kb;
  tgrP3_yb : (ty = 6 -> bytes_at W' mem' keys yb);
  tgrP3_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
    (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [false]));
  tgrP3_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [false]) -> exists hist', PresetRoomPos.iface_room_pos
    sm x os (i + length (prhPg_evs (ty =? 6)%Z n cap [false]))%nat H0 hist' S') }.

Lemma tgrP_R3_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z)
    (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte),
  tgrP_A3 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ->
  tgrP_R3 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem'.
Proof.
  intros most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' H. destruct
      H as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
  exact {| tgrP3_eq := H0; tgrP3_notchosen := H1; tgrP3_ret := H2; tgrP3_hp := H3; tgrP3_ablocks := H4; tgrP3_bytes :=
      H5; tgrP3_evidence := H6; tgrP3_errno := H7; tgrP3_outcome := H8; tgrP3_injected := H9; tgrP3_ledger := H10;
      tgrP3_hdr := H11; tgrP3_kb := H12; tgrP3_yb := H13; tgrP3_live := H14; tgrP3_pos := H15 |}.
Qed.

Lemma tgrP_A3_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z)
    (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte),
  tgrP_R3 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ->
  tgrP_A3 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem'.
Proof.
  intros most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' HR.
  exact (conj (tgrP3_eq HR) (conj (tgrP3_notchosen HR) (conj (tgrP3_ret HR) (conj (tgrP3_hp HR) (conj (tgrP3_ablocks
      HR) (conj (tgrP3_bytes HR) (conj (tgrP3_evidence HR) (conj (tgrP3_errno HR) (conj (tgrP3_outcome HR) (conj
      (tgrP3_injected HR) (conj (tgrP3_ledger HR) (conj (tgrP3_hdr HR) (conj (tgrP3_kb HR) (conj (tgrP3_yb HR) (conj
      (tgrP3_live HR) (tgrP3_pos HR)))))))))))))))).
Qed.


Record tgrP_R4 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z) (kb : list
    Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (k' : Z) (Lam' : list (Z * Z)) : Prop := {
  tgrP4_eq : n = cap;
  tgrP4_notchosen : cnt <> fail;
  tgrP4_array : ty <> 6;
  tgrP4_ret : getr regs' 10 = w64 0;
  tgrP4_kmin : 4096 + cf_head <= k';
  tgrP4_kalign : k' mod 16 = 0;
  tgrP4_swap : prhReader_swap ly S Hp Lam ly' S' Hp' Lam' (kids_blkR kids cap) [(k', 56 * cap2R cap)];
  tgrP4_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' (Z.max peak (Ledger.lsum Lam')) (cnt + 1) fail ran most own;
  tgrP4_lsum : Ledger.lsum Lam' = Ledger.lsum Lam + PjGrammar.held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap);
  tgrP4_kb : bytes_at W' mem' k' kb;
  tgrP4_kvis : prhReader_vis W' mem' k' (56 * cap2R cap);
  tgrP4_hdr : pj_hdrR segs (rdW W' mem') v ty num str k' keys n (cap2R cap);
  tgrP4_slots : pj_slots_atR (prh_lin Lam') ty k' keys n (cap2R cap);
  tgrP4_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
    (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [true]));
  tgrP4_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [true]) -> exists hist', PresetRoomPos.iface_room_pos sm
    x os (i + length (prhPg_evs (ty =? 6)%Z n cap [true]))%nat H0 hist' S') }.

Lemma tgrP_R4_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z)
    (kb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world
    segs) (regs' : bvmap 5 word) (mem' : word -> option byte),
  tgrP_A4 most own ly S Hp v ty num str kids keys n cap kb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ->
  exists k' Lam', tgrP_R4 most own ly S Hp v ty num str kids keys n cap kb Lam peak cnt fail ran ly' S' Hp' W' regs'
      mem' k' Lam'.
Proof.
  intros most own ly S Hp v ty num str kids keys n cap kb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' H. destruct H
      as (H0 & H1 & H2 & H3 & k' & Lam' & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14).
  exists k', Lam'.
  exact {| tgrP4_eq := H0; tgrP4_notchosen := H1; tgrP4_array := H2; tgrP4_ret := H3; tgrP4_kmin := H4; tgrP4_kalign :=
      H5; tgrP4_swap := H6; tgrP4_ledger := H7; tgrP4_lsum := H8; tgrP4_kb := H9; tgrP4_kvis := H10; tgrP4_hdr := H11;
      tgrP4_slots := H12; tgrP4_live := H13; tgrP4_pos := H14 |}.
Qed.

Lemma tgrP_A4_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z)
    (kb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world
    segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (k' : Z) (Lam' : list (Z * Z)),
  tgrP_R4 most own ly S Hp v ty num str kids keys n cap kb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' k' Lam' ->
  tgrP_A4 most own ly S Hp v ty num str kids keys n cap kb Lam peak cnt fail ran ly' S' Hp' W' regs' mem'.
Proof.
  intros most own ly S Hp v ty num str kids keys n cap kb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' k' Lam' HR.
  refine (conj (tgrP4_eq HR) (conj (tgrP4_notchosen HR) (conj (tgrP4_array HR) (conj (tgrP4_ret HR) _)))).
  exists k', Lam'.
  exact (conj (tgrP4_kmin HR) (conj (tgrP4_kalign HR) (conj (tgrP4_swap HR) (conj (tgrP4_ledger HR) (conj (tgrP4_lsum
      HR) (conj (tgrP4_kb HR) (conj (tgrP4_kvis HR) (conj (tgrP4_hdr HR) (conj (tgrP4_slots HR) (conj (tgrP4_live HR)
      (tgrP4_pos HR))))))))))).
Qed.


Record tgrP_R5 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z) (kb yb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (k' : Z) (Lam' : list (Z * Z)) : Prop := {
  tgrP5_eq : n = cap;
  tgrP5_notchosen : cnt <> fail;
  tgrP5_object : ty = 6;
  tgrP5_chosen : cnt + 1 = fail;
  tgrP5_ret : getr regs' 10 = w64 (-1);
  tgrP5_kmin : 4096 + cf_head <= k';
  tgrP5_kalign : k' mod 16 = 0;
  tgrP5_swap : prhReader_swap ly S Hp Lam ly' S' Hp' Lam' (kids_blkR kids cap) [(k', 56 * cap2R cap)];
  tgrP5_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' (Z.max peak (Ledger.lsum Lam')) (cnt + 2) SIZE_MAXZ ran most
    own;
  tgrP5_kb : bytes_at W' mem' k' kb;
  tgrP5_kvis : prhReader_vis W' mem' k' (56 * cap2R cap);
  tgrP5_yb : bytes_at W' mem' keys yb;
  tgrP5_hdr : pj_hdrR segs (rdW W' mem') v ty num str k' keys n cap;
  tgrP5_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
    (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [true; false]));
  tgrP5_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [true; false]) -> exists hist',
    PresetRoomPos.iface_room_pos sm x os (i + length (prhPg_evs (ty =? 6)%Z n cap [true; false]))%nat H0 hist' S') }.

Lemma tgrP_R5_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z)
    (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte),
  tgrP_A5 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ->
  exists k' Lam', tgrP_R5 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs'
      mem' k' Lam'.
Proof.
  intros most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' H. destruct
      H as (H0 & H1 & H2 & H3 & H4 & k' & Lam' & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14).
  exists k', Lam'.
  exact {| tgrP5_eq := H0; tgrP5_notchosen := H1; tgrP5_object := H2; tgrP5_chosen := H3; tgrP5_ret := H4; tgrP5_kmin
      := H5; tgrP5_kalign := H6; tgrP5_swap := H7; tgrP5_ledger := H8; tgrP5_kb := H9; tgrP5_kvis := H10; tgrP5_yb :=
      H11; tgrP5_hdr := H12; tgrP5_live := H13; tgrP5_pos := H14 |}.
Qed.

Lemma tgrP_A5_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z)
    (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (k' : Z) (Lam' : list (Z * Z)),
  tgrP_R5 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' k' Lam' ->
  tgrP_A5 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem'.
Proof.
  intros most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' k' Lam' HR.
  refine (conj (tgrP5_eq HR) (conj (tgrP5_notchosen HR) (conj (tgrP5_object HR) (conj (tgrP5_chosen HR) (conj
      (tgrP5_ret HR) _))))).
  exists k', Lam'.
  exact (conj (tgrP5_kmin HR) (conj (tgrP5_kalign HR) (conj (tgrP5_swap HR) (conj (tgrP5_ledger HR) (conj (tgrP5_kb HR)
      (conj (tgrP5_kvis HR) (conj (tgrP5_yb HR) (conj (tgrP5_hdr HR) (conj (tgrP5_live HR) (tgrP5_pos HR)))))))))).
Qed.


Record tgrP_R6 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z) (kb yb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (k' : Z) (Lam' : list (Z * Z)) : Prop := {
  tgrP6_eq : n = cap;
  tgrP6_notchosen : cnt <> fail;
  tgrP6_object : ty = 6;
  tgrP6_notchosen1 : cnt + 1 <> fail;
  tgrP6_ret : getr regs' 10 = w64 (-1);
  tgrP6_kmin : 4096 + cf_head <= k';
  tgrP6_kalign : k' mod 16 = 0;
  tgrP6_swap : prhReader_swap ly S Hp Lam ly' S' Hp' Lam' (kids_blkR kids cap) [(k', 56 * cap2R cap)];
  tgrP6_evidence : (exists S1, blocks S' = blocks S1 /\ st_chunks S' = st_chunks S1 /\ from_primary (8 * cap2R cap +
    cf_head) = true /\ YG00cf.exh_mem_cf S' (chunk_class (8 * cap2R cap + cf_head)) = true);
  tgrP6_errno : rd32 (aview segs (w_H W') mem') (as_errno B) 12;
  tgrP6_outcome : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap []) -> PRH_Base.prh_cons_from sm x os i (length
    (prhPg_evs (ty =? 6) n cap [])) -> False);
  tgrP6_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' (if cap =? 0 then Z.max (Z.max peak (Ledger.lsum Lam')) (Z.min
    SIZE_MAXZ (Ledger.lsum Lam' + 8 * cap2R cap)) else Z.max (Z.max peak (Ledger.lsum Lam')) (Z.min SIZE_MAXZ
    (Ledger.lsum Lam' - 8 * cap + 8 * cap2R cap))) ((cnt + 1 + 1) mod 2 ^ 64) fail (if 8 * cap2R cap <=? most then 1
    else ran) most own;
  tgrP6_kb : bytes_at W' mem' k' kb;
  tgrP6_kvis : prhReader_vis W' mem' k' (56 * cap2R cap);
  tgrP6_yb : bytes_at W' mem' keys yb;
  tgrP6_hdr : pj_hdrR segs (rdW W' mem') v ty num str k' keys n cap;
  tgrP6_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
    (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [true; false]));
  tgrP6_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [true; false]) -> exists hist',
    PresetRoomPos.iface_room_pos sm x os (i + length (prhPg_evs (ty =? 6)%Z n cap [true; false]))%nat H0 hist' S') }.

Lemma tgrP_R6_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z)
    (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte),
  tgrP_A6 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ->
  exists k' Lam', tgrP_R6 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs'
      mem' k' Lam'.
Proof.
  intros most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' H. destruct
      H as (H0 & H1 & H2 & H3 & H4 & k' & Lam' & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 &
      H17).
  exists k', Lam'.
  exact {| tgrP6_eq := H0; tgrP6_notchosen := H1; tgrP6_object := H2; tgrP6_notchosen1 := H3; tgrP6_ret := H4;
      tgrP6_kmin := H5; tgrP6_kalign := H6; tgrP6_swap := H7; tgrP6_evidence := H8; tgrP6_errno := H9; tgrP6_outcome :=
      H10; tgrP6_ledger := H11; tgrP6_kb := H12; tgrP6_kvis := H13; tgrP6_yb := H14; tgrP6_hdr := H15; tgrP6_live :=
      H16; tgrP6_pos := H17 |}.
Qed.

Lemma tgrP_A6_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z)
    (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (k' : Z) (Lam' : list (Z * Z)),
  tgrP_R6 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' k' Lam' ->
  tgrP_A6 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem'.
Proof.
  intros most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' k' Lam' HR.
  refine (conj (tgrP6_eq HR) (conj (tgrP6_notchosen HR) (conj (tgrP6_object HR) (conj (tgrP6_notchosen1 HR) (conj
      (tgrP6_ret HR) _))))).
  exists k', Lam'.
  exact (conj (tgrP6_kmin HR) (conj (tgrP6_kalign HR) (conj (tgrP6_swap HR) (conj (tgrP6_evidence HR) (conj
      (tgrP6_errno HR) (conj (tgrP6_outcome HR) (conj (tgrP6_ledger HR) (conj (tgrP6_kb HR) (conj (tgrP6_kvis HR) (conj
      (tgrP6_yb HR) (conj (tgrP6_hdr HR) (conj (tgrP6_live HR) (tgrP6_pos HR))))))))))))).
Qed.


Record tgrP_R7 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z) (kb yb :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (k' y' : Z) (Lam' : list (Z * Z)) : Prop := {
  tgrP7_eq : n = cap;
  tgrP7_notchosen : cnt <> fail;
  tgrP7_object : ty = 6;
  tgrP7_notchosen1 : cnt + 1 <> fail;
  tgrP7_ret : getr regs' 10 = w64 0;
  tgrP7_kmin : 4096 + cf_head <= k';
  tgrP7_kalign : k' mod 16 = 0;
  tgrP7_ymin : 4096 + cf_head <= y';
  tgrP7_yalign : y' mod 16 = 0;
  tgrP7_swap : prhReader_swap ly S Hp Lam ly' S' Hp' Lam' (kids_blkR kids cap ++ keys_blkR ty keys cap) [(y', 8 *
    cap2R cap); (k', 56 * cap2R cap)];
  tgrP7_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' (Z.max peak (Z.max (Ledger.lsum Lam + 56 * (cap2R cap - cap))
    (Ledger.lsum Lam'))) (cnt + 2) fail ran most own;
  tgrP7_lsum : Ledger.lsum Lam' = Ledger.lsum Lam + PjGrammar.held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap);
  tgrP7_kb : bytes_at W' mem' k' kb;
  tgrP7_kvis : prhReader_vis W' mem' k' (56 * cap2R cap);
  tgrP7_yb : bytes_at W' mem' y' yb;
  tgrP7_yvis : prhReader_vis W' mem' y' (8 * cap2R cap);
  tgrP7_hdr : pj_hdrR segs (rdW W' mem') v ty num str k' y' n (cap2R cap);
  tgrP7_slots : pj_slots_atR (prh_lin Lam') ty k' y' n (cap2R cap);
  tgrP7_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
    (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [true; true]));
  tgrP7_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [true; true]) -> exists hist',
    PresetRoomPos.iface_room_pos sm x os (i + length (prhPg_evs (ty =? 6)%Z n cap [true; true]))%nat H0 hist' S') }.

Lemma tgrP_R7_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z)
    (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte),
  tgrP_A7 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ->
  exists k' y' Lam', tgrP_R7 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W'
      regs' mem' k' y' Lam'.
Proof.
  intros most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' H. destruct
      H as (H0 & H1 & H2 & H3 & H4 & k' & y' & Lam' & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16
      & H17 & H18 & H19).
  exists k', y', Lam'.
  exact {| tgrP7_eq := H0; tgrP7_notchosen := H1; tgrP7_object := H2; tgrP7_notchosen1 := H3; tgrP7_ret := H4;
      tgrP7_kmin := H5; tgrP7_kalign := H6; tgrP7_ymin := H7; tgrP7_yalign := H8; tgrP7_swap := H9; tgrP7_ledger :=
      H10; tgrP7_lsum := H11; tgrP7_kb := H12; tgrP7_kvis := H13; tgrP7_yb := H14; tgrP7_yvis := H15; tgrP7_hdr := H16;
      tgrP7_slots := H17; tgrP7_live := H18; tgrP7_pos := H19 |}.
Qed.

Lemma tgrP_A7_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (v ty num str kids keys n cap : Z)
    (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (k' y' : Z) (Lam' : list (Z * Z)),
  tgrP_R7 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' k' y' Lam'
      ->
  tgrP_A7 most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem'.
Proof.
  intros most own ly S Hp v ty num str kids keys n cap kb yb Lam peak cnt fail ran ly' S' Hp' W' regs' mem' k' y' Lam'
      HR.
  refine (conj (tgrP7_eq HR) (conj (tgrP7_notchosen HR) (conj (tgrP7_object HR) (conj (tgrP7_notchosen1 HR) (conj
      (tgrP7_ret HR) _))))).
  exists k', y', Lam'.
  exact (conj (tgrP7_kmin HR) (conj (tgrP7_kalign HR) (conj (tgrP7_ymin HR) (conj (tgrP7_yalign HR) (conj (tgrP7_swap
      HR) (conj (tgrP7_ledger HR) (conj (tgrP7_lsum HR) (conj (tgrP7_kb HR) (conj (tgrP7_kvis HR) (conj (tgrP7_yb HR)
      (conj (tgrP7_yvis HR) (conj (tgrP7_hdr HR) (conj (tgrP7_slots HR) (conj (tgrP7_live HR) (tgrP7_pos
      HR))))))))))))))).
Qed.

Local Unset Implicit Arguments.

End c.
