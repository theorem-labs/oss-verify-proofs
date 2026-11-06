(* This file carries the kit's text of the re-hiding move for its two crossing texts
   (`PRIMED-SHAPES.md (sha256 9e4880d18317; internal record)` sec. 2.H1, 2.H2). Written by the recursive-reader author; the kit, under the kit owner, is the TEXT RECORD of these two
   statements (`OWNERS.tsv (sha256 b47a0f6ce18d; internal record)`; the walk-kit lead's 23:53Z text-owner ruling), and only their conclusions change here:
   tparse_value_specX and tparse_items_specX conclude SRr' segs RZ_cf and keep fpostWFbm, which is AFTER-FREE-ONLY and
   already at wle' (PRH_Base.v). tpvP_Q_check and tpiP_Q_check match the primed conclusion.
   The unit owner's ruling C2 (2026-10-31 04:19Z) struck the scratch notice that stood here, by a
   comment-only edit that keeps the header at 7 lines, so every line after it keeps its number. *)
(* fuzz_preset, program part (the recursive-reader slice): the ASan contract TEXTS of the reader's recursive unit, parse_value
   (image A 0x85f10, 373 instructions; image B 0x8637c, 371) and parse_items (A 0x87298, 429). Written by the recursive-reader author.
   The kit owner ruled that this author writes them; the other reader texts are the kit's lib/A/PRH_FnReader.v.

   RECORD: the walk-kit lead ruled (23:53Z, as text owner) that this file is the record, carrying the UNION of the premises two
   drafts justify: this one and the image-B parse_value walk's (the B' walker, commit a34197aa5760,
   lib/A/PRH_FnPValue.v), whose additions are folded in BY NAME (prhPv_gtrace, prhPi_gtrace, prhPv_rk_ev, prhPv_rk,
   prhPv_node's conjuncts; the image-B parse_value walk's LIVE_rd was RETIRED 2026-10-30 by the kit owner's entry-sum ruling, rd_room's live
   conjunct being PRH_Base.prh_live_evs). Kept from this draft: frm_zero at entry, the (lo, hi) footprint rd_fp, the window
   fwin e, rd_ledger_move, and d as the FIRST parameter.

   HISTORY: the first version (828bf5b332d) concluded in the plain post fpostF, which the S6 walk measured
   FALSE: ajournal_x keeps every real-stack byte above the entry sp, and the cursor q is in pj_parse's own frame (A
   0x85e60 `mv a0, sp`, B `addi a0, sp, 8` 0x86330). Both texts are in the kit's CALLER-WINDOW form (PRH_Base.v fwin /
   fpostWF): the journal runs at (STK + e) (spZ regs + e) with the caller granting e bytes above the entry sp; the
   written caller cells are FP, every other byte of [sp, sp + e) keeps its value; FLOAT form because both functions
   reach musl strtod.

   WHAT THEY SAY, from preset_file.c (omx-clap-core 246923f04ac0) and the rebuilt images' bytes: parse_value at nesting
   d reads one JSON value at the cursor into the zeroed node v; parse_items reads the members of an array (o = false) or
   an object (o = true). The model is the PURE grammar of lib/Spec/PjGrammar (jr_value / jr_items over the strtod model
   ReaderRes.jr_strtod, the one name the texts use; PRH_Reader.prh_jr_strtod has its body and stays the name of the
   granted-trace helpers), which returns the tree, the allocation trace and the unread rest. Outcomes follow
   PRH_Base.prh_oks: a failure is fuzz_alloc_fail's chosen failure or the class-full allocator's REFUSAL, which sets
   g_ran_out when its request is at most g_most and raises g_peak in every case (rd_ledger_move).
   ROOM, REQUEST AND LIVE ROOM are stated over the GRANTED run (every allocation succeeds, ok = []), as plain room_run
   (parse_value_c.v:40) and the kit's pj_parse prhPj_ptrace (PRH_FnPj.v:252) take them, so pj_parse composes by arithmetic;
   the live room is stated AT EACH EVENT of that run (PRH_Base.prh_live_evs; rd_room's note).
   FAMILY (the kit owner's condition 4, 2026-10-29 ~17:25Z): both texts are READING-CHAIN: POST-IMPLICATION form, no
   entry position, no entry run premise. They call only post-form texts (PRH_FnReader.v's parse_string, grow,
   literal and skip_ws, and each other; PRH_FnAlloc.v's fuzz_malloc / fuzz_free / fuzz_realloc; the runtime calls
   state no position). The writer / tx / round-trip / crcs / as_written texts (ENTRY-keyed list plus the rp_on entry
   spelling) may call them, as may every post-form text.
   THE POSITION (the form is stated once, in PRH_FnReader.v's header): the post binds the instance's outcomes ok and
   trace tr (jr_value / jr_items under ok) and states, beside the unconditional functional post,
     forall sm x os i H0 hist, iface_room_pos sm x os i H0 hist S -> prh_run_at sm x os i (rd_hevs tr) ->
       exists hist', iface_room_pos sm x os (i + length (rd_hevs tr)) H0 hist' S'
   the EXACT advance with no agreement premise: the caller picks the model run after the call to match ok, so
   prhReader_agree (AGREE-PREFIX) is no longer used here. SUPPLY: a caller's list is rd_hevs of its own trace,
   which holds the callee's tr after the earlier callees' traces; PRH_FnReader.prhReader_run_at_mid (from
   PRH_Base.prh_run_at_app_iff) gives the callee's run premise at the position the earlier callees' advances name.
   THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS; the kit owner's ruling ~18:5xZ): each post also states,
   under the same run quantifier, that at a model run whose next events are the ALL-GRANTED trace's (prhPv_gtrace /
   prhPi_gtrace), every allocation among them a CONSUMER event (PRH_Base.prh_cons_from), with no injected failure in
   the call's window (`fail < cnt \/ cnt + calls gt <= fail`), the instance's (res, tr) IS the all-granted run's,
   g_ran_out is unchanged, and S' is the position at the granted advance. The walk derives it from its callees' own
   outcome clauses (parse_string's and grow's refused-arm exclusions, the leaves' res <> 0).
   THE LIVE COUNTS AT THE INNER CALLS (PRH_FnReader.v's header; the K1-batch walk-kit lead's ruling R1 as amended, 2026-10-29): the
   entry premise is the PEAK of the secondary and class-24 counts along the ALL-GRANTED events, rd_hevs of
   prhPv_gtrace / prhPi_gtrace, from the entry's live requests (PresetRun.pkR); it replaces counts_of_room_pos_rl at
   every inner allocator call. The post's chaining fact is EXACT: the live requests after the call are the entry's
   moved by rd_hevs tr (Permutation with PresetReqAt.hlive_from). It follows from rd_blocks_move / rd_ledger_move
   (the new blocks D, sized by lszR tr) at cf_head = PresetReqAt.HEAD, because a reader trace frees and grows only
   blocks it made itself: okf [] (rd_hevs tr) is PresetReqAt.NB_fuel (jr_value, by its jrv) and PresetReqAt.NB_cont
   with NB_fuel's second half (jr_items), both Qed (Section Closed at sm := prh_jr_strtod), so PresetReqAt.hlive_okf
   gives hlive_from s (rd_hevs tr) = hlive (rd_hevs tr) ++ s, and hlive (rd_hevs tr) is lszR tr shifted by HEAD.

   PREMISES and why each is there, measured unless marked:
   - frm_zero (fp_csr fx): the parse_items proof walk measured fpostWF unprovable without it on every arm that does not reach strtod
     (fx' = fx there). The kit states it the same way (PRH_FnEx.v:312, PRH_FnCheck.v:440 ck_frm0).
   - the frames bound `length (frames S) + S (MAXD - d) <= fs_frames 0`: the parse_value proof walk measured the class-full arm of the
     ASan frame UNPROVABLE (the code builds the frame on the real stack and writes non-zero shadow there, which ARcf's
     ARmcf.amc_zshadow keeps at zero). Only parse_value takes a fake frame in the reader (__asan_stack_malloc_0; the
     image's callee lists show no stack_malloc in parse_items, parse_string, literal, hex4, put_utf8 or grow), so the
     deepest path from parse_value at d holds Nat.succ (MAXD - d) of them, and from parse_items at d (which takes no
     frame itself and calls parse_value at d + 1) MAXD - d. pj_parse's own premise (+ DOC_D) gives it at d = 0.
     The count is written Nat.succ, not S: S is the allocator state in these texts.
   - ROOM IS AN INVARIANT (the kit owner's ruling, kit b7722372682): room_live_cf S on entry (PRH_Base's PrhRoomLive, the
     non-primary room, owned by the allocator-model owner) and room_live_cf S' in every post arm; no margin, no room_cf. The history: plain ROOM_cf
     does not give room at a second allocator call (a successful secondary realloc can raise st_sec_arr to its cap).
   - the two realloc universe premises: grow reaches fuzz_realloc.
   - maxrun tb < 2 ^ 30: plain parse_value_c.v:33.
   NAMED GAPS: (G6) closed - ROOM_cf_k, RK_* and room_kept are the allocator-model owner's frozen YGcfRoomKeep (06d751f40e3d), which
   the kit binds since 1cf840fa800; the PrhNames stand-in class is gone.
   (G7) The node's place is prhReader_at (a live harness block, a live allocator block, a live fake frame, or the
   granted window). (G8) The failure post frees to depth MAXD - d; the Pj part instantiates pj_free's depth at MAXD.
   (FREEORD-NONE, #102) Both posts state, in each arm, pj_free's ORDER LIST of the tree left in the node (complete or
   partial) against the model's reader-side list (prhPv_frees / prhPi_frees below), so pj_parse's pj_free (out) on its
   refused path closes by citation.
   (V3, the image-B parse_value walk's) the three .rodata words literal compares must be kept_at and cstr_ok at the call (cstr_ok carries
   YGcfStr.amem_range8 w (len + 1) since kit cc19dfc36d7; their image addresses give its low arm): an image fact the
   walks carry as a named Section hypothesis. Its cstr_ok half is retired (2026-10-29): PRH_Base.cstr_ok_ro, the image
   premise decided by YGcallRoStr.ro_str_check / ro_str_check_ok (vm_compute).

   REFUTED, do not re-propose (the kit owner 07:08Z): the rd'-quantified entry-chain premise `forall rd', (agrees outside
   rd_fp q v) -> exists ch', achain ly rd' (spZ regs) (s0Z regs) ch' /\ ..` - on image B, the image-B parse_items walk showed (parse_items ->
   parse_value, B 0x87d94, s0 = q + 16 at B 0x87ab8) that the chain's first frame reads [q, q+8), inside rd_fp, so
   rd' := view except q is unconstrained there and no chain exists; the image-B parse_value walk showed q - 16 = sp0 - 8 is parse_value's own
   ra slot, written at B 0x86384, outside rd_fp. The entry chain is now stated plainly at the entry view (implied by
   fpre's afn_pre_x), and chain independence at each call is carried by the kit's closure and the cursor words (prh_univ_closure + prh_cur_entry)
   at the call state.
   THE HULL BUDGET (route (b) of the allocator hull premise; lib/Spec/PresetHullBudget.v,
   PRH_FnAlloc.v's header): both texts reach the allocator with no position, so each takes `hull_budget S Eg` over
   its ALL-GRANTED events Eg (rd_hevs of prhPv_gtrace / prhPi_gtrace, the list its room counts name) and pays its
   callees' budgets from it; each post states `hull_used S S' Eg` with the same Eg.
   Statements only; no proof (rule 24: no function proved). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YP0b YPsym YC4aP YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun PresetRoom
  PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
(* the re-hiding move's SRr' and wle' (YA0nH) and preset's zone (YGcfRehidePost.RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Local Open Scope Z_scope.

(* prhPv_rk_ev / prhPv_rk and the granted runs prhPv_gtrace / prhPi_gtrace are the kit's lib/A/PRH_Charge.v (ONE copy,
   the image-B parse_value walk's bodies, shared with every reader text's room premise since kit 38953abe503); not redefined here. *)

(* pj_free's ORDER LIST of the tree a reader call leaves in its node (FREEORD-NONE, the #102 kit; the B' walker's
   pj_parse measurement on pj_parse's refused path, commit 8a088cd72fac
   lib/B/Prog/pj_parse_seg_c2ref.v: no text tied the refused tree's order list to the model's HBulk). The list is the
   MODEL's own, PresetReqAt.jfv / jf_cont / jfl (PresetReqAt.v:251-294, the #102 model of record), at the grammar
   call's own fuel and outcome list: the complete tree after a value that returned, the PARTIAL tree after a refusal
   (the path of open containers, each with its completed slots, the refused value's partial slot - C :246 counts it -
   and its arrays as they are then). It is keyed on the READER's sizes (a string or key block is its escaped input
   span, src/preset_file.c:127), never on fo / tblk. At d = 0 over pj_parse's whole text, prhPv_frees 0 x ok IS
   PresetReqAt.pj_frees ReaderRes.jr_strtod ok x (PresetReqAt.v:297) by unfolding, so pj_parse's walk meets the
   HBulk that parse_evs emits on a refusal by citation. parse_value's list takes jr_value's fuel (PjGrammar.v:319),
   parse_items' takes jr_items' fuel and form (PjGrammar.v:321-322, jf_cont mirrors jr_cont). A walk that composes
   them across a nested call meets the same fuel shift as the grammar (PjGrammar.fuel_mono / jr_items_fuel); for jfv /
   jfl that shift is now PROVED and CITED, not owed: PresetFreeFo.jf_fuel_mono (:489), jfv_fuel (:528) and
   jf_items_fuel (:531), the P8 owner's lib/Spec/PresetFreeFo.v blob 75c11ade43e4 at commit
   28379aac52c (cb3 rc=0, Print Assumptions closed), carried by path in this batch. The note that this was OWED to the
   walk is gone with it, and the B' walker drops its three named image-B parse_items hypotheses for the same facts. *)
Definition prhPv_frees (d : nat) (x : list Z) (ok : list bool) : list Z :=
  PresetReqAt.jfv ReaderRes.jr_strtod (Nat.succ (2 * length x)) d x ok.
Definition prhPi_frees (d : nat) (o : bool) (x : list Z) (ok : list bool) : list Z :=
  PresetReqAt.jf_cont (PresetReqAt.jfl ReaderRes.jr_strtod (2 * length x + 2)) d o x ok.

(* g_fail_at after k harness allocations from g_count = cnt (plain ReaderRes.fail_after) *)
Definition fail_afterR (cnt fail : Z) (k : nat) (fail' : Z) : Prop :=
  (cnt <= fail < cnt + Z.of_nat k -> fail' = SIZE_MAXZ) /\ (~ (cnt <= fail < cnt + Z.of_nat k) -> fail' = fail).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the caller cells: the cursor's p field and depth word, and the node (the kit's FP convention, (lo, hi)) *)
Definition rd_fp (q v : Z) : list (Z * Z) := [(q, q + 8); (q + 16, q + 20); (v, v + 56)].

(* the node the caller hands the reader: 56 zeroed, writable, 8-aligned bytes where plain rplace allows (G7), outside
   the runtime's own bytes and the function's stack window, addressable for the instrumented stores (the image-B parse_value walk's
   prhPv_node, plain parse_value_c.v:35-38) *)
Definition prhPv_node (STK e : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (Lam : list (Z * Z)) (v : Z) : Prop :=
  4096 <= v /\ v mod 8 = 0 /\ pj_rwR segs (rdW W mem) v /\ pj_zeroR segs (rdW W mem) v /\
  prhReader_at B ly S Lam regs e v 56 /\ amem_range v 56 /\
  (forall a, v <= a < v + 56 -> ~ aowned B ly S a /\ ~ (spZ regs - STK <= a < spZ regs)) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 56.

(* the ledger moves of one reader call, from the pure trace tr. THE REFUSAL (#102's rule, PRH_Base.v prh_oks /
   prh_refused_peak; the kit owner's ruling, 2026-10-29): g_ran_out is keyed on each call's request, prh_ev_reqs tr,
   against g_most, and g_peak takes the refusal's live count plus request, read off the ALL-GRANTED trace gt
   (prhPv_gtrace / prhPi_gtrace): a refused grow's EFail n carries no old size. COUNTEREXAMPLE to the form without
   them (any refusal set ran' = 1; peak' from hpeakR alone, which counts EFail as 0): parse_value on the JSON string
   ab (bytes 34 97 98 34), ok = [false], cnt <> fail, Lam = [], peak = 0, most = 2, ran = 0: fuzz_malloc (3) is
   refused, g_peak = 3 and g_ran_out stays 0, where the old text said peak' = 0 and ran' = 1. *)
Definition rd_ledger_move (Lam : list (Z * Z)) (peak cnt fail ran most : Z) (ok : list bool) (gt tr : list ev)
  (D : list (Z * Z)) (Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) : Prop :=
  prh_oks ok cnt fail (calls tr) (prh_ev_reqs tr) most ran ran' /\
  cnt' = (cnt + Z.of_nat (calls tr)) mod 2 ^ 64 /\
  fail_afterR cnt fail (calls tr) fail' /\
  Permutation Lam' (D ++ Lam) /\
  Permutation (map snd D) (map Z.of_nat (lszR tr)) /\
  Z.of_nat (length D) = nliveR tr /\
  peak' = Z.max (Z.max peak (Ledger.lsum Lam + hpeakR tr))
    (prh_refused_peak ok cnt fail (calls tr) (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds gt))).

(* what a reader call does to the allocator's blocks and frames (the image-B parse_value walk's post conjuncts; parse_items calls
   parse_value again in its loop and needs them): the subtree's blocks are new, the allocator gained exactly them, the
   fake frames are as before, and the trace's peak is bounded by the text *)
Definition rd_blocks_move (ly : alayout) (S : astate) (ly' : alayout) (S' : astate) (D : list (Z * Z))
  (tr : list ev) (rest : list Z) (d : nat) : Prop :=
  (forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) /\
  Permutation (ablocks B ly' S') (prhReader_ab D ++ ablocks B ly S) /\
  Permutation (frames S') (frames S) /\
  hpeakR tr <= 224 * Z.of_nat (length rest) + 512 * Z.of_nat (PjGrammar.MAXD - d).

(* the premises every reader call shares (STK is the function's frame bound, for the node's window clause) *)
Definition rd_pre (STK : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (Lam : list (Z * Z)) (peak cnt fail ran most own e q text len p : Z) (d : nat)
  (tb : list Z) (v : Z) : Prop :=
  frm_zero (@YK11.fp_csr fx) /\
  prh_malloc_univ B /\
  (* the realloc pair is code-only (fuzz_realloc holds n in s0: empty chain): the FIXED part, explicitly *)
  In [cf_pc_realloc_ra0] (u_fix (as_universe B)) /\
  In (prh_trace cf_pc_realloc_ra0 pi_ret_realloc []) (u_fix (as_universe B)) /\
  pj_in_okR segs (rdW W mem) q text len p (Z.of_nat d) tb /\
  fwin ly W regs mem e /\ spZ regs <= q /\ q + 24 <= spZ regs + e /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 24 /\
  src_rd W mem text tb /\ prhReader_home B ly S Hp Lam text len /\
  Z.of_nat (PjRoundTrip.maxrun tb) < 2 ^ 30 /\
  prhPv_node STK e ly S W regs mem Lam v /\
  (q + 24 <= v \/ v + 56 <= q) /\
  (* the text lies apart from the node WHEN THERE IS A TEXT (the B' walker, matching tpj_parse_specX's guard): at
     len = 0 parse_value reads no text byte, and the unguarded form is underivable at pj_parse's call B 0x86338 *)
  (0 < len -> text + len <= v \/ v + 56 <= text) /\
  (* the node is NOT in the granted real-stack window (the items-element walk's counterexample: with v in the window below q, the chain
     from q reads the node's cap / n words as ra / next fp, so a grow that rewrites cap changes the chain's spine). Every
     caller passes a heap block, an allocator block or a live fake-frame node (pj_parse's out node, parse_items' kids
     slot), so this removes only prhReader_at's window case, which no caller uses. *)
  (v + 56 <= spZ regs \/ spZ regs + e <= v) /\
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own /\
  (d <= PjGrammar.MAXD)%nat /\
  cnt + 2 * Z.of_nat (length (rest_atR tb text p)) + 2 < 2 ^ 64 - 1 /\
  (* THE READER'S TEXT ENDS STRICTLY BELOW THE CEILING (the B' walker's proposal, the kit owner's ruling 2026-10-30, on
     the S1 owner's strict-harness answer: the harness buffer's end plus its ASan redzone is at most alloc_ceiling).
     This is SRC-CEIL's cost after the + 8 relaxation of src_rd: astk_ok is NON-STRICT, so relaxing to <= would
     let the byte at text + len be a stack word. Reader text only. APPENDED at the END on purpose: consumers
     destructure rd_pre positionally (the B' walker's eight B' sites), and an appended conjunct moves only the last
     name. *)
  text + len < YM05.alloc_ceiling.

(* the room of one call over its granted trace gt: margin room, the request bound and the live room. The request bound
   is the LARGEST SINGLE request (PRH_Charge.prh_maxreq), not the trace's peak: the peak is a high-water mark of live
   bytes and charging it as one request is FALSE at full size (the kit owner and the B' walker: 710,842,546 against cf_malloc_max
   535,822,336 on an accepted 3 MiB input), which made both texts vacuous on large inputs.
   THE LIVE ROOM IS PER EVENT (the kit owner's entry-sum ruling, 2026-10-30 00:36Z by its `date -u`; the
   sources are at PRH_Base.prh_live_evs): at EACH event of the call's own all-granted run, PresetReqAt.rd_hevs gt, the
   live bytes THERE plus that event's SINGLE request are at most LIVE_MAX. It REPLACES
   `blocks_bytes S + LIVE_rd gt <= LIVE_MAX` (LIVE_rd gt := 2 * hpeakR gt + cf_head * (calls gt + 1)), which ADDED THE
   ENTRY LIVE BYTES TO THE CALLEE'S OWN MAXIMUM, although the reader frees and reuses (a grow frees the block it
   replaces) and at each allocation event the run is POSITIONED. A REPAIR, NOT A RELAXATION: NO PROOF USES THE SUM
   FORM TODAY (the S1 owner: no consumer), and it is NOT DISCHARGEABLE - the ruling's pretty read-back figure 84.6e9 is
   a SUM OF MAXIMA, not a peak (the plain bounds hpeak <= 224 * L + 16384 and calls <= 2 * L + 2 of PRH_FnPj.v:248-249
   at the pretty text of a 3 MiB input, L = 56 * 3 MiB - 54: 2 * (224 * L + 16384) + 16 * (2 * L + 3) =
   84,557,175,536, above LIVE_MAX = 2 ^ 34), where the measured whole-run peak is 8.30e9 and the proved bound 1e10.
   Wherever the sum held it implies this form (at cf_head = HEAD, CFHEAD-16), so pj_parse's sum LIVE_pj_parse
   bounds parse_value 0's conjuncts, and a recursive caller hands on a segment of its own list. gt keeps the chosen
   failure's allocation (every allocation granted), so the room is asked there too, more than the guarded leaf needs
   (fuzz_malloc's live premise is under cnt <> fail, PRH_FnAlloc.v:303). THE DISCHARGER IS NAMED AND PROVED: the live-bytes owner's
   entry_sum_ok / entry_sum_closed (M1 + M2 + M6), proved: PresetLiveBytes.v:1751 entry_sum_ok, :1827 entry_sum_closed. *)
Definition rd_room (S : astate) (gt : list ev) : Prop :=
  room_live_cf S /\
  prh_maxreq gt + cf_head < cf_malloc_max /\
  prh_live_evs S (PresetReqAt.rd_hevs gt).

(* ---- parse_value: a0 = the cursor q, a1 = the node v, at nesting d ---- *)

(* It takes its class-0 fake frame, skips white space, dispatches on the first byte and fills v: a string
   (parse_string), an array or an object (parse_items with o = false / true), a literal (literal), or a number (the
   token scan, fuzz_malloc of the token bytes + 1, the checked memcpy, strtod, and the block kept as the node's
   string); it releases the frame inline and returns 0 or -1. *)
Definition tparse_value_specX (d : nat) (CTX : list (list Z)) (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall ly S Hp W regs mem md ch e q text len p (tb : list Z) v Lam peak cnt fail ran most own,
  fpre B ARx (STK_parse_value d) ly S Hp W regs mem md ch ->
  (* the memory overlay is normal at entry (the kit's spelling, agreed 10:09Z and ruled by the kit owner): strtod's only callers
     are ex_value and parse_value, and all ten kit texts whose subtree reaches strtod carry this premise in exactly this
     form (here :284, :694; PRH_FnEx.v:311, PRH_FnPj.v:616, PRH_FnCheck.v:617/1079/1321/1766/1966/2334). parse_value reaches strtod
     through jr_strtod, parse_items through parse_value. The POST-side keep is in the post: fpostWFbm wraps Q in fQmn
     (PRH_Base.v:1655, :1469); the outer keep is assembled once per function from YSRrMemnorm's runner lemma plus the per-call
     keeps, never threaded through a segment lemma. A cut must hand this on (the memnorm-runner author's finding: SEG_N starts after
     segment A has run, so an entry conjunct alone does not reach it). *)
  YAkMemnorm.memnorm segs mem ->
  In (raZ regs :: spine ch) CTX ->
  (* the call-graph universe closure, and the cursor chain's stop word named at this entry so the walk meets
     parse_string's (and parse_items') call-state chain premises (the kit at 4eb03b7b7e8) *)
  prh_univ_closure B CTX0 ->
  prh_cur_entry W mem regs q ->
  (* THE CURSOR SET CW (PRH_Base.prh_cw_entry), IN THE SLOT prh_cur_entry's sp - 8 arm VACATED when the run-word
     lists went: the trace each cursor free this subtree makes is in CW, or its word is the code word of
     pj_parse's `jal parse_value` (image A', where the trace is FIXED and costs no room). prh_cur_low and
     prh_cur_entry's sp - 16 arm, above, are what make that trace exactly [pc0; r; w], so |CW| = 2. *)
  prh_cw_entry B CW W mem regs q ->
  (* the entry call chain survives any change of the caller cells the reader writes, up to its spine (the image-B parse_items walk proved the
     fixed-ch form FALSE at image B's parse_items -> parse_value call, B 0x87d94, where s0 = q + 16 and the chain's first
     frame reads the cursor's p word; the kit owner's 06:39Z ruling). Earlier: the entry call chain reads no caller cell the reader writes (the parse_value proof walk's measurement: the walk stores the cursor's p
     word, and at d > 0 the entry s0 is parse_items' own, next to q; a cut chain meets it for free, and pj_parse
     discharges it from its frame layout since q lies below its entry sp) *)
  (exists ch', achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch' /\ spine ch' = spine ch) ->
  (* PARTITIONED (the kit owner's 06:39Z ruling): below spZ regs + 16 the callee builds the chain at q from its own two
     saved words; at or above it the caller supplies one (the slice walker proved the chain does not transfer below that bound).
     The chain at the CURSOR, which parse_string's entry-chain premise needs at every nested call (the kit owner's 06:12Z ruling,
     measured by the S4 walk): from pj_parse the cursor is in the caller's frame right at the callee's entry sp
     (image A `mv a0, sp`: q = spZ regs; image B `addi a0, sp, 8`: q = spZ regs + 8, which the image-B pj_parse walk proved makes a
     `q = spZ regs` form false on B), so the first disjunct covers both and the record at fp = q straddles the callee's
     own saved ra / s0; from a reader caller it is the caller's chain at q, and
     achain is monotone downward in sp *)
  ((spZ regs <= q < spZ regs + 16) \/
   (spZ regs + 16 <= q /\ exists ch', achain ly (aview segs (w_H W) mem) (spZ regs) (prh_s0 F_parse_string q) ch')) ->
  getr regs 10 = w64 q -> getr regs 11 = w64 v ->
  rd_pre (STK_parse_value d) ly S Hp W regs mem Lam peak cnt fail ran most own e q text len p d tb v ->
  rd_room S (prhPv_gtrace d (rest_atR tb text p)) ->
  (* THE WILD BUDGET (the room count of P''): every wild site below this call is a cursor free, whose trace is in
     CW, so the room is stated against the SET CW with NO fresh slot - a recursive call hands on the same CW and
     the same k = 0, which is why the recursion through parse_value / parse_items composes. *)
  YCbqGwild.wild_room (as_universe B) CW 0 (st_depot S) ->
  (* THE LIVE COUNTS AT THE INNER CALLS (the header; PRH_FnReader.v's header; they replace counts_of_room_pos_rl): the
     secondary and class-24 counts at every state along the ALL-GRANTED events rd_hevs (prhPv_gtrace ..), from the
     entry's live requests, so an inner call at a state with more live blocks than the entry is covered. Position-free;
     no cnt / fail guard *)
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* THE HULL BUDGET (the header): room for the all-granted events *)
  PresetHullBudget.hull_budget S (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) ->
  Z.of_nat (length (frames S)) + Z.of_nat (Nat.succ (PjGrammar.MAXD - d)) <= fs_frames 0 ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.H1); fpostWFbm is already at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_parse_value) regs mem md)
    (fpostWFbm B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_value d) e (rd_fp q v) regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' =>
       exists (ok : list bool) res tr okr D Lam' peak' cnt' fail' ran',
       jr_value ReaderRes.jr_strtod d (rest_atR tb text p) ok = (res, tr, okr) /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own /\ room_live_cf S' /\
       (* THE HULL USE (the header): at most the entry budget's list *)
       PresetHullBudget.hull_used S S' (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) /\
       (* the live requests move by the events the instance made, E = rd_hevs tr (the header) *)
       (* CFHEAD-16, NOT GUARDED (the kit owner's ruling D1; the head-size census): rs_live holds the INSTANCE sizes
          (user + cf_head), the model's events HEAD-sized; equal exactly when cf_head = PresetReqAt.HEAD, which the walk
          takes as its Section hypothesis PRH_Base.prh_head16 (reflexivity at CfParams_preset). *)
       Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
         (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetReqAt.rd_hevs tr)) /\
       (* THE POSITION TRANSFER (post-implication form): THE EXACT ADVANCE by the events the instance made, at any
          model run and position the caller picks (no agreement premise: the caller picks the run to match ok) *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs tr) ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs tr))%nat H0 hist' S') /\
       (* THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS): at a model run and position whose next events
          are the ALL-GRANTED value's (rd_hevs (prhPv_gtrace ..)), every allocation among them a CONSUMER event
          (PRH_Base.prh_cons_from), with no injected failure in the value's window, the value GRANTED: g_ran_out
          unchanged, the instance's (res, tr) IS the all-granted run's, and S' is the position at the GRANTED advance *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) ->
          PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) ->
          (fail < cnt \/ cnt + Z.of_nat (calls (prhPv_gtrace d (rest_atR tb text p))) <= fail) ->
          ran' = ran /\ fst (jr_value ReaderRes.jr_strtod d (rest_atR tb text p) []) = (res, tr) /\
          exists hist', PresetRoomPos.iface_room_pos sm x os
            (i + length (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))))%nat H0 hist' S') /\
       (* THE OUTCOME OF AN INJECTED READING (GUARDED): at a model
          run and position whose next events are the value's under the MODEL's grant list with the chosen failure at
          its call fail - cnt (PresetReqAt.okk), every allocation among them a CONSUMER event
          (PRH_Base.prh_cons_from), with the chosen failure INSIDE the value's window, no call was REFUSED: every
          failed outcome the instance met is the chosen one. The run premise names the MODEL's grant list, not the
          outcomes ok the post binds. tpj_parse_specX's conjunct of the same name IS this one at d = 0 over the whole
          text (PRH_FnPj.v, after ITS OUTCOME): pj_parse's refused path cites this one, which THE OUTCOME above
          cannot give - it speaks only of the ALL-GRANTED list, while prh_oks ALLOWS a real refusal (PRH_Base.v
          :946-950) and prh_granted FORBIDS one (:984-985). The walk derives it per call: before the chosen failure
          the model's list agrees with the all-granted one, so each callee's REFUSED-arm exclusion applies
          (parse_string, grow: PRH_FnReader.v) or the leaf's `cnt <> fail -> res <> 0` does (PRH_FnAlloc.v); at the
          chosen call the refusal IS the chosen one; after it the reading makes no call. *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (jr_value ReaderRes.jr_strtod d
            (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
          PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (jr_value ReaderRes.jr_strtod d
            (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) ->
          cnt <= fail < cnt + Z.of_nat (calls (prhPv_gtrace d (rest_atR tb text p))) ->
          PRH_Base.prh_granted ok cnt fail (calls tr)) /\
       rd_ledger_move Lam peak cnt fail ran most ok (prhPv_gtrace d (rest_atR tb text p)) tr D Lam' peak' cnt' fail'
         ran' /\
       rd_blocks_move ly S ly' S' D tr (rest_atR tb text p) d /\
       (* the live room handed on to the next call (the items-element walk's finding: rd_room's live conjunct cannot be re-established
          after a call otherwise); blocks_bytes counts allocator requests, each a user request plus the head: prh_held *)
       blocks_bytes S' <= blocks_bytes S + prh_held tr /\
       (* the subtree's blocks are exactly the trace's net bytes, so a caller composing rd_ledger_move across this
          call can re-associate the peak (the items-element walk's finding: Permutation of the sizes alone does not give it) *)
       Ledger.lsum D = PjGrammar.held tr /\
       match res with
       | Some (t, r) =>
           getr regs' 10 = w64 0 /\
           (* THE TREE'S FREE ORDER (FREEORD-NONE; tparse_noting_specX's shape, PRH_FnCheck.v): for every depth bound
              n >= depth t, pj_free's order list F of the node's tree carries the model's reader-side list prhPv_frees
              at this call's (d, rest, ok), IN ORDER. pj_parse's walk takes it at n := DOC_D on its refused path when a
              non-blank tail follows the value (src/preset_file.c:301-307: the tree is complete and pj_free (out) frees
              it; PresetReqAt.parse_evs emits HBulk (pj_frees ok tl), which is prhPv_frees 0 tl ok), with depth t <=
              MAXD - d from PjGrammar.jr_value_depth. CFHEAD-16: the model's list carries PresetReqAt.HEAD. *)
           (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
              exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n v D F /\
                map (fun b => snd b + cf_head) F = prhPv_frees d (rest_atR tb text p) ok) /\
           pj_in_okR segs (rdW W' mem') q text len (text + len - Z.of_nat (length r)) (Z.of_nat d) tb /\
           pj_nodeR segs (rdW W' mem') (prh_lin Lam') v t D /\
           (* CAP (PRH_Reader.pj_ncapR, its comment has the source lines): every array / object node of the tree
              has header cap = PresetReqAt.ncap of its count (v starts zeroed and parse_items grows cap from 0 by
              gcap); tpj_parse_specX's Some arm cites it at d = 0. pj_nodeR alone gives only n <= cap. *)
           pj_ncapR segs (rdW W' mem') v t /\
           Ledger.lsum D <= 224 * (Z.of_nat (length (rest_atR tb text p)) - Z.of_nat (length r))
       | None =>
           getr regs' 10 = w64 (-1) /\
           (* THE PARTIAL TREE'S FREE ORDER (FREEORD-NONE, the B' pj_parse walk's open site): for every depth bound
              n >= MAXD - d (the depth the partial path can reach: pj_fdR's below), pj_free's order list F of what the
              refused call left in the node carries prhPv_frees at this call's (d, rest, ok), IN ORDER - possibly []
              (nothing allocated, or the first allocation refused). pj_parse's walk takes it at n := DOC_D for its
              pj_free (out); the F = [] case is PRH_FnPj.prhPj_free_evs_bulk (the model's HBulk [] stepped over). *)
           (cf_head = PresetReqAt.HEAD -> forall n, (PjGrammar.MAXD - d <= n)%nat ->
              exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n v D F /\
                map (fun b => snd b + cf_head) F = prhPv_frees d (rest_atR tb text p) ok) /\
           pj_in_afterR segs (rdW W' mem') q text len (Z.of_nat d) 33 /\
           pj_fdR segs (rdW W' mem') (prh_lin Lam') (PjGrammar.MAXD - d) v D
       end)).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tparse_value_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
    cite the
   lemma). ADDITIVE: the text above is unchanged. tpvP_Q IS the text's post (tpvP_Q_check fails to build if the two ever
   differ); tpvP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas build the post
   from them. A consumer that reads and builds the post through these is not broken by the NEXT appended conjunct. ====
       *)

Definition tpvP_ASome (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (W' : world segs) (regs' : bvmap 5 word) (mem'
    : word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)) (t : PjTree.jv) (r : list Z) : Prop :=
  getr regs' 10 = w64 0 /\ (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat -> exists F,
    PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n v D F /\ map (fun b => snd b + cf_head) F = prhPv_frees d
    (rest_atR tb text p) ok) /\ pj_in_okR segs (rdW W' mem') q text len (text + len - Z.of_nat (length r)) (Z.of_nat
    d) tb /\ pj_nodeR segs (rdW W' mem') (prh_lin Lam') v t D /\ pj_ncapR segs (rdW W' mem') v t /\ Ledger.lsum D <=
    224 * (Z.of_nat (length (rest_atR tb text p)) - Z.of_nat (length r)).

Definition tpvP_ANone (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (W' : world segs) (regs' : bvmap 5 word) (mem'
    : word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)) : Prop :=
  getr regs' 10 = w64 (-1) /\ (cf_head = PresetReqAt.HEAD -> forall n, (PjGrammar.MAXD - d <= n)%nat -> exists F,
    PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n v D F /\ map (fun b => snd b + cf_head) F = prhPv_frees d
    (rest_atR tb text p) ok) /\ pj_in_afterR segs (rdW W' mem') q text len (Z.of_nat d) 33 /\ pj_fdR segs (rdW W'
    mem') (prh_lin Lam') (PjGrammar.MAXD - d) v D.

Definition tpvP_Q (d : nat) (ly : alayout) (S : astate) (q text len p : Z) (tb : list Z) (v : Z) (Lam : list (Z * Z))
    (peak cnt fail ran most own : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  exists (ok : list bool) res tr okr D Lam' peak' cnt' fail' ran', jr_value ReaderRes.jr_strtod d (rest_atR tb text
    p) ok = (res, tr, okr) /\ prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own /\ room_live_cf S'
    /\ PresetHullBudget.hull_used S S' (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) /\ Permutation
    (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
    (YGcfRoom.room_of_cf S)) (PresetReqAt.rd_hevs tr)) /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os : list
    (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs tr) ->
    exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs tr))%nat H0 hist' S') /\
    (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 :
    list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os
    i (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) -> PRH_Base.prh_cons_from sm x os i (length
    (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) -> (fail < cnt \/ cnt + Z.of_nat (calls
    (prhPv_gtrace d (rest_atR tb text p))) <= fail) -> ran' = ran /\ fst (jr_value ReaderRes.jr_strtod d (rest_atR tb
    text p) []) = (res, tr) /\ exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs
    (prhPv_gtrace d (rest_atR tb text p))))%nat H0 hist' S') /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os :
    list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst
    (jr_value ReaderRes.jr_strtod d (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
    PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (jr_value ReaderRes.jr_strtod d (rest_atR
    tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) -> cnt <= fail < cnt + Z.of_nat (calls (prhPv_gtrace d
    (rest_atR tb text p))) -> PRH_Base.prh_granted ok cnt fail (calls tr)) /\ rd_ledger_move Lam peak cnt fail ran
    most ok (prhPv_gtrace d (rest_atR tb text p)) tr D Lam' peak' cnt' fail' ran' /\ rd_blocks_move ly S ly' S' D tr
    (rest_atR tb text p) d /\ blocks_bytes S' <= blocks_bytes S + prh_held tr /\ Ledger.lsum D = PjGrammar.held tr /\
    match res with | Some (t, r) => tpvP_ASome d q text len p tb v W' regs' mem' ok D Lam' t r | None => tpvP_ANone d
    q text len p tb v W' regs' mem' ok D Lam' end.

Lemma tpvP_Q_check : forall (d : nat) (CTX CTX0 CW : list (list Z)), tparse_value_specX d CTX CTX0 CW ->
    tparse_value_specX d CTX CTX0 CW.
Proof.
  intros d CTX CTX0 CW H. unfold tparse_value_specX in *.
  intros ly S Hp W regs mem md ch e q text len p tb v Lam peak cnt fail ran most own.
  specialize (H ly S Hp W regs mem md ch e q text len p tb v Lam peak cnt fail ran most own).
  (* the conclusion is SRr' (the re-hiding move), so the post is found under SRr' *)
  lazymatch type of H with context [SRr' _ _ _ _ (?F ?Q)] => change Q with (tpvP_Q d ly S q text len p tb v Lam peak cnt
      fail ran most own) in H end.
  exact H.
Qed.

Record tpvP_R (d : nat) (ly : alayout) (S : astate) (q text len p : Z) (tb : list Z) (v : Z) (Lam : list (Z * Z)) (peak
    cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (ok : list bool) (res : option (PjTree.jv * list Z)) (tr : list PjGrammar.ev) (okr :
    list bool) (D Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) : Prop := {
  tpvP_run : jr_value ReaderRes.jr_strtod d (rest_atR tb text p) ok = (res, tr, okr);
  tpvP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own;
  tpvP_room : room_live_cf S';
  tpvP_hull : PresetHullBudget.hull_used S S' (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)));
  tpvP_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
    (YGcfRoom.room_of_cf S)) (PresetReqAt.rd_hevs tr));
  tpvP_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at
    sm x os i (PresetReqAt.rd_hevs tr) -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length
    (PresetReqAt.rd_hevs tr))%nat H0 hist' S');
  tpvP_outcome : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) ->
    PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) -> (fail <
    cnt \/ cnt + Z.of_nat (calls (prhPv_gtrace d (rest_atR tb text p))) <= fail) -> ran' = ran /\ fst (jr_value
    ReaderRes.jr_strtod d (rest_atR tb text p) []) = (res, tr) /\ exists hist', PresetRoomPos.iface_room_pos sm x os
    (i + length (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))))%nat H0 hist' S');
  tpvP_injected : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (jr_value ReaderRes.jr_strtod d (rest_atR tb text p)
    (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) -> PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs
    (snd (fst (jr_value ReaderRes.jr_strtod d (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) ->
    cnt <= fail < cnt + Z.of_nat (calls (prhPv_gtrace d (rest_atR tb text p))) -> PRH_Base.prh_granted ok cnt fail
    (calls tr));
  tpvP_ledger_move : rd_ledger_move Lam peak cnt fail ran most ok (prhPv_gtrace d (rest_atR tb text p)) tr D Lam'
    peak' cnt' fail' ran';
  tpvP_blocks_move : rd_blocks_move ly S ly' S' D tr (rest_atR tb text p) d;
  tpvP_bytes : blocks_bytes S' <= blocks_bytes S + prh_held tr;
  tpvP_lsum : Ledger.lsum D = PjGrammar.held tr;
  tpvP_arm : match res with | Some (t, r) => tpvP_ASome d q text len p tb v W' regs' mem' ok D Lam' t r | None =>
    tpvP_ANone d q text len p tb v W' regs' mem' ok D Lam' end }.

Lemma tpvP_R_of : forall (d : nat) (ly : alayout) (S : astate) (q text len p : Z) (tb : list Z) (v : Z) (Lam : list (Z
    * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' :
    bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  tpvP_Q d ly S q text len p tb v Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md' ->
  exists ok res tr okr D Lam' peak' cnt' fail' ran', tpvP_R d ly S q text len p tb v Lam peak cnt fail ran most own ly'
      S' Hp' W' regs' mem' ok res tr okr D Lam' peak' cnt' fail' ran'.
Proof.
  intros d ly S q text len p tb v Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md' H. destruct H as (ok &
      res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & H0 & H1 & H2 & Hh & H3 & H4 & H5 & H6 & H7 & H8 & H9 &
      H10 & H11).
  exists ok, res, tr, okr, D, Lam', peak', cnt', fail', ran'.
  exact {| tpvP_run := H0; tpvP_ledger := H1; tpvP_room := H2; tpvP_hull := Hh; tpvP_live := H3; tpvP_pos := H4;
      tpvP_outcome := H5; tpvP_injected := H6; tpvP_ledger_move := H7; tpvP_blocks_move := H8; tpvP_bytes := H9;
      tpvP_lsum := H10; tpvP_arm := H11 |}.
Qed.

Lemma tpvP_Q_of_R : forall (d : nat) (ly : alayout) (S : astate) (q text len p : Z) (tb : list Z) (v : Z) (Lam : list
    (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' :
    bvmap 5 word) (mem' : word -> option byte) (md' : Model) (ok : list bool) (res : option (PjTree.jv * list Z)) (tr :
    list PjGrammar.ev) (okr : list bool) (D Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z),
  tpvP_R d ly S q text len p tb v Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak'
      cnt' fail' ran' ->
  tpvP_Q d ly S q text len p tb v Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md'.
Proof.
  intros d ly S q text len p tb v Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md' ok res tr okr D Lam'
      peak' cnt' fail' ran' HR.
  exists ok, res, tr, okr, D, Lam', peak', cnt', fail', ran'.
  exact (conj (tpvP_run HR) (conj (tpvP_ledger HR) (conj (tpvP_room HR) (conj (tpvP_hull HR) (conj (tpvP_live HR)
      (conj (tpvP_pos HR) (conj (tpvP_outcome HR) (conj (tpvP_injected HR) (conj (tpvP_ledger_move HR) (conj
      (tpvP_blocks_move HR) (conj (tpvP_bytes HR) (conj (tpvP_lsum HR) (tpvP_arm HR))))))))))))).
Qed.

(* the CONSEQUENTS of the post's guarded conjuncts, NAMED: each conjunct of an implication's conclusion, read from the
   record through one lemma (a consumer that applies the guard and destructs its conclusion is not broken
   by the next conjunct appended there) *)

Lemma tpvP_outcome_ran : forall (d : nat) (ly : alayout) (S : astate) (q text len p : Z) (tb : list Z) (v : Z) (Lam :
    list (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (res : option (PjTree.jv * list Z)) (tr : list
    PjGrammar.ev) (okr : list bool) (D Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z),
  tpvP_R d ly S q text len p tb v Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak'
      cnt' fail' ran' ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) -> PRH_Base.prh_cons_from sm x os i (length
      (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) -> (fail < cnt \/ cnt + Z.of_nat (calls
      (prhPv_gtrace d (rest_atR tb text p))) <= fail) ->
  ran' = ran.
Proof.
  intros d ly S q text len p tb v Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak'
      cnt' fail' ran' HR sm x os i H0 hist HP0 HP1 HP2 HP3.
  exact (proj1 (tpvP_outcome HR HP0 HP1 HP2 HP3)).
Qed.

Lemma tpvP_outcome_run : forall (d : nat) (ly : alayout) (S : astate) (q text len p : Z) (tb : list Z) (v : Z) (Lam :
    list (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (res : option (PjTree.jv * list Z)) (tr : list
    PjGrammar.ev) (okr : list bool) (D Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z),
  tpvP_R d ly S q text len p tb v Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak'
      cnt' fail' ran' ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) -> PRH_Base.prh_cons_from sm x os i (length
      (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) -> (fail < cnt \/ cnt + Z.of_nat (calls
      (prhPv_gtrace d (rest_atR tb text p))) <= fail) ->
  fst (jr_value ReaderRes.jr_strtod d (rest_atR tb text p) []) = (res, tr).
Proof.
  intros d ly S q text len p tb v Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak'
      cnt' fail' ran' HR sm x os i H0 hist HP0 HP1 HP2 HP3.
  exact (proj1 (proj2 (tpvP_outcome HR HP0 HP1 HP2 HP3))).
Qed.

Lemma tpvP_outcome_pos : forall (d : nat) (ly : alayout) (S : astate) (q text len p : Z) (tb : list Z) (v : Z) (Lam :
    list (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (res : option (PjTree.jv * list Z)) (tr : list
    PjGrammar.ev) (okr : list bool) (D Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z),
  tpvP_R d ly S q text len p tb v Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak'
      cnt' fail' ran' ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) -> PRH_Base.prh_cons_from sm x os i (length
      (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) -> (fail < cnt \/ cnt + Z.of_nat (calls
      (prhPv_gtrace d (rest_atR tb text p))) <= fail) ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text
      p))))%nat H0 hist' S'.
Proof.
  intros d ly S q text len p tb v Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak'
      cnt' fail' ran' HR sm x os i H0 hist HP0 HP1 HP2 HP3.
  exact (proj2 (proj2 (tpvP_outcome HR HP0 HP1 HP2 HP3))).
Qed.


Record tpvP_RSome (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (W' : world segs) (regs' : bvmap 5 word) (mem' :
    word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)) (t : PjTree.jv) (r : list Z) : Prop := {
  tpvPs_ret : getr regs' 10 = w64 0;
  tpvPs_freeord : (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat -> exists F, PRH_PjOrder.pj_foR
    segs (rdW W' mem') (prh_lin Lam') n v D F /\ map (fun b => snd b + cf_head) F = prhPv_frees d (rest_atR tb text
    p) ok);
  tpvPs_in_ok : pj_in_okR segs (rdW W' mem') q text len (text + len - Z.of_nat (length r)) (Z.of_nat d) tb;
  tpvPs_node : pj_nodeR segs (rdW W' mem') (prh_lin Lam') v t D;
  tpvPs_ncap : pj_ncapR segs (rdW W' mem') v t;
  tpvPs_lsum_le : Ledger.lsum D <= 224 * (Z.of_nat (length (rest_atR tb text p)) - Z.of_nat (length r)) }.

Lemma tpvP_RSome_of : forall (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (W' : world segs) (regs' : bvmap 5
    word) (mem' : word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)) (t : PjTree.jv) (r : list Z),
  tpvP_ASome d q text len p tb v W' regs' mem' ok D Lam' t r ->
  tpvP_RSome d q text len p tb v W' regs' mem' ok D Lam' t r.
Proof.
  intros d q text len p tb v W' regs' mem' ok D Lam' t r H. destruct H as (H0 & H1 & H2 & H3 & H4 & H5).
  exact {| tpvPs_ret := H0; tpvPs_freeord := H1; tpvPs_in_ok := H2; tpvPs_node := H3; tpvPs_ncap := H4; tpvPs_lsum_le
      := H5 |}.
Qed.

Lemma tpvP_ASome_of_R : forall (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (W' : world segs) (regs' : bvmap 5
    word) (mem' : word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)) (t : PjTree.jv) (r : list Z),
  tpvP_RSome d q text len p tb v W' regs' mem' ok D Lam' t r ->
  tpvP_ASome d q text len p tb v W' regs' mem' ok D Lam' t r.
Proof.
  intros d q text len p tb v W' regs' mem' ok D Lam' t r HR.
  exact (conj (tpvPs_ret HR) (conj (tpvPs_freeord HR) (conj (tpvPs_in_ok HR) (conj (tpvPs_node HR) (conj (tpvPs_ncap
      HR) (tpvPs_lsum_le HR)))))).
Qed.


Record tpvP_RNone (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (W' : world segs) (regs' : bvmap 5 word) (mem' :
    word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)) : Prop := {
  tpvPn_ret : getr regs' 10 = w64 (-1);
  tpvPn_freeord : (cf_head = PresetReqAt.HEAD -> forall n, (PjGrammar.MAXD - d <= n)%nat -> exists F,
    PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n v D F /\ map (fun b => snd b + cf_head) F = prhPv_frees d
    (rest_atR tb text p) ok);
  tpvPn_in_after : pj_in_afterR segs (rdW W' mem') q text len (Z.of_nat d) 33;
  tpvPn_fd : pj_fdR segs (rdW W' mem') (prh_lin Lam') (PjGrammar.MAXD - d) v D }.

Lemma tpvP_RNone_of : forall (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (W' : world segs) (regs' : bvmap 5
    word) (mem' : word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)),
  tpvP_ANone d q text len p tb v W' regs' mem' ok D Lam' ->
  tpvP_RNone d q text len p tb v W' regs' mem' ok D Lam'.
Proof.
  intros d q text len p tb v W' regs' mem' ok D Lam' H. destruct H as (H0 & H1 & H2 & H3).
  exact {| tpvPn_ret := H0; tpvPn_freeord := H1; tpvPn_in_after := H2; tpvPn_fd := H3 |}.
Qed.

Lemma tpvP_ANone_of_R : forall (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (W' : world segs) (regs' : bvmap 5
    word) (mem' : word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)),
  tpvP_RNone d q text len p tb v W' regs' mem' ok D Lam' ->
  tpvP_ANone d q text len p tb v W' regs' mem' ok D Lam'.
Proof.
  intros d q text len p tb v W' regs' mem' ok D Lam' HR.
  exact (conj (tpvPn_ret HR) (conj (tpvPn_freeord HR) (conj (tpvPn_in_after HR) (tpvPn_fd HR)))).
Qed.

Local Unset Implicit Arguments.

(* ---- parse_items: a0 = the cursor q, a1 = the node v, a2 = 1 for an object and 0 for an array, at nesting d ---- *)

(* The cursor is at the opener ('[' or '{'). It reads the members: for an object a key (parse_string) and a colon,
   then each value by parse_value at d + 1, growing the kids (and keys) arrays by grow, and freeing on refusal.
   Returns 0 or -1; the refused cursor's depth may be one deeper. *)
Definition tparse_items_specX (d : nat) (CTX : list (list Z)) (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall ly S Hp W regs mem md ch e q text len p (tb : list Z) v (o : bool) Lam peak cnt fail ran most own,
  fpre B ARx (STK_parse_items d) ly S Hp W regs mem md ch ->
  (* the memory overlay is normal at entry; see tparse_value_specX's note (parse_items reaches strtod through
     parse_value) *)
  YAkMemnorm.memnorm segs mem ->
  In (raZ regs :: spine ch) CTX ->
  (* the call-graph universe closure, and the cursor chain's stop word named at this entry so the walk meets
     parse_string's (and parse_items') call-state chain premises (the kit at 4eb03b7b7e8) *)
  prh_univ_closure B CTX0 ->
  prh_cur_entry W mem regs q ->
  (* THE CURSOR SET CW (PRH_Base.prh_cw_entry); see tparse_value_specX's note *)
  prh_cw_entry B CW W mem regs q ->
  (* the entry call chain survives any change of the caller cells the reader writes, up to its spine (the image-B parse_items walk proved the
     fixed-ch form FALSE at image B's parse_items -> parse_value call, B 0x87d94, where s0 = q + 16 and the chain's first
     frame reads the cursor's p word; the kit owner's 06:39Z ruling). Earlier: the entry call chain reads no caller cell the reader writes (the parse_value proof walk's measurement: the walk stores the cursor's p
     word, and at d > 0 the entry s0 is parse_items' own, next to q; a cut chain meets it for free, and pj_parse
     discharges it from its frame layout since q lies below its entry sp) *)
  (exists ch', achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch' /\ spine ch' = spine ch) ->
  (* PARTITIONED (the kit owner's 06:39Z ruling): below spZ regs + 16 the callee builds the chain at q from its own two
     saved words; at or above it the caller supplies one (the slice walker proved the chain does not transfer below that bound).
     The chain at the CURSOR, which parse_string's entry-chain premise needs at every nested call (the kit owner's 06:12Z ruling,
     measured by the S4 walk): from pj_parse the cursor is in the caller's frame right at the callee's entry sp
     (image A `mv a0, sp`: q = spZ regs; image B `addi a0, sp, 8`: q = spZ regs + 8, which the image-B pj_parse walk proved makes a
     `q = spZ regs` form false on B), so the first disjunct covers both and the record at fp = q straddles the callee's
     own saved ra / s0; from a reader caller it is the caller's chain at q, and
     achain is monotone downward in sp *)
  ((spZ regs <= q < spZ regs + 16) \/
   (spZ regs + 16 <= q /\ exists ch', achain ly (aview segs (w_H W) mem) (spZ regs) (prh_s0 F_parse_string q) ch')) ->
  getr regs 10 = w64 q -> getr regs 11 = w64 v -> getr regs 12 = w64 (if o then 1 else 0) ->
  rd_pre (STK_parse_items d) ly S Hp W regs mem Lam peak cnt fail ran most own e q text len p d tb v ->
  p < text + len -> nth_error tb (Z.to_nat (p - text)) = Some (if o then 123 else 91) ->
  rd_room S (prhPi_gtrace d o (rest_atR tb text p)) ->
  (* THE WILD BUDGET (the room count of P''); see tparse_value_specX's note: the SET is CW and k is 0 *)
  YCbqGwild.wild_room (as_universe B) CW 0 (st_depot S) ->
  (* THE LIVE COUNTS AT THE INNER CALLS along the ALL-GRANTED events rd_hevs (prhPi_gtrace ..); see tparse_value_specX's
     note *)
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* THE HULL BUDGET (the header): room for the all-granted events *)
  PresetHullBudget.hull_budget S (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) ->
  (* parse_items' own fuzz_free (A 0x87760, B 0x87f30, the missing-colon free of the key): its free trace is held by the
     closure (prh_univ_closure's clause 4b at every chain word, 4a at the code word), and the call needs the chain from
     s0 = prh_s0 F_parse_items q (q on A, q + 16 on B); prh_cur_entry gives its prh_cur_low at entry, and the walk
     keeps the cursor's p word, which B's chain reads at q, below alloc_ceiling by pj_in_okR (the kit owner's (2), replacing D4) *)
  (exists ch, achain ly (aview segs (w_H W) mem) (spZ regs - pi_frame F_parse_items) (prh_s0 F_parse_items q) ch) ->
  Z.of_nat (length (frames S)) + Z.of_nat (PjGrammar.MAXD - d) <= fs_frames 0 ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.H2); fpostWFbm is already at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_parse_items) regs mem md)
    (fpostWFbm B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v) regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' =>
       exists (ok : list bool) res tr okr D Lam' peak' cnt' fail' ran',
       jr_items ReaderRes.jr_strtod d o (rest_atR tb text p) ok = (res, tr, okr) /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own /\ room_live_cf S' /\
       (* THE HULL USE (the header): at most the entry budget's list *)
       PresetHullBudget.hull_used S S' (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) /\
       (* the live requests move by the events the instance made, E = rd_hevs tr *)
       (* CFHEAD-16, NOT GUARDED (the kit owner's ruling D1; the head-size census): rs_live holds the INSTANCE sizes
          (user + cf_head), the model's events HEAD-sized; equal exactly when cf_head = PresetReqAt.HEAD, which the walk
          takes as its Section hypothesis PRH_Base.prh_head16 (reflexivity at CfParams_preset). *)
       Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
         (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetReqAt.rd_hevs tr)) /\
       (* THE POSITION TRANSFER (post-implication form): THE EXACT ADVANCE by the events the instance made *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs tr) ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs tr))%nat H0 hist' S') /\
       (* THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS; tparse_value_specX's note), over the
          ALL-GRANTED members' events rd_hevs (prhPi_gtrace ..) *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) ->
          PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) ->
          (fail < cnt \/ cnt + Z.of_nat (calls (prhPi_gtrace d o (rest_atR tb text p))) <= fail) ->
          ran' = ran /\ fst (jr_items ReaderRes.jr_strtod d o (rest_atR tb text p) []) = (res, tr) /\
          exists hist', PresetRoomPos.iface_room_pos sm x os
            (i + length (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))))%nat H0 hist' S') /\
       (* THE OUTCOME OF AN INJECTED READING (GUARDED; tparse_value_specX's note has the reason and
          the per-call derivation), over the members' events under the MODEL's grant list PresetReqAt.okk at the
          chosen call fail - cnt. The recursion parse_value / parse_items carries it: each one cites the other's. *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (jr_items ReaderRes.jr_strtod d o
            (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
          PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (jr_items ReaderRes.jr_strtod d o
            (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) ->
          cnt <= fail < cnt + Z.of_nat (calls (prhPi_gtrace d o (rest_atR tb text p))) ->
          PRH_Base.prh_granted ok cnt fail (calls tr)) /\
       rd_ledger_move Lam peak cnt fail ran most ok (prhPi_gtrace d o (rest_atR tb text p)) tr D Lam' peak' cnt' fail'
         ran' /\
       rd_blocks_move ly S ly' S' D tr (rest_atR tb text p) d /\
       (* the live room handed on to the next call (the items-element walk's finding: rd_room's live conjunct cannot be re-established
          after a call otherwise); blocks_bytes counts allocator requests, each a user request plus the head: prh_held *)
       blocks_bytes S' <= blocks_bytes S + prh_held tr /\
       (* the subtree's blocks are exactly the trace's net bytes, so a caller composing rd_ledger_move across this
          call can re-associate the peak (the items-element walk's finding: Permutation of the sizes alone does not give it) *)
       Ledger.lsum D = PjGrammar.held tr /\
       match res with
       | Some (t, r) =>
           getr regs' 10 = w64 0 /\
           (* THE TREE'S FREE ORDER (FREEORD-NONE; tparse_value_specX's note): pj_free's order list of the container
              carries prhPi_frees at this call's (d, o, rest, ok), IN ORDER; parse_value's walk at '{' / '[' passes it
              on as its own (prhPv_frees at the same cursor, through jfv's container arm). *)
           (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
              exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n v D F /\
                map (fun b => snd b + cf_head) F = prhPi_frees d o (rest_atR tb text p) ok) /\
           pj_in_okR segs (rdW W' mem') q text len (text + len - Z.of_nat (length r)) (Z.of_nat d) tb /\
           pj_nodeR segs (rdW W' mem') (prh_lin Lam') v t D /\
           (* CAP (PRH_Reader.pj_ncapR; tparse_value_specX's note): every array / object node of the container's
              tree has header cap = PresetReqAt.ncap of its count; parse_value's walk at '{' / '[' passes it on *)
           pj_ncapR segs (rdW W' mem') v t /\
           Ledger.lsum D <= 224 * (Z.of_nat (length (rest_atR tb text p)) - Z.of_nat (length r))
       | None =>
           getr regs' 10 = w64 (-1) /\
           (* THE PARTIAL TREE'S FREE ORDER (FREEORD-NONE; tparse_value_specX's note): the refused container's
              order list (its completed slots, the refused member's partial slot, its arrays as they are then) carries
              prhPi_frees at this call's (d, o, rest, ok), IN ORDER, at every depth bound n >= MAXD - d *)
           (cf_head = PresetReqAt.HEAD -> forall n, (PjGrammar.MAXD - d <= n)%nat ->
              exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n v D F /\
                map (fun b => snd b + cf_head) F = prhPi_frees d o (rest_atR tb text p) ok) /\
           pj_in_afterR segs (rdW W' mem') q text len (Z.of_nat d + 1) 33 /\
           pj_fdR segs (rdW W' mem') (prh_lin Lam') (PjGrammar.MAXD - d) v D
       end)).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tparse_items_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
    cite the
   lemma). ADDITIVE: the text above is unchanged. tpiP_Q IS the text's post (tpiP_Q_check fails to build if the two ever
   differ); tpiP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas build the post
   from them. A consumer that reads and builds the post through these is not broken by the NEXT appended conjunct. ====
       *)

Definition tpiP_ASome (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (o : bool) (W' : world segs) (regs' : bvmap 5
    word) (mem' : word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)) (t : PjTree.jv) (r : list Z) : Prop :=
  getr regs' 10 = w64 0 /\ (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat -> exists F,
    PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n v D F /\ map (fun b => snd b + cf_head) F = prhPi_frees d
    o (rest_atR tb text p) ok) /\ pj_in_okR segs (rdW W' mem') q text len (text + len - Z.of_nat (length r))
    (Z.of_nat d) tb /\ pj_nodeR segs (rdW W' mem') (prh_lin Lam') v t D /\ pj_ncapR segs (rdW W' mem') v t /\
    Ledger.lsum D <= 224 * (Z.of_nat (length (rest_atR tb text p)) - Z.of_nat (length r)).

Definition tpiP_ANone (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (o : bool) (W' : world segs) (regs' : bvmap 5
    word) (mem' : word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)) : Prop :=
  getr regs' 10 = w64 (-1) /\ (cf_head = PresetReqAt.HEAD -> forall n, (PjGrammar.MAXD - d <= n)%nat -> exists F,
    PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n v D F /\ map (fun b => snd b + cf_head) F = prhPi_frees d
    o (rest_atR tb text p) ok) /\ pj_in_afterR segs (rdW W' mem') q text len (Z.of_nat d + 1) 33 /\ pj_fdR segs (rdW
    W' mem') (prh_lin Lam') (PjGrammar.MAXD - d) v D.

Definition tpiP_Q (d : nat) (ly : alayout) (S : astate) (q text len p : Z) (tb : list Z) (v : Z) (o : bool) (Lam : list
    (Z * Z)) (peak cnt fail ran most own : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  exists (ok : list bool) res tr okr D Lam' peak' cnt' fail' ran', jr_items ReaderRes.jr_strtod d o (rest_atR tb text
    p) ok = (res, tr, okr) /\ prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own /\ room_live_cf S'
    /\ PresetHullBudget.hull_used S S' (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) /\ Permutation
    (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
    (YGcfRoom.room_of_cf S)) (PresetReqAt.rd_hevs tr)) /\ (forall (sm : list Z -> Z * Z) (x : list Z) (os : list
    (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs tr) ->
    exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs tr))%nat H0 hist' S') /\
    (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 :
    list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os
    i (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) -> PRH_Base.prh_cons_from sm x os i (length
    (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) -> (fail < cnt \/ cnt + Z.of_nat (calls
    (prhPi_gtrace d o (rest_atR tb text p))) <= fail) -> ran' = ran /\ fst (jr_items ReaderRes.jr_strtod d o
    (rest_atR tb text p) []) = (res, tr) /\ exists hist', PresetRoomPos.iface_room_pos sm x os (i + length
    (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))))%nat H0 hist' S') /\ (forall (sm : list Z -> Z * Z)
    (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst
    (jr_items ReaderRes.jr_strtod d o (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) ->
    PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (jr_items ReaderRes.jr_strtod d o
    (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt)))))))) -> cnt <= fail < cnt + Z.of_nat (calls
    (prhPi_gtrace d o (rest_atR tb text p))) -> PRH_Base.prh_granted ok cnt fail (calls tr)) /\ rd_ledger_move Lam
    peak cnt fail ran most ok (prhPi_gtrace d o (rest_atR tb text p)) tr D Lam' peak' cnt' fail' ran' /\
    rd_blocks_move ly S ly' S' D tr (rest_atR tb text p) d /\ blocks_bytes S' <= blocks_bytes S + prh_held tr /\
    Ledger.lsum D = PjGrammar.held tr /\ match res with | Some (t, r) => tpiP_ASome d q text len p tb v o W' regs'
    mem' ok D Lam' t r | None => tpiP_ANone d q text len p tb v o W' regs' mem' ok D Lam' end.

Lemma tpiP_Q_check : forall (d : nat) (CTX CTX0 CW : list (list Z)), tparse_items_specX d CTX CTX0 CW ->
    tparse_items_specX d CTX CTX0 CW.
Proof.
  intros d CTX CTX0 CW H. unfold tparse_items_specX in *.
  intros ly S Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own.
  specialize (H ly S Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own).
  (* the conclusion is SRr' (the re-hiding move), so the post is found under SRr' *)
  lazymatch type of H with context [SRr' _ _ _ _ (?F ?Q)] => change Q with (tpiP_Q d ly S q text len p tb v o Lam peak cnt
      fail ran most own) in H end.
  exact H.
Qed.

Record tpiP_R (d : nat) (ly : alayout) (S : astate) (q text len p : Z) (tb : list Z) (v : Z) (o : bool) (Lam : list (Z
    * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' :
    bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (res : option (PjTree.jv * list Z)) (tr : list
    PjGrammar.ev) (okr : list bool) (D Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) : Prop := {
  tpiP_run : jr_items ReaderRes.jr_strtod d o (rest_atR tb text p) ok = (res, tr, okr);
  tpiP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own;
  tpiP_room : room_live_cf S';
  tpiP_hull : PresetHullBudget.hull_used S S' (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)));
  tpiP_live : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.hlive_from (PresetRoom.rs_live
    (YGcfRoom.room_of_cf S)) (PresetReqAt.rd_hevs tr));
  tpiP_pos : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at
    sm x os i (PresetReqAt.rd_hevs tr) -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length
    (PresetReqAt.rd_hevs tr))%nat H0 hist' S');
  tpiP_outcome : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) ->
    PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) -> (fail
    < cnt \/ cnt + Z.of_nat (calls (prhPi_gtrace d o (rest_atR tb text p))) <= fail) -> ran' = ran /\ fst (jr_items
    ReaderRes.jr_strtod d o (rest_atR tb text p) []) = (res, tr) /\ exists hist', PresetRoomPos.iface_room_pos sm x
    os (i + length (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))))%nat H0 hist' S');
  tpiP_injected : (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i :
    nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (jr_items ReaderRes.jr_strtod d o (rest_atR tb text
    p) (PresetReqAt.okk (Z.to_nat (fail - cnt))))))) -> PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs
    (snd (fst (jr_items ReaderRes.jr_strtod d o (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt))))))))
    -> cnt <= fail < cnt + Z.of_nat (calls (prhPi_gtrace d o (rest_atR tb text p))) -> PRH_Base.prh_granted ok cnt
    fail (calls tr));
  tpiP_ledger_move : rd_ledger_move Lam peak cnt fail ran most ok (prhPi_gtrace d o (rest_atR tb text p)) tr D Lam'
    peak' cnt' fail' ran';
  tpiP_blocks_move : rd_blocks_move ly S ly' S' D tr (rest_atR tb text p) d;
  tpiP_bytes : blocks_bytes S' <= blocks_bytes S + prh_held tr;
  tpiP_lsum : Ledger.lsum D = PjGrammar.held tr;
  tpiP_arm : match res with | Some (t, r) => tpiP_ASome d q text len p tb v o W' regs' mem' ok D Lam' t r | None =>
    tpiP_ANone d q text len p tb v o W' regs' mem' ok D Lam' end }.

Lemma tpiP_R_of : forall (d : nat) (ly : alayout) (S : astate) (q text len p : Z) (tb : list Z) (v : Z) (o : bool) (Lam
    : list (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  tpiP_Q d ly S q text len p tb v o Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md' ->
  exists ok res tr okr D Lam' peak' cnt' fail' ran', tpiP_R d ly S q text len p tb v o Lam peak cnt fail ran most own
      ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak' cnt' fail' ran'.
Proof.
  intros d ly S q text len p tb v o Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md' H. destruct H as (ok &
      res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & H0 & H1 & H2 & Hh & H3 & H4 & H5 & H6 & H7 & H8 & H9 &
      H10 & H11).
  exists ok, res, tr, okr, D, Lam', peak', cnt', fail', ran'.
  exact {| tpiP_run := H0; tpiP_ledger := H1; tpiP_room := H2; tpiP_hull := Hh; tpiP_live := H3; tpiP_pos := H4;
      tpiP_outcome := H5; tpiP_injected := H6; tpiP_ledger_move := H7; tpiP_blocks_move := H8; tpiP_bytes := H9;
      tpiP_lsum := H10; tpiP_arm := H11 |}.
Qed.

Lemma tpiP_Q_of_R : forall (d : nat) (ly : alayout) (S : astate) (q text len p : Z) (tb : list Z) (v : Z) (o : bool)
    (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world
    segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (ok : list bool) (res : option (PjTree.jv *
    list Z)) (tr : list PjGrammar.ev) (okr : list bool) (D Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z),
  tpiP_R d ly S q text len p tb v o Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak'
      cnt' fail' ran' ->
  tpiP_Q d ly S q text len p tb v o Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md'.
Proof.
  intros d ly S q text len p tb v o Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md' ok res tr okr D Lam'
      peak' cnt' fail' ran' HR.
  exists ok, res, tr, okr, D, Lam', peak', cnt', fail', ran'.
  exact (conj (tpiP_run HR) (conj (tpiP_ledger HR) (conj (tpiP_room HR) (conj (tpiP_hull HR) (conj (tpiP_live HR)
      (conj (tpiP_pos HR) (conj (tpiP_outcome HR) (conj (tpiP_injected HR) (conj (tpiP_ledger_move HR) (conj
      (tpiP_blocks_move HR) (conj (tpiP_bytes HR) (conj (tpiP_lsum HR) (tpiP_arm HR))))))))))))).
Qed.

(* the CONSEQUENTS of the post's guarded conjuncts, NAMED: each conjunct of an implication's conclusion, read from the
   record through one lemma (a consumer that applies the guard and destructs its conclusion is not broken
   by the next conjunct appended there) *)

Lemma tpiP_outcome_ran : forall (d : nat) (ly : alayout) (S : astate) (q text len p : Z) (tb : list Z) (v : Z) (o :
    bool) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (res : option (PjTree.jv * list
    Z)) (tr : list PjGrammar.ev) (okr : list bool) (D Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z),
  tpiP_R d ly S q text len p tb v o Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak'
      cnt' fail' ran' ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) -> PRH_Base.prh_cons_from sm x os i (length
      (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) -> (fail < cnt \/ cnt + Z.of_nat (calls
      (prhPi_gtrace d o (rest_atR tb text p))) <= fail) ->
  ran' = ran.
Proof.
  intros d ly S q text len p tb v o Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak'
      cnt' fail' ran' HR sm x os i H0 hist HP0 HP1 HP2 HP3.
  exact (proj1 (tpiP_outcome HR HP0 HP1 HP2 HP3)).
Qed.

Lemma tpiP_outcome_run : forall (d : nat) (ly : alayout) (S : astate) (q text len p : Z) (tb : list Z) (v : Z) (o :
    bool) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (res : option (PjTree.jv * list
    Z)) (tr : list PjGrammar.ev) (okr : list bool) (D Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z),
  tpiP_R d ly S q text len p tb v o Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak'
      cnt' fail' ran' ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) -> PRH_Base.prh_cons_from sm x os i (length
      (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) -> (fail < cnt \/ cnt + Z.of_nat (calls
      (prhPi_gtrace d o (rest_atR tb text p))) <= fail) ->
  fst (jr_items ReaderRes.jr_strtod d o (rest_atR tb text p) []) = (res, tr).
Proof.
  intros d ly S q text len p tb v o Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak'
      cnt' fail' ran' HR sm x os i H0 hist HP0 HP1 HP2 HP3.
  exact (proj1 (proj2 (tpiP_outcome HR HP0 HP1 HP2 HP3))).
Qed.

Lemma tpiP_outcome_pos : forall (d : nat) (ly : alayout) (S : astate) (q text len p : Z) (tb : list Z) (v : Z) (o :
    bool) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (res : option (PjTree.jv * list
    Z)) (tr : list PjGrammar.ev) (okr : list bool) (D Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z),
  tpiP_R d ly S q text len p tb v o Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak'
      cnt' fail' ran' ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) -> PRH_Base.prh_cons_from sm x os i (length
      (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) -> (fail < cnt \/ cnt + Z.of_nat (calls
      (prhPi_gtrace d o (rest_atR tb text p))) <= fail) ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb
      text p))))%nat H0 hist' S'.
Proof.
  intros d ly S q text len p tb v o Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' ok res tr okr D Lam' peak'
      cnt' fail' ran' HR sm x os i H0 hist HP0 HP1 HP2 HP3.
  exact (proj2 (proj2 (tpiP_outcome HR HP0 HP1 HP2 HP3))).
Qed.


Record tpiP_RSome (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (o : bool) (W' : world segs) (regs' : bvmap 5
    word) (mem' : word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)) (t : PjTree.jv) (r : list Z) : Prop :=
    {
  tpiPs_ret : getr regs' 10 = w64 0;
  tpiPs_freeord : (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat -> exists F, PRH_PjOrder.pj_foR
    segs (rdW W' mem') (prh_lin Lam') n v D F /\ map (fun b => snd b + cf_head) F = prhPi_frees d o (rest_atR tb text
    p) ok);
  tpiPs_in_ok : pj_in_okR segs (rdW W' mem') q text len (text + len - Z.of_nat (length r)) (Z.of_nat d) tb;
  tpiPs_node : pj_nodeR segs (rdW W' mem') (prh_lin Lam') v t D;
  tpiPs_ncap : pj_ncapR segs (rdW W' mem') v t;
  tpiPs_lsum_le : Ledger.lsum D <= 224 * (Z.of_nat (length (rest_atR tb text p)) - Z.of_nat (length r)) }.

Lemma tpiP_RSome_of : forall (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (o : bool) (W' : world segs) (regs' :
    bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)) (t : PjTree.jv) (r : list Z),
  tpiP_ASome d q text len p tb v o W' regs' mem' ok D Lam' t r ->
  tpiP_RSome d q text len p tb v o W' regs' mem' ok D Lam' t r.
Proof.
  intros d q text len p tb v o W' regs' mem' ok D Lam' t r H. destruct H as (H0 & H1 & H2 & H3 & H4 & H5).
  exact {| tpiPs_ret := H0; tpiPs_freeord := H1; tpiPs_in_ok := H2; tpiPs_node := H3; tpiPs_ncap := H4; tpiPs_lsum_le
      := H5 |}.
Qed.

Lemma tpiP_ASome_of_R : forall (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (o : bool) (W' : world segs) (regs' :
    bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)) (t : PjTree.jv) (r : list Z),
  tpiP_RSome d q text len p tb v o W' regs' mem' ok D Lam' t r ->
  tpiP_ASome d q text len p tb v o W' regs' mem' ok D Lam' t r.
Proof.
  intros d q text len p tb v o W' regs' mem' ok D Lam' t r HR.
  exact (conj (tpiPs_ret HR) (conj (tpiPs_freeord HR) (conj (tpiPs_in_ok HR) (conj (tpiPs_node HR) (conj (tpiPs_ncap
      HR) (tpiPs_lsum_le HR)))))).
Qed.


Record tpiP_RNone (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (o : bool) (W' : world segs) (regs' : bvmap 5
    word) (mem' : word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)) : Prop := {
  tpiPn_ret : getr regs' 10 = w64 (-1);
  tpiPn_freeord : (cf_head = PresetReqAt.HEAD -> forall n, (PjGrammar.MAXD - d <= n)%nat -> exists F,
    PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n v D F /\ map (fun b => snd b + cf_head) F = prhPi_frees d
    o (rest_atR tb text p) ok);
  tpiPn_in_after : pj_in_afterR segs (rdW W' mem') q text len (Z.of_nat d + 1) 33;
  tpiPn_fd : pj_fdR segs (rdW W' mem') (prh_lin Lam') (PjGrammar.MAXD - d) v D }.

Lemma tpiP_RNone_of : forall (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (o : bool) (W' : world segs) (regs' :
    bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)),
  tpiP_ANone d q text len p tb v o W' regs' mem' ok D Lam' ->
  tpiP_RNone d q text len p tb v o W' regs' mem' ok D Lam'.
Proof.
  intros d q text len p tb v o W' regs' mem' ok D Lam' H. destruct H as (H0 & H1 & H2 & H3).
  exact {| tpiPn_ret := H0; tpiPn_freeord := H1; tpiPn_in_after := H2; tpiPn_fd := H3 |}.
Qed.

Lemma tpiP_ANone_of_R : forall (d : nat) (q text len p : Z) (tb : list Z) (v : Z) (o : bool) (W' : world segs) (regs' :
    bvmap 5 word) (mem' : word -> option byte) (ok : list bool) (D Lam' : list (Z * Z)),
  tpiP_RNone d q text len p tb v o W' regs' mem' ok D Lam' ->
  tpiP_ANone d q text len p tb v o W' regs' mem' ok D Lam'.
Proof.
  intros d q text len p tb v o W' regs' mem' ok D Lam' HR.
  exact (conj (tpiPn_ret HR) (conj (tpiPn_freeord HR) (conj (tpiPn_in_after HR) (tpiPn_fd HR)))).
Qed.

Local Unset Implicit Arguments.

End c.
