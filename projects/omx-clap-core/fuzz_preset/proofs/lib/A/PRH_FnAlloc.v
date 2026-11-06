(* This file carries the kit's text of the re-hiding move for the two crossing texts
   tfuzz_free_specX and tfuzz_realloc_specX (`PRIMED-SHAPES.md (sha256 9e4880d18317; internal record)` sec. 2.1, 2.2, 5.1): SRr' segs RZ_cf, the post
   at wle' segs RZ_cf, and tfuzz_realloc_specX's refusal evidence world-free. The unit owner's ruling
   C2 (2026-10-31 04:19Z) struck the scratch notice that stood here, by a comment-only edit that keeps the header at
   5 lines, so every line after it keeps its number. *)
(* fuzz_preset, program part (the kit): the ASan contract TEXTS of alloc.c's twelve functions (the eleven both images
   have, and own, which image B keeps out of line), in cgif's per-function form (cgif_file lib/YC21.v:33-66; the fm port's
   FMH_Fn.v:101-180): fpre (YCbqG's afn_pre_x + the read-only view), argument registers, the allocation trace in the
   image's universe where the function calls the allocator, the alloc.c ledger (PRH_Base.v prh_ledger), and SRr to the
   return address through fpost (YCbqG's apost_base_x at PST := prh_pst). Every conclusion is `srealizes`: SRr
   (lib/Reusable/YA0n.v:38-41) is the continuation form over srealizes.
   IMAGE-PARAMETRIC: the image is the listing class (YC4aP PAImg L): the segments are pa_segs and each text's entry is
   pa_sigma AS_<fn>; the other image numbers are PrhImg's (PRH_Base.v). No image constant is named here.
   ALLOCATOR-PARAMETRIC: ARx is an explicit argument; the walks instantiate it at the allocator-model owner's ARcf segs B.
   The functional content is preset's source alloc.c @0b89c6c1bd (:36-162), re-read against the rebuilt image's bytes
   by the S1 owner: the arm structure, the write sets, the two tail calls, the constant malloc / realloc
   traces (n is held in s0 at the call, so the frame chain is empty). Preset's released plain texts lib/Prog/fuzz_*_c.v
   are not ported (they conclude in SR / realizes) and none of their lemmas is cited.
   cf_head is alloc.c's HEAD (16, :31) at preset's CfParams instance; a walk takes `cf_head = 16` from that instance.
   ROOM (PRH_Base.v, the kit owner's rulings (B) and (i)): fuzz_malloc, fuzz_strdup, fuzz_realloc and fuzz_free (if p <> 0)
   take the NON-PRIMARY invariant room_live_cf S on entry and give room_live_cf S' in every arm. NO text states the PRIMARY
   room_cf: its only consumer excludes the NULL, and no caller could supply it at an interior state. So the REFUSED
   arm of prh_alloc_post (arm 2) and of fuzz_realloc's post is KEPT EXPLICITLY: it is the ONLY thing between these
   texts and a silent gap - the primary room is excluded ONCE, globally, by the driver (the driver-contract owner's
   LLVMFuzzerTestOneInput slot: P8's preset_room -> room_at -> no_null_preset). DO NOT remove it as unused-looking.
   The seven accessors and own carry room_live_cf S -> room_live_cf S'. No margin. own takes no room premise: own runs inside
   image B's fuzz_malloc / fuzz_realloc AFTER the allocator call, where the room of the post state is not derivable
   (the secondary count may have risen to the maximum), so a room premise on own would make B's fuzz_malloc walk
   unprovable; and own makes no allocator call itself (it writes the head and calls the poison entry). Do not add it.
   THE PROGRAM LIVE-SET BOUNDS (the kit owner's ruling, on the S1 owner's measurement while re-proving fuzz_free on kit
   9d109484e53): room_live_cf S does NOT give room_live_cf S' across one allocator step on its own. free_cf can grow
   the batch class (enqueue, populate class 24: by YGcfRoomLive.v M24 one growth adds kBatchBytes + kUserMapSize to
   its mapped size), and malloc_cf can raise the secondary count. a8's keeps (RL_free_step :1442, RL_malloc_step
   :1433, RL_realloc_step :1451) take rl_b24_ok L24 S (and rl_sec_ok Lsec S for malloc / realloc), and nothing in
   fpre, prh_ledger or ARcf bounds the live counts: they are input-driven. So, as PRH_Base.v's room bullet says, the
   bounds enter as NAMED conjuncts, in the driver-contract owner's form: `YGcfRoomLive.ccnt24 S <= L24 + DRV` (fuzz_malloc,
   fuzz_realloc, fuzz_strdup, and fuzz_free under p <> 0: FAMILY below) and `YGcfRoomLive.sec_cnt S <= LSEC + DRV`
   (fuzz_malloc, fuzz_realloc, fuzz_strdup), spelled over the LEAF lib/Spec/PresetLiveBounds.v (the kit owner's
   ruling: PresetLiveSec.v and PresetGate.v pull six plain lib/Prog/*_c.v files into any closure through
   lib/Prog/SlotSizes.v; they re-export the leaf's terms as notations, so PresetLiveSec.L24 IS PresetLiveBounds.L24).
   Discharge route, ONE:
   CfRoomLivePreset.preset_rl_b24_ok gives rl_b24_ok (L24 + DRV + 1) S (and ccnt24 S < L24 + DRV + 1, realloc's strict
   premise), preset_rl_sec_ok gives rl_sec_ok (LSEC + DRV) S (its premise is sec_cnt S's, by conversion:
   rs_live_blocks is reflexivity). fuzz_strdup only passes both to fuzz_malloc. The constants are P8's model bounds
   over the 3 MiB input cap (PresetReqAt.MAXB; L24 = 146,219, LSEC = 9,521, DRV = 3), no image number.
   FAMILY (the kit owner's ruling, 2026-10-29 ~17:25Z: the post-implication form, a YES with five conditions).
   tfuzz_malloc_specX, tfuzz_realloc_specX, tfuzz_strdup_specX and tfuzz_free_specX are LEAVES in the
   POST-IMPLICATION form: no entry position, no entry run premise, no model-run binder at entry. Each arm of the post
   states the position transfer as an implication quantified over the model run, at that arm's OWN event list E
   (keyed on the value the post binds, res or p, not on a model grant list):
     forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i E ->
       exists hist', PresetRoomPos.iface_room_pos sm x os (i + length E)%nat H0 hist' S'
   E is [HMal (n + cf_head)] at a granted malloc, strdup (n = len + 1) or realloc (NULL, n); [HRe (k + cf_head)
   (n + cf_head)] at a granted realloc of a live block; [HFr (n + cf_head)] at a non-NULL free; [] at every NULL
   return and at a NULL free (the identity on the position, stated). fuzz_free's bulk arm has the same shape at the
   bulk sub-position: iface_room_pos_bulk sm x os i L k H0 hb S -> prh_run_at sm x os i [HBulk L] -> nth_error L k =
   Some (n + cf_head) -> exists hb', iface_room_pos_bulk sm x os i L (S k) H0 hb' S' (the event at i is pj_free's
   bulk; the advance is k to S k, and i stays). ONLY the position is under the implication: the result, the memory,
   the ledger, the blocks and the room facts are unconditional. The advance is EXACT, i + length E, never <=.
   THE RUN PREMISE is PRH_Base.prh_run_at, not nth_error: it is the spelling a caller splits its own list with
   (prh_run_at_app_iff), and at one event PRH_Base.prh_run_at_one makes it the same statement as
   nth_error (PresetRun.hruns sm x os) i = Some ev. NOT `exists i' hist', i <= i' /\ iface_room_pos .. i' .. S'`:
   that is false at the end of a run (the recursive-reader author's witness: i = length hruns with |d| = 3; a successful allocation
   needs a fourth d entry and there is no later position).
   SUPPLY (condition 3): every E here is one event or none. PRH_Base.prh_run_at_one turns the caller's (or the
   model's) nth_error (PresetRun.hruns sm x os) i = Some ev into prh_run_at sm x os i [ev]; a caller holding its own
   list splits it at this call with PRH_Base.prh_run_at_app_iff; E = [] needs nothing (prh_run_at sm x os i [] is
   firstn 0 _ = [], by reflexivity).
   THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS; the kit owner's ruling ~18:5xZ): fuzz_malloc,
   fuzz_realloc and fuzz_strdup also state, under the same run quantifier, that at a CONSUMER allocation of the run
   (PRH_Base.prh_cons_from over PresetRun.hcons) whose next event is the call's GRANTED one, with cnt <> fail (no
   injected failure at this call), res <> 0 and S' is the position after that event. It is P8's exclusion
   (PresetP8.no_null_preset) with the environment's grant the engine gives on every realized path (amreal; PRH_Base's
   prh_rpost_granted), restated inside the post: the walk applies it at its own malloc_cf, the only place that can.
   So a NULL arm's E = [] is used only off a consumer position or at the chosen failure; the refusal arm stays (the
   header's ROOM paragraph), and fuzz_free, which allocates nothing, has no outcome clause.
   WHAT A CALLER NOW DOES: it calls these texts with no position. At its own end it chains the post implications in
   call order, choosing the model run (sm x os), the start i and H0 then: the hist' one implication gives is the hist
   the next one takes (the PresetRoomPos / PresetRoomPosKeep keeps carry it across the steps between calls), and the
   advances add up to the length of the caller's own list (prh_run_at_app_iff).
   CALLS: post-form texts call only post-form texts. Here fuzz_realloc's p = 0 arm is fuzz_malloc's (a tail call) and
   fuzz_strdup calls fuzz_malloc. The seven accessors and own state no position and make no model event, so a text of
   either family may call them. The entry-keyed family (writer / tx / round-trip / crcs / as_written: an ENTRY-keyed
   list plus the rp_on entry spelling) may call these leaves too.
   THE ROOM FACTS ARE POSITION-FREE entry premises. fuzz_malloc, fuzz_realloc and fuzz_strdup keep
   sec_cnt S <= LSEC + DRV and ccnt24 S <= L24 + DRV at entry: the allocation itself needs them (a8's RL_malloc_step /
   RL_realloc_step, for room_live_cf S'). They name no position. The CALLER supplies them; after a refusal the
   supply is the open half, on the ledger side (the P8 owner's ledger-side bound). fuzz_free (the kit owner's ORDER 1
   + 2) takes p <> 0 -> room_live_cf S and p <> 0 -> ccnt24 S <= L24 + DRV: a NULL free frees nothing and makes no event, so
   its arm needs no room fact and no position; the post gives the bound back as an implication,
   ccnt24 S <= L24 + DRV -> ccnt24 S' <= L24 + DRV.
   THE HULL BUDGET (route (b) of the allocator hull premise; lib/Spec/PresetHullBudget.v): the
   allocator call needs the ASan owner's admission cf_hull_ok at its entry (acall_pre_cf, QM_cf_of_room) and a realloc tree
   the entry headroom cf_hull_adm, and these texts have no position to derive them from. So fuzz_malloc,
   fuzz_realloc and fuzz_strdup take `hull_budget S Eg` (room for the call's one event Eg; at preset's CfParams it IS
   cf_hull_adm S (n + cf_head), lib/A/PresetHullPay.v hull_adm_of_budget_mal / _re), fuzz_free takes
   `p <> 0 -> hull_budget S []` (cf_hull_ok S: a NULL free calls nothing), and each post states `hull_used S S' Eg`
   with the SAME Eg (the meters grew by at most the call's charge; 0 on a NULL arm). A caller with no position pays
   the budget from its own (PresetHullBudget.hull_budget_app), a caller with one from the run's count
   (PresetHullPay.hull_budget_of_room_pos).
   Statements only. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep PresetRun
  PresetReqAt PresetHullBudget.
(* the re-hiding move's SRr' and wle' (YA0nH), preset's zone (YGcfRehidePost.RZ_cf), and
   exh_mem_cf for the world-free refusal (YG00cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YG00cf.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

(* ---- the accessors and setters of the statics (alloc.c :129-162): no call, no block, Hp kept; the statics they
   write are PST, so their FP is empty ---- *)

(* fuzz_alloc_live (:129-132): returns g_live *)
Definition tfuzz_alloc_live_specX : Prop :=
  forall ly S Hp W regs mem md ch Lam peak cnt fail ran most own,
  fpre B ARx STK_fuzz_alloc_live ly S Hp W regs mem md ch ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_live) regs mem md)
    (fpostm B ARx SK STK_fuzz_alloc_live [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       getr regs' 10 = w64 (Ledger.lsum Lam) /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own)).

(* fuzz_alloc_peak (:134-137): returns g_peak *)
Definition tfuzz_alloc_peak_specX : Prop :=
  forall ly S Hp W regs mem md ch Lam peak cnt fail ran most own,
  fpre B ARx STK_fuzz_alloc_peak ly S Hp W regs mem md ch ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_peak) regs mem md)
    (fpostm B ARx SK STK_fuzz_alloc_peak [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       getr regs' 10 = w64 peak /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own)).

(* fuzz_alloc_peak_reset (:139-142): g_peak = g_live *)
Definition tfuzz_alloc_peak_reset_specX : Prop :=
  forall ly S Hp W regs mem md ch Lam peak cnt fail ran most own,
  fpre B ARx STK_fuzz_alloc_peak_reset ly S Hp W regs mem md ch ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_peak_reset) regs mem md)
    (fpostm B ARx SK STK_fuzz_alloc_peak_reset [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam (Ledger.lsum Lam) cnt fail ran most own)).

(* fuzz_alloc_count (:144-147): returns g_count *)
Definition tfuzz_alloc_count_specX : Prop :=
  forall ly S Hp W regs mem md ch Lam peak cnt fail ran most own,
  fpre B ARx STK_fuzz_alloc_count ly S Hp W regs mem md ch ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_count) regs mem md)
    (fpostm B ARx SK STK_fuzz_alloc_count [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       getr regs' 10 = w64 cnt /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own)).

(* fuzz_alloc_fail (:149-152): g_fail_at = k < SIZE_MAX - g_count ? g_count + k : SIZE_MAX *)
Definition tfuzz_alloc_fail_specX : Prop :=
  forall ly S Hp W regs mem md ch Lam peak cnt fail ran k most own,
  fpre B ARx STK_fuzz_alloc_fail ly S Hp W regs mem md ch ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  getr regs 10 = w64 k -> 0 <= k < 2 ^ 64 ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_fail) regs mem md)
    (fpostm B ARx SK STK_fuzz_alloc_fail [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt (if k <? SIZE_MAXZ - cnt then cnt + k else SIZE_MAXZ) ran most own)).

(* fuzz_alloc_ran_out (:154-157): returns g_ran_out (an int, 0 or 1) *)
Definition tfuzz_alloc_ran_out_specX : Prop :=
  forall ly S Hp W regs mem md ch Lam peak cnt fail ran most own,
  fpre B ARx STK_fuzz_alloc_ran_out ly S Hp W regs mem md ch ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_ran_out) regs mem md)
    (fpostm B ARx SK STK_fuzz_alloc_ran_out [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       getr regs' 10 = w64 ran /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own)).

(* fuzz_alloc_ran_out_reset (:159-162): g_ran_out = 0 *)
Definition tfuzz_alloc_ran_out_reset_specX : Prop :=
  forall ly S Hp W regs mem md ch Lam peak cnt fail ran most own,
  fpre B ARx STK_fuzz_alloc_ran_out_reset ly S Hp W regs mem md ch ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_ran_out_reset) regs mem md)
    (fpostm B ARx SK STK_fuzz_alloc_ran_out_reset [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail 0 most own)).

(* ---- the allocation wrappers (S1) ---- *)

(* what one harness allocation of n user bytes leaves (alloc.c fuzz_malloc :65-76 with own :45-53). g_count + 1 on
   every arm; the request n + cf_head is admissible (premise), so alloc.c's TOOBIG arm is excluded. Three arms:
   (1) CHOSEN-FAIL, the allocation fuzz_alloc_fail set to fail (failing() :37-43): NULL, g_fail_at = SIZE_MAX, no
       allocator call; g_ran_out, the blocks and Hp unchanged;
   (2) REFUSED, the allocator's NULL (the class-full arm) - KEPT ON PURPOSE, see the header: the driver, not this
       text, excludes it - : NULL, g_ran_out := 1 if n <= g_most (refused(), below; a ONE-byte static in the image: LLVM
       shrank `static int g_ran_out`; its asan_globals descriptor size is 1, generated as pi_gz_ran_out);
       the block list, Hp and Lam unchanged; the refusal writes errno 12 and the OOM byte (as_errno B,
       as_oom_byte B), which the journal allows, and no client byte; the arm carries the refusal leaf
       malloc_cf_null_post (the allocator-model owner's YG0dcf.v:315: a refused call writes no client byte, only errno 12 and the OOM
       byte; blocks and chunks unchanged; exh_mem_cf on n's class, the conjunct malloc_cf_success_of_room refutes),
       from the pre allocator state S, Hp and world W (no allocator step precedes the call) to the POST allocator
       state S', at request n + cf_head, so a caller with room refutes the arm;
   (3) SUCCESS: a new block at res - cf_head of n + cf_head bytes, its head holding n and hidden (Hp gains
       res - cf_head), its n user bytes readable (their values are what the allocator left: any), g_live += n,
       g_peak = max (g_peak, g_live). *)
(* THE REFUSAL'S TWO CELLS (the S1 owner's agreement 14:30:49Z, the kit owner's ruling): on a REFUSAL - never on the
   injected failure, which is failing() alone (g_count + 1, g_fail_at := SIZE_MAX) - refused() (merged alloc.c:70-78)
   does g_peak := max (g_peak, min SIZE_MAX (g_live + n)) and g_ran_out := 1 ONLY when n <= g_most. So the arm needs
   g_most's value, and prh_alloc_post takes it. The TOOBIG path (n > SIZE_MAX - HEAD) calls refused(n) too, without
   the C library, and is the same arm: this text does not omit it, because the arm is keyed on res = 0 and the
   leaf, not on which NULL the library gave. *)
Definition prh_alloc_post (n : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (Lam : list (Z * Z))
  (peak cnt fail ran most own : Z)
  (res : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) : Prop :=
  (cnt = fail /\ res = 0 /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
   prh_ledger B ly' S' Hp' W' mem' Lam peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ ran most own)
  \/
  (cnt <> fail /\ res = 0 /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
   (exists regsc memc mdc Wc cc, malloc_cf_null_post segs B ly S Hp W regsc memc mdc (n + cf_head) (PNull, S') Wc cc) /\
   rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\
   prh_ledger B ly' S' Hp' W' mem' Lam (Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam + n)))
     ((cnt + 1) mod 2 ^ 64) fail (if n <=? most then 1 else ran) most own)
  \/
  (cnt <> fail /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\ ~ In res (map fst Lam) /\
   Hp' = (res - cf_head) :: Hp /\
   ablocks B ly' S' = ablocks B ly S ++ [(res - cf_head, n + cf_head)] /\
   range_addressable (aview segs (w_H W') mem') SHADOW_OFF res n /\
   (0 < n -> shadow_hull_vis (aview segs (w_H W') mem') res n) /\
   (exists l, Z.of_nat (length l) = n /\ bytes_at W' mem' res l) /\
   prh_ledger B ly' S' Hp' W' mem' ((res, n) :: Lam) (Z.max peak (Ledger.lsum Lam + n))
     ((cnt + 1) mod 2 ^ 64) fail ran most own).

(* THE BLOCK AT res - cf_head IS FRESH, from the append equality alone (the kit owner's ruling: one home, because three
   lanes would otherwise write these four lines). prh_alloc_post's success arm gives
   `ablocks B ly' S' = ablocks B ly S ++ [(res - cf_head, n + cf_head)]` (arm 3); with NoDup of the block BASES at the
   post state (ARcf's Wf_cf, carried through ajournal_x; the walk supplies it) `In new (ablocks B ly S)` would put
   new's base twice in ablocks B ly' S'. No proof cites it (grow_at_kept0's callers use PwGrowG.v:995 grow_alloc_fresh_append).
   WHY THE TWO SITES DIFFER, so a reader does not re-open the question: only REALLOC removes a block, so only its
   permutation form (`Permutation (ablocks B ly' S') (new :: b1 ++ b2)`) can hide the new block among the ones left
   alone; every arm that goes through prh_alloc_post's APPEND equality is safe for that reason. That is why
   tfuzz_realloc_specX's success arm needed the explicit `~ In .. (b1 ++ b2)` and its p = 0 arm does not, and
   fuzz_strdup is safe for the same reason.
   NAMED FOR THE ARM IT SERVES (the kit owner's ruling on the recursive-reader author's worry): this lemma takes the APPEND equality, so it
   does not apply at realloc's PERMUTATION arm. Realloc's success arm has the permutation form instead, and its block
   freshness is stated DIRECTLY in the text, `~ In (res - cf_head, n + cf_head) (b1 ++ b2)` in tfuzz_realloc_specX -
   cite that there, not this. *)
Lemma prh_alloc_fresh_append : forall ly S ly' S' res n,
  ablocks B ly' S' = ablocks B ly S ++ [(res - cf_head, n + cf_head)] ->
  List.NoDup (map fst (ablocks B ly' S')) ->
  ~ In (res - cf_head, n + cf_head) (ablocks B ly S).
Proof.
  intros ly S ly' S' res n E ND Hin.
  rewrite E, map_app in ND. cbn [map fst] in ND.
  apply List.NoDup_remove_2 in ND. apply ND. rewrite app_nil_r.
  exact (in_map fst (ablocks B ly S) (res - cf_head, n + cf_head) Hin).
Qed.

(* fuzz_malloc (:65-76). The request n + cf_head is below the instance's cf_malloc_max (so `n <= SIZE_MAX - HEAD`
   holds and the allocator takes it: amalloc_realizes_cf's `0 <= n < cf_malloc_max`); the live user bytes stay within
   LIVE_MAX (amalloc_realizes_cf's premise; LIVE_MAX is the bound Wf_cf keeps on blocks_bytes; it is not a class-room
   premise). Write set: the statics (PST), the new block's head, the frame. *)
Definition tfuzz_malloc_specX : Prop :=
  forall ly S Hp W regs mem md ch n Lam peak cnt fail ran most own,
  fpre B ARx STK_fuzz_malloc ly S Hp W regs mem md ch -> room_live_cf S -> prh_malloc_univ B ->
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* THE HULL BUDGET (the header): room for this call's one event *)
  PresetHullBudget.hull_budget S [PresetReqAt.HMal (n + cf_head)] ->
  getr regs 10 = w64 n -> 0 <= n -> n + cf_head < cf_malloc_max ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (* PER-CALL, SO GUARDED BY ITS CALL'S SUCCESS FLAG (the unit owner's peak-bytes-102 signing; the same shape as
     tfuzz_strdup's below and tpj_string's): at the CHOSEN FAILURE (cnt = fail) alloc.c makes no allocator call at
     all, so there is no event to charge and nothing to bound - and the model agrees: prhWriter_evs (PRH_FnWriter.v:199) emits
     NO event at that grow. The live-event walk measured that the UNGUARDED form left a writer walk stuck on exactly that
     arm once the callers' LIVE premise moved to the per-event form, because neither an event nor the live-bytes owner's
     blocks_bytes_bound_preset can cover a call that does not happen. *)
  (cnt <> fail -> blocks_bytes S + (n + cf_head) <= LIVE_MAX) ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_malloc) regs mem md)
    (fpostm B ARx SK STK_fuzz_malloc [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       exists res, getr regs' 10 = w64 res /\ room_live_cf S' /\
       (* THE HULL USE (the header): at most the entry budget's event *)
       PresetHullBudget.hull_used S S' [PresetReqAt.HMal (n + cf_head)] /\
       (* THE POSITION, POST-IMPLICATION (the header's FAMILY): no position at entry; each arm transfers any position
          of any model run whose next events are this arm's own E, by EXACTLY length E. A NULL makes no event
          (E = [], the identity on the position, stated); a grant makes HMal (n + cf_head). The history is
          existential (the one form for every leaf; the kit names blocks by address, the PresetRoomPosKeep steps by
          allocator pointer). *)
       (res = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [] ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S') /\
       (res <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (n + cf_head)] ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (n + cf_head)])%nat H0
            hist' S') /\
       (* THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS): at a CONSUMER allocation of a model run whose
          next event is this call's granted HMal, with no injected failure at this call (cnt <> fail), the instance
          GRANTED and S' is the position after it. So the NULL clause above (E = []) is used only off a consumer
          position or at the chosen failure. *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (n + cf_head)] ->
          PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal (n + cf_head)]) -> cnt <> fail ->
          res <> 0 /\
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (n + cf_head)])%nat H0
            hist' S') /\
       prh_alloc_post n ly S Hp W Lam peak cnt fail ran most own res ly' S' Hp' W' mem')).

(* fuzz_free (:118-127): p = NULL returns; else disown (unpoison the head: Hp loses p - cf_head; g_live -= n) and
   free the allocator block by a TAIL CALL with the caller's ra and the frame popped (A 0x85830), so the free's trace
   is call_trace of the ENTRY registers and chain, and the walk ends in afree_realizes_cf's post (cgif aj_free_at,
   YCbq.v:992-1010: the block list loses exactly that block). The freed block is in the journal footprint. *)
Definition tfuzz_free_specX : Prop :=
  forall most own,
  forall ly S Hp W regs mem md ch p n Lam peak cnt fail ran,
  fpre B ARx STK_fuzz_free ly S Hp W regs mem md ch ->
  (* ORDER 2, completed (the corollary walk / the leaf walk: the free-caller walker's NULL-free callability rests on it): a NULL free needs no
     room invariant either - its post keeps S' = S *)
  (p <> 0 -> room_live_cf S) ->
  (* The kit owner's ORDER 1 + 2: no position at entry, and the class-24 bound only for a non-NULL free (a NULL free
     frees nothing and makes no event, so that arm takes no room fact) *)
  (p <> 0 -> YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV) ->
  (* THE HULL BUDGET (the header): the admission at a non-NULL free; a free makes no secondary entry *)
  (p <> 0 -> PresetHullBudget.hull_budget S []) ->
  (* THE FREE'S TRACE IN THE ENGINE'S OWN FORM (the unit owner's reviewer, 23:46Z): afree_realizes_cf's premise,
     `admits (as_universe B) (call_trace ..) S` (YG0d.v:286, YG0dcf.v:452). The old `In (call_trace ..) (as_universe B)`
     meant, through the coercion u_fix, the FIXED list, which the cursor callers cannot supply on B' (their trace
     carries a DATA word), and the closure's clause 4b gives only `inU`, a DISJUNCTION (YG01.v:145-146) whose fixed half
     cannot be extracted. SUPPLIERS: a caller whose trace is fixed (clauses 1-3, 4a of PRH_Base.prh_univ_closure)
     supplies it by YG01.admits_fix; a CURSOR caller (parse_string, parse_items) supplies it from clause 4b plus the
     ROOM COUNT (|wild_part| < u_wmax), so those rows stay CONDITIONAL ON THE COUNT THREAD (owned by the S1 owner, not
     proved). The cursor walks do so: a FIXED trace (prh_univ_closure_cur) is admitted at every state, a CW trace by
     YCbqGwild.wild_room_admits(_laws): parse_string lib/A/Prog/S4_PsFree.v:375-391 (HISTORY: it used prh_cur_ok at
     c7796752a117), parse_items lib/A/VrdIKeyB.v:1611-1622 / lib/B/Prog/PItems_body_free.v:732-740. *)
  admits (as_universe B) (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S ->
  getr regs 10 = w64 p -> (p = 0 \/ In (p, n) Lam) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.1): a non-NULL free can recycle a secondary,
     so the run ends at wle' segs RZ_cf. The post fpostbm is AFTER-FREE-ONLY and already at wle' (PRH_Base.v) *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_fuzz_free) regs mem md)
    (* THE POST IS BUDGETED AT THIS CALL'S OWN TRACE (the wild-budget walk's finding on the admits premise above, the unit owner's
       answer 23:24Z (a) + (c)). With a WILD trace admitted, this free STORES it, and the plain fpostm - the journal
       at the EMPTY budget, whose last conjunct is `incl (wild_part U (st_depot S')) (wild_part U (st_depot S))` -
       is FALSE. So the post states the journal at a budget WS of which this text claims `wbudget SET 0 WS`, SET
       being the one trace this call can store: p = 0 stores nothing (WS = []) and p <> 0 stores exactly that trace
       (YCbqGwild.wfresh_one_in), so k is 0 either way. NO CALLER THAT STORES ONLY FIXED TRACES CHANGES: it reads
       the old post back through PRH_Base.fpost_of_fpostb_fix. Only the CURSOR callers (parse_string, parse_items),
       whose trace carries a data word on B', carry the budget, and their texts name it CW. *)
    (fpostbm B ARx SK
       (YCbqGwild.wbudget [call_trace ly (pc_free_ra0 (as_code B)) regs ch] 0)
       STK_fuzz_free (if p =? 0 then [] else ablocks_fp [(p - cf_head, n + cf_head)])
       regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (p <> 0 -> room_live_cf S') /\
       (* THE HULL USE (the header): a free keeps both meters *)
       PresetHullBudget.hull_used S S' [] /\
       (* THE POSITION, POST-IMPLICATION (the header's FAMILY; tfuzz_malloc_specX's note): a NULL free makes no event
          (E = []); a non-NULL free at the run's own free event makes HFr (n + cf_head); a non-NULL free inside a
          pj_free's bulk event HBulk L at i moves the bulk sub-position from k to S k (i stays: the bulk is ONE event
          of the run). *)
       (p = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [] ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S') /\
       (p <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i [PresetReqAt.HFr (n + cf_head)] ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HFr (n + cf_head)])%nat H0
            hist' S') /\
       (p <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (L : list Z) (k : nat) (hb : list YG00.chunk),
          PresetRoomPosKeep.iface_room_pos_bulk sm x os i L k H0 hb S ->
          PRH_Base.prh_run_at sm x os i [PresetReqAt.HBulk L] ->
          nth_error L k = Some (n + cf_head) ->
          exists hb', PresetRoomPosKeep.iface_room_pos_bulk sm x os i L (Datatypes.S k) H0 hb' S') /\
       (* THE BOUND IS KEPT (the kit owner's ruling on the image-B pj_free walk): a free NEVER raises ccnt24,
          so the callee says so once and every caller of fuzz_free gets it. pj_free's FOUR fuzz_free calls
          (B 0x86660 / 0x86694 / 0x866ac / 0x866c8, NULL frees included) each pass the bound on from pj_free's entry
          bound. An IMPLICATION since ORDER 2: the entry gives the bound only for p <> 0, and a NULL free keeps S, so
          an unconditional bound at S' is not available on that arm. The alternative, a caller carrying the bound at
          every state along the post-order free list, would put a per-call invariant into every caller of a function
          that cannot break it. *)
       (YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
        YGcfRoomLive.ccnt24 S' <= PresetLiveBounds.L24 + PresetLiveBounds.DRV) /\
       (* AND EXACTLY (the S1 owner's measurement, `CCNT24-FREE.md (sha256 1bcb7d8e0845; internal record)`; the kit owner's ruling): ccnt24 counts only
          ALLOCATED chunks whose request is class 24 (YGcfRoomLive.ccnt24; quarantined chunks and batches are n24's).
          A NULL free never calls free_cf, so the state is unchanged; a non-NULL free removes exactly its own block,
          whose request is n + cf_head, and no free_cf step adds an allocated chunk (the quarantine batch grows the
          class-24 REGION and n24, not ccnt24). The inequality above follows by lia; the equality is stated so a later
          consumer that needs it does not re-open the text. *)
       ((p = 0 /\ S' = S /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
        prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own)
       \/
       (p <> 0 /\ Hp' = remove Z.eq_dec (p - cf_head) Hp /\
        YGcfRoomLive.ccnt24 S' + Z.of_nat (PresetRoom.ccnt YG00.kBatchClass [n + cf_head]) = YGcfRoomLive.ccnt24 S /\
        (exists b1 b2, ablocks B ly S = b1 ++ (p - cf_head, n + cf_head) :: b2 /\ ablocks B ly' S' = b1 ++ b2) /\
        exists l1 l2, Lam = l1 ++ (p, n) :: l2 /\
        prh_ledger B ly' S' Hp' W' mem' (l1 ++ l2) peak cnt fail ran most own)))).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tfuzz_free_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. tffP_Q IS the text's post (tffP_Q_check fails to build if
   the two ever differ); tffP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition tffP_A1 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (p : Z) (Lam : list (Z * Z)) (peak cnt fail
    ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) : Prop :=
  p = 0 /\ S' = S /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail
      ran most own.

Definition tffP_A2 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (p n : Z) (Lam : list (Z * Z)) (peak cnt
    fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) : Prop :=
  p <> 0 /\ Hp' = remove Z.eq_dec (p - cf_head) Hp /\ YGcfRoomLive.ccnt24 S' + Z.of_nat (PresetRoom.ccnt
      YG00.kBatchClass [n + cf_head]) = YGcfRoomLive.ccnt24 S /\ (exists b1 b2, ablocks B ly S = b1 ++ (p - cf_head, n
      + cf_head) :: b2 /\ ablocks B ly' S' = b1 ++ b2) /\ exists l1 l2, Lam = l1 ++ (p, n) :: l2 /\ prh_ledger B ly' S'
      Hp' W' mem' (l1 ++ l2) peak cnt fail ran most own.

Definition tffP_Q (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (p n : Z) (Lam : list (Z * Z)) (peak cnt
    fail ran : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  (p <> 0 -> room_live_cf S') /\ PresetHullBudget.hull_used S S' [] /\ (p = 0 -> forall (sm : list Z -> Z * Z) (x :
      list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
      PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [] -> exists hist',
      PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S') /\ (p <> 0 -> forall
      (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z)
      (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i
      [PresetReqAt.HFr (n + cf_head)] -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length
      [PresetReqAt.HFr (n + cf_head)])%nat H0 hist' S') /\ (p <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os :
      list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (L : list Z) (k : nat) (hb : list
      YG00.chunk), PresetRoomPosKeep.iface_room_pos_bulk sm x os i L k H0 hb S -> PRH_Base.prh_run_at sm x os i
      [PresetReqAt.HBulk L] -> nth_error L k = Some (n + cf_head) -> exists hb', PresetRoomPosKeep.iface_room_pos_bulk
      sm x os i L (Datatypes.S k) H0 hb' S') /\ (YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV
      -> YGcfRoomLive.ccnt24 S' <= PresetLiveBounds.L24 + PresetLiveBounds.DRV) /\ (tffP_A1 most own ly S Hp p Lam peak
      cnt fail ran ly' S' Hp' W' mem' \/ tffP_A2 most own ly S Hp p n Lam peak cnt fail ran ly' S' Hp' W' mem').

Lemma tffP_Q_check : tfuzz_free_specX -> tfuzz_free_specX.
Proof.
  intros H. unfold tfuzz_free_specX in *.
  intros most own ly S Hp W regs mem md ch p n Lam peak cnt fail ran HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (tffP_Q most own ly S Hp p n Lam
      peak cnt fail ran) end.
  exact (H most own ly S Hp W regs mem md ch p n Lam peak cnt fail ran HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7).
Qed.

Record tffP_R (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (p n : Z) (Lam : list (Z * Z)) (peak cnt fail
    ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word ->
    option byte) : Prop := {
  tffP_room : (p <> 0 -> room_live_cf S');
  tffP_hull : PresetHullBudget.hull_used S S' [];
  tffP_pos_null : (p = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option
      nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
      PRH_Base.prh_run_at sm x os i [] -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil
      PresetReqAt.hev))%nat H0 hist' S');
  tffP_pos_free : (p <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option
      nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
      PRH_Base.prh_run_at sm x os i [PresetReqAt.HFr (n + cf_head)] -> exists hist', PresetRoomPos.iface_room_pos sm x
      os (i + length [PresetReqAt.HFr (n + cf_head)])%nat H0 hist' S');
  tffP_pos_bulk : (p <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option
      nat)) (i : nat) (H0 : list Z) (L : list Z) (k : nat) (hb : list YG00.chunk),
      PresetRoomPosKeep.iface_room_pos_bulk sm x os i L k H0 hb S -> PRH_Base.prh_run_at sm x os i [PresetReqAt.HBulk
      L] -> nth_error L k = Some (n + cf_head) -> exists hb', PresetRoomPosKeep.iface_room_pos_bulk sm x os i L
      (Datatypes.S k) H0 hb' S');
  tffP_ccnt24 : (YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV -> YGcfRoomLive.ccnt24 S' <=
      PresetLiveBounds.L24 + PresetLiveBounds.DRV);
  tffP_arm : (tffP_A1 most own ly S Hp p Lam peak cnt fail ran ly' S' Hp' W' mem' \/ tffP_A2 most own ly S Hp p n Lam
      peak cnt fail ran ly' S' Hp' W' mem') }.

Lemma tffP_R_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (p n : Z) (Lam : list (Z * Z)) (peak
    cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' :
    word -> option byte) (md' : Model),
  tffP_Q most own ly S Hp p n Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' ->
  tffP_R most own ly S Hp p n Lam peak cnt fail ran ly' S' Hp' W' regs' mem'.
Proof.
  intros most own ly S Hp p n Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' H. destruct H as (H0 & H1 & H2 & H3 &
      H4 & H5 & H6).
  exact {| tffP_room := H0; tffP_hull := H1; tffP_pos_null := H2; tffP_pos_free := H3; tffP_pos_bulk := H4; tffP_ccnt24
      := H5; tffP_arm := H6 |}.
Qed.

Lemma tffP_Q_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (p n : Z) (Lam : list (Z * Z))
    (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem'
    : word -> option byte) (md' : Model),
  tffP_R most own ly S Hp p n Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ->
  tffP_Q most own ly S Hp p n Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md'.
Proof.
  intros most own ly S Hp p n Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' HR.
  exact (conj (tffP_room HR) (conj (tffP_hull HR) (conj (tffP_pos_null HR) (conj (tffP_pos_free HR) (conj
      (tffP_pos_bulk HR) (conj (tffP_ccnt24 HR) (tffP_arm HR))))))).
Qed.

Record tffP_R1 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (p : Z) (Lam : list (Z * Z)) (peak cnt fail ran
    : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) : Prop := {
  tffP1_null : p = 0;
  tffP1_state : S' = S;
  tffP1_hp : Hp' = Hp;
  tffP1_ablocks : ablocks B ly' S' = ablocks B ly S;
  tffP1_ledger : prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own }.

Lemma tffP_R1_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (p : Z) (Lam : list (Z * Z)) (peak
    cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte),
  tffP_A1 most own ly S Hp p Lam peak cnt fail ran ly' S' Hp' W' mem' ->
  tffP_R1 most own ly S Hp p Lam peak cnt fail ran ly' S' Hp' W' mem'.
Proof.
  intros most own ly S Hp p Lam peak cnt fail ran ly' S' Hp' W' mem' H. destruct H as (H0 & H1 & H2 & H3 & H4).
  exact {| tffP1_null := H0; tffP1_state := H1; tffP1_hp := H2; tffP1_ablocks := H3; tffP1_ledger := H4 |}.
Qed.

Lemma tffP_A1_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (p : Z) (Lam : list (Z * Z)) (peak
    cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte),
  tffP_R1 most own ly S Hp p Lam peak cnt fail ran ly' S' Hp' W' mem' ->
  tffP_A1 most own ly S Hp p Lam peak cnt fail ran ly' S' Hp' W' mem'.
Proof.
  intros most own ly S Hp p Lam peak cnt fail ran ly' S' Hp' W' mem' HR.
  exact (conj (tffP1_null HR) (conj (tffP1_state HR) (conj (tffP1_hp HR) (conj (tffP1_ablocks HR) (tffP1_ledger HR))))).
Qed.

Record tffP_R2 (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (p n : Z) (Lam : list (Z * Z)) (peak cnt fail
    ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (l1 l2 : list
    (Z * Z)) : Prop := {
  tffP2_nonnull : p <> 0;
  tffP2_hp : Hp' = remove Z.eq_dec (p - cf_head) Hp;
  tffP2_ccnt24 : YGcfRoomLive.ccnt24 S' + Z.of_nat (PresetRoom.ccnt YG00.kBatchClass [n + cf_head]) =
      YGcfRoomLive.ccnt24 S;
  tffP2_ablocks : (exists b1 b2, ablocks B ly S = b1 ++ (p - cf_head, n + cf_head) :: b2 /\ ablocks B ly' S' = b1 ++
      b2);
  tffP2_lam : Lam = l1 ++ (p, n) :: l2;
  tffP2_ledger : prh_ledger B ly' S' Hp' W' mem' (l1 ++ l2) peak cnt fail ran most own }.

Lemma tffP_R2_of : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (p n : Z) (Lam : list (Z * Z)) (peak
    cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte),
  tffP_A2 most own ly S Hp p n Lam peak cnt fail ran ly' S' Hp' W' mem' ->
  exists l1 l2, tffP_R2 most own ly S Hp p n Lam peak cnt fail ran ly' S' Hp' W' mem' l1 l2.
Proof.
  intros most own ly S Hp p n Lam peak cnt fail ran ly' S' Hp' W' mem' H. destruct H as (H0 & H1 & H2 & H3 & l1 & l2 &
      H4 & H5).
  exists l1, l2.
  exact {| tffP2_nonnull := H0; tffP2_hp := H1; tffP2_ccnt24 := H2; tffP2_ablocks := H3; tffP2_lam := H4; tffP2_ledger
      := H5 |}.
Qed.

Lemma tffP_A2_of_R : forall (most own : Z) (ly : alayout) (S : astate) (Hp : list Z) (p n : Z) (Lam : list (Z * Z))
    (peak cnt fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte)
    (l1 l2 : list (Z * Z)),
  tffP_R2 most own ly S Hp p n Lam peak cnt fail ran ly' S' Hp' W' mem' l1 l2 ->
  tffP_A2 most own ly S Hp p n Lam peak cnt fail ran ly' S' Hp' W' mem'.
Proof.
  intros most own ly S Hp p n Lam peak cnt fail ran ly' S' Hp' W' mem' l1 l2 HR.
  refine (conj (tffP2_nonnull HR) (conj (tffP2_hp HR) (conj (tffP2_ccnt24 HR) (conj (tffP2_ablocks HR) _)))).
  exists l1, l2.
  exact (conj (tffP2_lam HR) (tffP2_ledger HR)).
Qed.

Local Unset Implicit Arguments.

(* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 4.1; route (i) of the unit owner's
   18:51Z item (2)): fuzz_free (NULL) (:122-123, `if (!p) return;`), THE NULL-ONLY TEXT, UNPRIMED ON PURPOSE. The walk
   is the frame, beqz a0 taken, the epilogue, ret: NO CALL IS MADE, so free is never reached, no allocator row is a
   premise, nothing is freed or recycled, no shadow is re-hidden, and the post holds at plain wle (SRr, fpostm) under
   every route. A caller that frees NULL takes THIS text: tfuzz_free_specX above concludes SRr' segs RZ_cf, and at
   p = 0 that would cost the caller its plain SRr for nothing (YA0nH lifts SRr to SRr', SRr_SRr'; nothing lowers it at
   RZ_cf, which is not empty).
   Weaker premises than tfuzz_free_specX at p = 0: no room invariant, no live-set bound, no hull budget, no trace
   premise (no call is made, so no trace is stored), no block n. The post is fpostm at FP = [] with S' = S, so the room,
   the run position, the class-24 bound, the hull meters and the wild budget (WS = []) all carry over from S by the
   caller's own facts.
   TAKERS: crs_free0 (lib/A/Prog/CrsFree0Ap.v) and crs_free0_B (lib/B/Prog/CrsFree0Bp.v, this text at prh_img_B), proved
   from it by CrsBridgeAp.crs_free0_of_text / CrsBridgeBp.crs_free0_of_text_B, one SRr_mono each: room after the call
   from S' = S; the trace premise goes unused. PROOF: lib/A/Prog/FuzzFreeNull.v fuzz_free_null_holds and
   lib/B/Prog/FuzzFreeNullB.v fuzz_free_null_holds_B, each one SRr_mono over the S1 owner's walk ff_p0 (FuzzFree.v:601 /
   FuzzFreeB.v:483; it puts the memnorm keep inside Q, fQmn outside), at afn_pre_x, the first conjunct of fpre. *)
Definition tfuzz_free_null_specX : Prop :=
  forall most own,
  forall ly S Hp W regs mem md ch Lam peak cnt fail ran,
  fpre B ARx STK_fuzz_free ly S Hp W regs mem md ch ->
  getr regs 10 = w64 0 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_free) regs mem md)
    (fpostm B ARx SK STK_fuzz_free [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       S' = S /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own)).

(* fuzz_realloc (:87-106). p = NULL is a TAIL CALL of fuzz_malloc (n) after the frame pops (A 0x85480): that arm is
   fuzz_malloc's post at n, with g_count counted once, by fuzz_malloc. Otherwise g_count + 1, then:
   CHOSEN-FAIL: NULL, the old block untouched and still hidden;
   REFUSED: disown (Hp loses p - cf_head), realloc NULL, refused() (g_ran_out := 1 if n <= g_most), the old block
     owned again (its head rewritten with the same k, hidden again: Hp is the same set, p - cf_head moved to the front,
     so a PERMUTATION), NULL; the arm carries WORLD-FREE the four conjuncts of the inner malloc's refusal leaf
     malloc_cf_null_post that a refusal changes (below), not the leaf at a world;
   SUCCESS: the new block owned (Hp = (res - cf_head) :: remove (p - cf_head) Hp), holding the first min (k, n) old
     bytes; g_live = g_live - k + n.
   The realloc call holds n in s0 too, so its trace is constant (cf_pc_realloc_ra0, the call's return site).
   Write set: the statics (PST), the old head, the new head, the frame. *)
Definition tfuzz_realloc_specX : Prop :=
  forall ly S Hp W regs mem md ch p k n (old : list Z) Lam peak cnt fail ran most own,
  fpre B ARx STK_fuzz_realloc ly S Hp W regs mem md ch -> room_live_cf S -> prh_malloc_univ B ->
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* THE HULL BUDGET (the header): room for this call's one event, HMal at p = 0, HRe at p <> 0 (the same charge) *)
  PresetHullBudget.hull_budget S
    (if p =? 0 then [PresetReqAt.HMal (n + cf_head)] else [PresetReqAt.HRe (k + cf_head) (n + cf_head)]) ->
  (* the realloc pair, code-only (fuzz_realloc holds n in s0: empty chain), in the FIXED part explicitly *)
  In [cf_pc_realloc_ra0] (u_fix (as_universe B)) ->
  In (prh_trace cf_pc_realloc_ra0 pi_ret_realloc []) (u_fix (as_universe B)) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 n -> 0 <= n -> n + cf_head < cf_malloc_max ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (p = 0 /\ k = 0 /\ old = [] \/ In (p, k) Lam /\ bytes_at W mem p old /\ Z.of_nat (length old) = k) ->
  (* PER-CALL, SO GUARDED BY ITS CALL'S SUCCESS FLAG (the unit owner's peak-bytes-102 signing; the same shape as
     tfuzz_strdup's below and tpj_string's): at the CHOSEN FAILURE (cnt = fail) alloc.c makes no allocator call at
     all, so there is no event to charge and nothing to bound - and the model agrees: prhWriter_evs (PRH_FnWriter.v:199) emits
     NO event at that grow. The live-event walk measured that the UNGUARDED form left a writer walk stuck on exactly that
     arm once the callers' LIVE premise moved to the per-event form, because neither an event nor the live-bytes owner's
     blocks_bytes_bound_preset can cover a call that does not happen. *)
  (cnt <> fail -> blocks_bytes S + (n + cf_head) <= LIVE_MAX) ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.2): a realloc of a live block frees the old
     block, so the run ends at wle' segs RZ_cf. fpostm is SHARED, so the post is its R form at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_fuzz_realloc) regs mem md)
    (fpostmR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) STK_fuzz_realloc
      (if p =? 0 then [] else ablocks_fp [(p - cf_head, k + cf_head)])
       regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       exists res, getr regs' 10 = w64 res /\ room_live_cf S' /\
       (* THE HULL USE (the header): at most the entry budget's event *)
       PresetHullBudget.hull_used S S'
         (if p =? 0 then [PresetReqAt.HMal (n + cf_head)] else [PresetReqAt.HRe (k + cf_head) (n + cf_head)]) /\
       (* THE POSITION, POST-IMPLICATION (the header's FAMILY; tfuzz_malloc_specX's note): a NULL makes no event
          (E = []); a grant at p = 0 is fuzz_malloc's, HMal (n + cf_head); a grant at p <> 0 makes
          HRe (k + cf_head) (n + cf_head). *)
       (res = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [] ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S') /\
       (res <> 0 -> p = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (n + cf_head)] ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (n + cf_head)])%nat H0
            hist' S') /\
       (res <> 0 -> p <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i [PresetReqAt.HRe (k + cf_head) (n + cf_head)] ->
          exists hist', PresetRoomPos.iface_room_pos sm x os
            (i + length [PresetReqAt.HRe (k + cf_head) (n + cf_head)])%nat H0 hist' S') /\
       (* THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS; tfuzz_malloc_specX's note): at a CONSUMER
          allocation of a model run whose next event is this call's granted one (p = 0: fuzz_malloc's HMal; p <> 0:
          HRe), with no injected failure at this call (cnt <> fail), the instance GRANTED and S' is the position
          after it. *)
       (p = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (n + cf_head)] ->
          PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal (n + cf_head)]) -> cnt <> fail ->
          res <> 0 /\
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (n + cf_head)])%nat H0
            hist' S') /\
       (p <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i [PresetReqAt.HRe (k + cf_head) (n + cf_head)] ->
          PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HRe (k + cf_head) (n + cf_head)]) -> cnt <> fail ->
          res <> 0 /\
          exists hist', PresetRoomPos.iface_room_pos sm x os
            (i + length [PresetReqAt.HRe (k + cf_head) (n + cf_head)])%nat H0 hist' S') /\
       ((p = 0 /\ prh_alloc_post n ly S Hp W Lam peak cnt fail ran most own res ly' S' Hp' W' mem')
        \/
        (p <> 0 /\ cnt = fail /\ res = 0 /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
         bytes_at W' mem' p old /\
         prh_ledger B ly' S' Hp' W' mem' Lam peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ ran most own)
        \/
        (p <> 0 /\ cnt <> fail /\ res = 0 /\ Permutation Hp' Hp /\ ablocks B ly' S' = ablocks B ly S /\
         bytes_at W' mem' p old /\
         (* WORLD-FREE (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 5.1): the four conjuncts of
            malloc_cf_null_post that a refusal changes, with NO world (the old witness was malloc_cf_null_post at
            the entry world W, which the primed row gives only where its dead set is empty). Weaker than the old
            witness; the allocator-model owner's realloc_cf_refused_state gives it from the primed row (lib/Reusable/YGcfRealloc.v:136) *)
         (blocks S' = blocks S /\ st_chunks S' = st_chunks S /\
          from_primary (n + cf_head) = true /\ YG00cf.exh_mem_cf S' (chunk_class (n + cf_head)) = true) /\
         rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\
         (* THE ONLY ARM IN THIS FAMILY WHERE THE LEDGER READS A g_live THAT IS NOT THE CALLER'S
            (the kit owner's amendment, 14:31Z): refused() runs AFTER disown (merged alloc.c:104-128), so g_live at
            that moment is live - k, and the peak takes live - k + n. own (b, old) then restores g_live = live and
            its g_peak = max (g_peak, g_live) changes nothing, because live <= peak by prh_glob.
            realloc (NULL, n) is the p = 0 arm and goes through prh_alloc_post at live + n. *)
         prh_ledger B ly' S' Hp' W' mem' Lam (Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam - k + n)))
           ((cnt + 1) mod 2 ^ 64) fail (if n <=? most then 1 else ran) most own)
        \/
        (p <> 0 /\ cnt <> fail /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\
         exists l1 l2, Lam = l1 ++ (p, k) :: l2 /\ ~ In res (map fst (l1 ++ l2)) /\
         Hp' = (res - cf_head) :: remove Z.eq_dec (p - cf_head) Hp /\
         (exists b1 b2, ablocks B ly S = b1 ++ (p - cf_head, k + cf_head) :: b2 /\
            (* the new BLOCK is fresh, not only the harness pointer (the S5a2 walk on grow A, the image-B grow walk on B):
               the block at res - cf_head need not be a harness block at the entry state, so without this the new
               block could be one of the blocks the realloc left alone, and then the node the caller must still place
               (prhReader_at at the post state) could sit in the new block's hidden head [res - cf_head, res), where
               neither case of prhReader_at holds. The S5a2 walk's grow_at_kept takes it as a premise today. *)
            ~ In (res - cf_head, n + cf_head) (b1 ++ b2) /\
            Permutation (ablocks B ly' S') ((res - cf_head, n + cf_head) :: b1 ++ b2)) /\
         (exists rest, Z.of_nat (length rest) = n - Z.min k n /\
            bytes_at W' mem' res (firstn (Z.to_nat (Z.min k n)) old ++ rest)) /\
         range_addressable (aview segs (w_H W') mem') SHADOW_OFF res n /\
         (0 < n -> shadow_hull_vis (aview segs (w_H W') mem') res n) /\
         prh_ledger B ly' S' Hp' W' mem' ((res, n) :: l1 ++ l2) (Z.max peak (Ledger.lsum (l1 ++ l2) + n))
           ((cnt + 1) mod 2 ^ 64) fail ran most own)))).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tfuzz_realloc_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. tfrP_Q IS the text's post (tfrP_Q_check fails to build if
   the two ever differ); tfrP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition tfrP_A1 (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (p n : Z) (Lam : list (Z * Z)) (peak cnt
    fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte)
    (res : Z) : Prop :=
  p = 0 /\ prh_alloc_post n ly S Hp W Lam peak cnt fail ran most own res ly' S' Hp' W' mem'.

Definition tfrP_A2 (ly : alayout) (S : astate) (Hp : list Z) (p : Z) (old : list Z) (Lam : list (Z * Z)) (peak cnt fail
    ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (res
    : Z) : Prop :=
  p <> 0 /\ cnt = fail /\ res = 0 /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\ bytes_at W' mem' p old /\
      prh_ledger B ly' S' Hp' W' mem' Lam peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ ran most own.

Definition tfrP_A3 (ly : alayout) (S : astate) (Hp : list Z) (p k n : Z) (old : list Z) (Lam : list (Z * Z)) (peak cnt
    fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte)
    (res : Z) : Prop :=
  p <> 0 /\ cnt <> fail /\ res = 0 /\ Permutation Hp' Hp /\ ablocks B ly' S' = ablocks B ly S /\ bytes_at W' mem' p old
      /\ (blocks S' = blocks S /\ st_chunks S' = st_chunks S /\ from_primary (n + cf_head) = true /\ YG00cf.exh_mem_cf
      S' (chunk_class (n + cf_head)) = true) /\ rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ prh_ledger B ly' S'
      Hp' W' mem' Lam (Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam - k + n))) ((cnt + 1) mod 2 ^ 64) fail (if n <=?
      most then 1 else ran) most own.

Definition tfrP_A4 (ly : alayout) (S : astate) (Hp : list Z) (p k n : Z) (old : list Z) (Lam : list (Z * Z)) (peak cnt
    fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte)
    (res : Z) : Prop :=
  p <> 0 /\ cnt <> fail /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\ exists l1 l2, Lam = l1 ++ (p, k) :: l2 /\ ~ In
      res (map fst (l1 ++ l2)) /\ Hp' = (res - cf_head) :: remove Z.eq_dec (p - cf_head) Hp /\ (exists b1 b2, ablocks B
      ly S = b1 ++ (p - cf_head, k + cf_head) :: b2 /\ ~ In (res - cf_head, n + cf_head) (b1 ++ b2) /\ Permutation
      (ablocks B ly' S') ((res - cf_head, n + cf_head) :: b1 ++ b2)) /\ (exists rest, Z.of_nat (length rest) = n -
      Z.min k n /\ bytes_at W' mem' res (firstn (Z.to_nat (Z.min k n)) old ++ rest)) /\ range_addressable (aview segs
      (w_H W') mem') SHADOW_OFF res n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W') mem') res n) /\ prh_ledger B
      ly' S' Hp' W' mem' ((res, n) :: l1 ++ l2) (Z.max peak (Ledger.lsum (l1 ++ l2) + n)) ((cnt + 1) mod 2 ^ 64) fail
      ran most own.

Definition tfrP_Q (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (p k n : Z) (old : list Z) (Lam : list (Z
    * Z)) (peak cnt fail ran most own : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  exists res, getr regs' 10 = w64 res /\ room_live_cf S' /\ PresetHullBudget.hull_used S S' (if p =? 0 then
      [PresetReqAt.HMal (n + cf_head)] else [PresetReqAt.HRe (k + cf_head) (n + cf_head)]) /\ (res = 0 -> forall (sm :
      list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist :
      list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [] -> exists
      hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S') /\ (res <> 0 ->
      p = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
      (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at
      sm x os i [PresetReqAt.HMal (n + cf_head)] -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length
      [PresetReqAt.HMal (n + cf_head)])%nat H0 hist' S') /\ (res <> 0 -> p <> 0 -> forall (sm : list Z -> Z * Z) (x :
      list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
      PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [PresetReqAt.HRe (k + cf_head)
      (n + cf_head)] -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HRe (k + cf_head)
      (n + cf_head)])%nat H0 hist' S') /\ (p = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat *
      option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os
      i H0 hist S -> PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (n + cf_head)] -> PRH_Base.prh_cons_from sm x os i
      (length [PresetReqAt.HMal (n + cf_head)]) -> cnt <> fail -> res <> 0 /\ exists hist',
      PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (n + cf_head)])%nat H0 hist' S') /\ (p <> 0 ->
      forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0 :
      list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os
      i [PresetReqAt.HRe (k + cf_head) (n + cf_head)] -> PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HRe (k +
      cf_head) (n + cf_head)]) -> cnt <> fail -> res <> 0 /\ exists hist', PresetRoomPos.iface_room_pos sm x os (i +
      length [PresetReqAt.HRe (k + cf_head) (n + cf_head)])%nat H0 hist' S') /\ (tfrP_A1 ly S Hp W p n Lam peak cnt
      fail ran most own ly' S' Hp' W' mem' res \/ tfrP_A2 ly S Hp p old Lam peak cnt fail ran most own ly' S' Hp' W'
      mem' res \/ tfrP_A3 ly S Hp p k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res \/ tfrP_A4 ly S Hp p
      k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res).

Lemma tfrP_Q_check : tfuzz_realloc_specX -> tfuzz_realloc_specX.
Proof.
  intros H. unfold tfuzz_realloc_specX in *.
  intros ly S Hp W regs mem md ch p k n old Lam peak cnt fail ran most own HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10
      HP11 HP12 HP13 HP14.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (tfrP_Q ly S Hp W p k n old Lam
      peak cnt fail ran most own) end.
  exact (H ly S Hp W regs mem md ch p k n old Lam peak cnt fail ran most own HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9
      HP10 HP11 HP12 HP13 HP14).
Qed.

Record tfrP_R (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (p k n : Z) (old : list Z) (Lam : list (Z *
    Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap
    5 word) (mem' : word -> option byte) (res : Z) : Prop := {
  tfrP_ret : getr regs' 10 = w64 res;
  tfrP_room : room_live_cf S';
  tfrP_hull : PresetHullBudget.hull_used S S' (if p =? 0 then [PresetReqAt.HMal (n + cf_head)] else [PresetReqAt.HRe (k
      + cf_head) (n + cf_head)]);
  tfrP_pos_null : (res = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option
      nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
      PRH_Base.prh_run_at sm x os i [] -> exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil
      PresetReqAt.hev))%nat H0 hist' S');
  tfrP_pos_malloc : (res <> 0 -> p = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option
      nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0
      hist S -> PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (n + cf_head)] -> exists hist',
      PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (n + cf_head)])%nat H0 hist' S');
  tfrP_pos_realloc : (res <> 0 -> p <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option
      nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0
      hist S -> PRH_Base.prh_run_at sm x os i [PresetReqAt.HRe (k + cf_head) (n + cf_head)] -> exists hist',
      PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HRe (k + cf_head) (n + cf_head)])%nat H0 hist' S');
  tfrP_outcome_malloc : (p = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat *
      option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S
      -> PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (n + cf_head)] -> PRH_Base.prh_cons_from sm x os i (length
      [PresetReqAt.HMal (n + cf_head)]) -> cnt <> fail -> res <> 0 /\ exists hist', PresetRoomPos.iface_room_pos sm x
      os (i + length [PresetReqAt.HMal (n + cf_head)])%nat H0 hist' S');
  tfrP_outcome_realloc : (p <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat *
      option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S
      -> PRH_Base.prh_run_at sm x os i [PresetReqAt.HRe (k + cf_head) (n + cf_head)] -> PRH_Base.prh_cons_from sm x os
      i (length [PresetReqAt.HRe (k + cf_head) (n + cf_head)]) -> cnt <> fail -> res <> 0 /\ exists hist',
      PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HRe (k + cf_head) (n + cf_head)])%nat H0 hist' S');
  tfrP_arm : (tfrP_A1 ly S Hp W p n Lam peak cnt fail ran most own ly' S' Hp' W' mem' res \/ tfrP_A2 ly S Hp p old Lam
      peak cnt fail ran most own ly' S' Hp' W' mem' res \/ tfrP_A3 ly S Hp p k n old Lam peak cnt fail ran most own ly'
      S' Hp' W' mem' res \/ tfrP_A4 ly S Hp p k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res) }.

Lemma tfrP_R_of : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (p k n : Z) (old : list Z) (Lam :
    list (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  tfrP_Q ly S Hp W p k n old Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md' ->
  exists res, tfrP_R ly S Hp W p k n old Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' res.
Proof.
  intros ly S Hp W p k n old Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md' H. destruct H as (res & H0 &
      H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  exists res.
  exact {| tfrP_ret := H0; tfrP_room := H1; tfrP_hull := H2; tfrP_pos_null := H3; tfrP_pos_malloc := H4;
      tfrP_pos_realloc := H5; tfrP_outcome_malloc := H6; tfrP_outcome_realloc := H7; tfrP_arm := H8 |}.
Qed.

Lemma tfrP_Q_of_R : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (p k n : Z) (old : list Z) (Lam :
    list (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (res : Z),
  tfrP_R ly S Hp W p k n old Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' res ->
  tfrP_Q ly S Hp W p k n old Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md'.
Proof.
  intros ly S Hp W p k n old Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md' res HR.
  exists res.
  exact (conj (tfrP_ret HR) (conj (tfrP_room HR) (conj (tfrP_hull HR) (conj (tfrP_pos_null HR) (conj (tfrP_pos_malloc
      HR) (conj (tfrP_pos_realloc HR) (conj (tfrP_outcome_malloc HR) (conj (tfrP_outcome_realloc HR) (tfrP_arm
      HR))))))))).
Qed.

(* the CONSEQUENTS of tfrP_R's guarded conjuncts, NAMED: each conjunct of an implication's conclusion, read from
   the record through one lemma (a consumer that applies the guard and destructs its conclusion is not broken by the
   next conjunct appended there) *)

Lemma tfrP_outcome_malloc_ok : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (p k n : Z) (old :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (res : Z),
  tfrP_R ly S Hp W p k n old Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' res ->
  p = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0
      : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x
      os i [PresetReqAt.HMal (n + cf_head)] -> PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal (n +
      cf_head)]) -> cnt <> fail ->
  res <> 0.
Proof.
  intros ly S Hp W p k n old Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' res HR HP0 sm x os i H0 hist HP1
      HP2 HP3 HP4.
  pose proof (tfrP_outcome_malloc HR) as G.
  exact (proj1 (G HP0 sm x os i H0 hist HP1 HP2 HP3 HP4)).
Qed.

Lemma tfrP_outcome_malloc_pos : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (p k n : Z) (old :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (res : Z),
  tfrP_R ly S Hp W p k n old Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' res ->
  p = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0
      : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x
      os i [PresetReqAt.HMal (n + cf_head)] -> PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal (n +
      cf_head)]) -> cnt <> fail ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (n + cf_head)])%nat H0 hist' S'.
Proof.
  intros ly S Hp W p k n old Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' res HR HP0 sm x os i H0 hist HP1
      HP2 HP3 HP4.
  pose proof (tfrP_outcome_malloc HR) as G.
  exact (proj2 (G HP0 sm x os i H0 hist HP1 HP2 HP3 HP4)).
Qed.

Lemma tfrP_outcome_realloc_ok : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (p k n : Z) (old :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (res : Z),
  tfrP_R ly S Hp W p k n old Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' res ->
  p <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0
      : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x
      os i [PresetReqAt.HRe (k + cf_head) (n + cf_head)] -> PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HRe
      (k + cf_head) (n + cf_head)]) -> cnt <> fail ->
  res <> 0.
Proof.
  intros ly S Hp W p k n old Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' res HR HP0 sm x os i H0 hist HP1
      HP2 HP3 HP4.
  pose proof (tfrP_outcome_realloc HR) as G.
  exact (proj1 (G HP0 sm x os i H0 hist HP1 HP2 HP3 HP4)).
Qed.

Lemma tfrP_outcome_realloc_pos : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (p k n : Z) (old :
    list Z) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (res : Z),
  tfrP_R ly S Hp W p k n old Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' res ->
  p <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat) (H0
      : list Z) (hist : list YG00.chunk), PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x
      os i [PresetReqAt.HRe (k + cf_head) (n + cf_head)] -> PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HRe
      (k + cf_head) (n + cf_head)]) -> cnt <> fail ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HRe (k + cf_head) (n + cf_head)])%nat H0
      hist' S'.
Proof.
  intros ly S Hp W p k n old Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' res HR HP0 sm x os i H0 hist HP1
      HP2 HP3 HP4.
  pose proof (tfrP_outcome_realloc HR) as G.
  exact (proj2 (G HP0 sm x os i H0 hist HP1 HP2 HP3 HP4)).
Qed.

Record tfrP_R1 (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (p n : Z) (Lam : list (Z * Z)) (peak cnt fail
    ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (res
    : Z) : Prop := {
  tfrP1_null : p = 0;
  tfrP1_alloc : prh_alloc_post n ly S Hp W Lam peak cnt fail ran most own res ly' S' Hp' W' mem' }.

Lemma tfrP_R1_of : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (p n : Z) (Lam : list (Z * Z))
    (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word ->
    option byte) (res : Z),
  tfrP_A1 ly S Hp W p n Lam peak cnt fail ran most own ly' S' Hp' W' mem' res ->
  tfrP_R1 ly S Hp W p n Lam peak cnt fail ran most own ly' S' Hp' W' mem' res.
Proof.
  intros ly S Hp W p n Lam peak cnt fail ran most own ly' S' Hp' W' mem' res H. destruct H as (H0 & H1).
  exact {| tfrP1_null := H0; tfrP1_alloc := H1 |}.
Qed.

Lemma tfrP_A1_of_R : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (p n : Z) (Lam : list (Z * Z))
    (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word ->
    option byte) (res : Z),
  tfrP_R1 ly S Hp W p n Lam peak cnt fail ran most own ly' S' Hp' W' mem' res ->
  tfrP_A1 ly S Hp W p n Lam peak cnt fail ran most own ly' S' Hp' W' mem' res.
Proof.
  intros ly S Hp W p n Lam peak cnt fail ran most own ly' S' Hp' W' mem' res HR.
  exact (conj (tfrP1_null HR) (tfrP1_alloc HR)).
Qed.

Record tfrP_R2 (ly : alayout) (S : astate) (Hp : list Z) (p : Z) (old : list Z) (Lam : list (Z * Z)) (peak cnt fail ran
    most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (res : Z)
    : Prop := {
  tfrP2_nonnull : p <> 0;
  tfrP2_chosen : cnt = fail;
  tfrP2_res0 : res = 0;
  tfrP2_hp : Hp' = Hp;
  tfrP2_ablocks : ablocks B ly' S' = ablocks B ly S;
  tfrP2_bytes : bytes_at W' mem' p old;
  tfrP2_ledger : prh_ledger B ly' S' Hp' W' mem' Lam peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ ran most own }.

Lemma tfrP_R2_of : forall (ly : alayout) (S : astate) (Hp : list Z) (p : Z) (old : list Z) (Lam : list (Z * Z)) (peak
    cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option
    byte) (res : Z),
  tfrP_A2 ly S Hp p old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res ->
  tfrP_R2 ly S Hp p old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res.
Proof.
  intros ly S Hp p old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res H. destruct H as (H0 & H1 & H2 & H3 & H4 &
      H5 & H6).
  exact {| tfrP2_nonnull := H0; tfrP2_chosen := H1; tfrP2_res0 := H2; tfrP2_hp := H3; tfrP2_ablocks := H4; tfrP2_bytes
      := H5; tfrP2_ledger := H6 |}.
Qed.

Lemma tfrP_A2_of_R : forall (ly : alayout) (S : astate) (Hp : list Z) (p : Z) (old : list Z) (Lam : list (Z * Z)) (peak
    cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option
    byte) (res : Z),
  tfrP_R2 ly S Hp p old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res ->
  tfrP_A2 ly S Hp p old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res.
Proof.
  intros ly S Hp p old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res HR.
  exact (conj (tfrP2_nonnull HR) (conj (tfrP2_chosen HR) (conj (tfrP2_res0 HR) (conj (tfrP2_hp HR) (conj (tfrP2_ablocks
      HR) (conj (tfrP2_bytes HR) (tfrP2_ledger HR))))))).
Qed.

Record tfrP_R3 (ly : alayout) (S : astate) (Hp : list Z) (p k n : Z) (old : list Z) (Lam : list (Z * Z)) (peak cnt fail
    ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (res
    : Z) : Prop := {
  tfrP3_nonnull : p <> 0;
  tfrP3_notchosen : cnt <> fail;
  tfrP3_res0 : res = 0;
  tfrP3_hp : Permutation Hp' Hp;
  tfrP3_ablocks : ablocks B ly' S' = ablocks B ly S;
  tfrP3_bytes : bytes_at W' mem' p old;
  tfrP3_evidence : (blocks S' = blocks S /\ st_chunks S' = st_chunks S /\ from_primary (n + cf_head) = true /\
      YG00cf.exh_mem_cf S' (chunk_class (n + cf_head)) = true);
  tfrP3_errno : rd32 (aview segs (w_H W') mem') (as_errno B) 12;
  tfrP3_ledger : prh_ledger B ly' S' Hp' W' mem' Lam (Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam - k + n))) ((cnt +
      1) mod 2 ^ 64) fail (if n <=? most then 1 else ran) most own }.

Lemma tfrP_R3_of : forall (ly : alayout) (S : astate) (Hp : list Z) (p k n : Z) (old : list Z) (Lam : list (Z * Z))
    (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word ->
    option byte) (res : Z),
  tfrP_A3 ly S Hp p k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res ->
  tfrP_R3 ly S Hp p k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res.
Proof.
  intros ly S Hp p k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res H. destruct H as (H0 & H1 & H2 & H3 &
      H4 & H5 & H6 & H7 & H8).
  exact {| tfrP3_nonnull := H0; tfrP3_notchosen := H1; tfrP3_res0 := H2; tfrP3_hp := H3; tfrP3_ablocks := H4;
      tfrP3_bytes := H5; tfrP3_evidence := H6; tfrP3_errno := H7; tfrP3_ledger := H8 |}.
Qed.

Lemma tfrP_A3_of_R : forall (ly : alayout) (S : astate) (Hp : list Z) (p k n : Z) (old : list Z) (Lam : list (Z * Z))
    (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word ->
    option byte) (res : Z),
  tfrP_R3 ly S Hp p k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res ->
  tfrP_A3 ly S Hp p k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res.
Proof.
  intros ly S Hp p k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res HR.
  exact (conj (tfrP3_nonnull HR) (conj (tfrP3_notchosen HR) (conj (tfrP3_res0 HR) (conj (tfrP3_hp HR) (conj
      (tfrP3_ablocks HR) (conj (tfrP3_bytes HR) (conj (tfrP3_evidence HR) (conj (tfrP3_errno HR) (tfrP3_ledger
      HR))))))))).
Qed.

Record tfrP_R4 (ly : alayout) (S : astate) (Hp : list Z) (p k n : Z) (old : list Z) (Lam : list (Z * Z)) (peak cnt fail
    ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (res
    : Z) (l1 l2 : list (Z * Z)) : Prop := {
  tfrP4_nonnull : p <> 0;
  tfrP4_notchosen : cnt <> fail;
  tfrP4_res_min : 4096 + cf_head <= res;
  tfrP4_res_align : res mod 16 = 0;
  tfrP4_lam : Lam = l1 ++ (p, k) :: l2;
  tfrP4_fresh : ~ In res (map fst (l1 ++ l2));
  tfrP4_hp : Hp' = (res - cf_head) :: remove Z.eq_dec (p - cf_head) Hp;
  tfrP4_ablocks : (exists b1 b2, ablocks B ly S = b1 ++ (p - cf_head, k + cf_head) :: b2 /\ ~ In (res - cf_head, n +
      cf_head) (b1 ++ b2) /\ Permutation (ablocks B ly' S') ((res - cf_head, n + cf_head) :: b1 ++ b2));
  tfrP4_bytes : (exists rest, Z.of_nat (length rest) = n - Z.min k n /\ bytes_at W' mem' res (firstn (Z.to_nat (Z.min k
      n)) old ++ rest));
  tfrP4_addressable : range_addressable (aview segs (w_H W') mem') SHADOW_OFF res n;
  tfrP4_hull : (0 < n -> shadow_hull_vis (aview segs (w_H W') mem') res n);
  tfrP4_ledger : prh_ledger B ly' S' Hp' W' mem' ((res, n) :: l1 ++ l2) (Z.max peak (Ledger.lsum (l1 ++ l2) + n)) ((cnt
      + 1) mod 2 ^ 64) fail ran most own }.

Lemma tfrP_R4_of : forall (ly : alayout) (S : astate) (Hp : list Z) (p k n : Z) (old : list Z) (Lam : list (Z * Z))
    (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word ->
    option byte) (res : Z),
  tfrP_A4 ly S Hp p k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res ->
  exists l1 l2, tfrP_R4 ly S Hp p k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res l1 l2.
Proof.
  intros ly S Hp p k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res H. destruct H as (H0 & H1 & H2 & H3 &
      l1 & l2 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  exists l1, l2.
  exact {| tfrP4_nonnull := H0; tfrP4_notchosen := H1; tfrP4_res_min := H2; tfrP4_res_align := H3; tfrP4_lam := H4;
      tfrP4_fresh := H5; tfrP4_hp := H6; tfrP4_ablocks := H7; tfrP4_bytes := H8; tfrP4_addressable := H9; tfrP4_hull :=
      H10; tfrP4_ledger := H11 |}.
Qed.

Lemma tfrP_A4_of_R : forall (ly : alayout) (S : astate) (Hp : list Z) (p k n : Z) (old : list Z) (Lam : list (Z * Z))
    (peak cnt fail ran most own : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word ->
    option byte) (res : Z) (l1 l2 : list (Z * Z)),
  tfrP_R4 ly S Hp p k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res l1 l2 ->
  tfrP_A4 ly S Hp p k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res.
Proof.
  intros ly S Hp p k n old Lam peak cnt fail ran most own ly' S' Hp' W' mem' res l1 l2 HR.
  refine (conj (tfrP4_nonnull HR) (conj (tfrP4_notchosen HR) (conj (tfrP4_res_min HR) (conj (tfrP4_res_align HR) _)))).
  exists l1, l2.
  exact (conj (tfrP4_lam HR) (conj (tfrP4_fresh HR) (conj (tfrP4_hp HR) (conj (tfrP4_ablocks HR) (conj (tfrP4_bytes HR)
      (conj (tfrP4_addressable HR) (conj (tfrP4_hull HR) (tfrP4_ledger HR)))))))).
Qed.

Local Unset Implicit Arguments.

(* fuzz_strdup (:108-116): n = strlen (s) + 1 (the strlen wrapper), fuzz_malloc (n), and on success __asan_memcpy
   (d, s, n). The string is read by the strlen interceptor and by __asan_memcpy, so it is a cstr_ok; __asan_memcpy
   needs its shadow facts AFTER fuzz_malloc, which a journal does not keep, so the string lies where the shadow is
   kept (kept_at: a live harness block, or a registered read-only global by in_zs with the image margins; the
   cgif-lineage form of the walking hand's correction). cstr_ok already puts it below the stack, so no stack case.
   The arms are fuzz_malloc's at n = len + 1. *)
Definition tfuzz_strdup_specX : Prop :=
  forall ly S Hp W regs mem md ch s (cs : list Z) Lam peak cnt fail ran most own,
  fpre B ARx STK_fuzz_strdup ly S Hp W regs mem md ch -> room_live_cf S -> prh_malloc_univ B ->
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* THE HULL BUDGET (the header): room for fuzz_malloc's one event at n = len + 1 *)
  PresetHullBudget.hull_budget S [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)] ->
  getr regs 10 = w64 s -> cstr_ok W mem s cs ->
  kept_at B Lam s (Z.of_nat (length cs) + 1) ->
  Z.of_nat (length cs) + 1 + cf_head < cf_malloc_max ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (* PER-CALL, SO GUARDED BY ITS CALL'S SUCCESS FLAG (the unit owner's peak-bytes-102 signing, 2026-10-29; the same
     shape as tpj_string's and as the tx rows' `f0 = 0 ->` room guard): the bytes this call adds are owed only on the
     path where the allocation HAPPENS, that is at cnt <> fail. The live-bytes owner proves the entry sums (M1 + M2 + M6,
     statement owned by the S1 owner); the kit's half is the guard. *)
  (cnt <> fail -> blocks_bytes S + (Z.of_nat (length cs) + 1 + cf_head) <= LIVE_MAX) ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_strdup) regs mem md)
    (fpostm B ARx SK STK_fuzz_strdup [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       exists res, getr regs' 10 = w64 res /\ room_live_cf S' /\
       (* THE HULL USE (the header): at most the entry budget's event *)
       PresetHullBudget.hull_used S S' [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)] /\
       (* THE POSITION, POST-IMPLICATION (the header's FAMILY; tfuzz_malloc_specX's note): fuzz_malloc's arms at
          n = len + 1; a NULL makes no event (E = []), a grant makes HMal (len + 1 + cf_head). *)
       (res = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [] ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S') /\
       (res <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)] ->
          exists hist', PresetRoomPos.iface_room_pos sm x os
            (i + length [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)])%nat H0 hist' S') /\
       (* THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS; tfuzz_malloc_specX's note), at
          n = len + 1 *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
          (i : nat) (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)] ->
          PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)]) ->
          cnt <> fail ->
          res <> 0 /\
          exists hist', PresetRoomPos.iface_room_pos sm x os
            (i + length [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)])%nat H0 hist' S') /\
       prh_alloc_post (Z.of_nat (length cs) + 1) ly S Hp W Lam peak cnt fail ran most own res ly' S' Hp' W' mem' /\
       (res <> 0 -> bytes_at W' mem' res (cs ++ [0])))).

(* own (alloc.c :45-53; out of line in image B only, B 0x8595c; inlined in image A's fuzz_malloc / fuzz_realloc):
   memcpy (b, &n, 8) into the head of a live allocator block that is not hidden, poison [b, b + cf_head) (Hp gains b),
   g_live += n, g_peak = max (g_peak, g_live), return b + cf_head. The head word is the only block byte written, so
   it is the footprint (the statics are PST). Called from fuzz_malloc after a successful malloc and from fuzz_realloc
   after realloc (success: the new block; refusal: the old block again). NO ROOM_cf premise: see the header.
   errno is KEPT, stated: own writes only the head, the statics and its frame, and errno is exempt from the journal's
   image clause, so without this clause errno 12 is lost across own in B's fuzz_realloc refused arm (B 0x85bb4;
   the S1 owner's measurement). *)
Definition town_specX : Prop :=
  forall ly S Hp W regs mem md ch b n Lam peak cnt fail ran most own,
  fpre B ARx STK_own ly S Hp W regs mem md ch ->
  getr regs 10 = w64 b -> getr regs 11 = w64 n -> 0 <= n ->
  In (b, n + cf_head) (ablocks B ly S) -> b mod 16 = 0 -> 4096 <= b ->
  ~ In (b + cf_head) (map fst Lam) ->
  Ledger.lsum Lam + n < 2 ^ 64 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_own) regs mem md)
    (fpostm B ARx SK STK_own [(b, b + 8)] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\ S' = S /\ ly' = ly /\
       getr regs' 10 = w64 (b + cf_head) /\ Hp' = b :: Hp /\ ablocks B ly' S' = ablocks B ly S /\
       (forall a, as_errno B <= a < as_errno B + 4 -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
       prh_ledger B ly' S' Hp' W' mem' ((b + cf_head, n) :: Lam) (Z.max peak (Ledger.lsum Lam + n)) cnt fail ran most own)).

End c.
