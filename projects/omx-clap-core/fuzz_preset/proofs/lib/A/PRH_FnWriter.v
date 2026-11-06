(* This file carries the kit's text of the re-hiding move for its five crossing texts
   (`PRIMED-SHAPES.md (sha256 9e4880d18317; internal record)` sec. 2.16-2.20): each concludes SRr' segs RZ_cf. tput / tindent (fpostWm) and tput_string /
   twrite_value (fpostWFm) are SHARED families, so their posts are the R forms at wle' segs RZ_cf; tpj_write keeps
   fpostFm, which is AFTER-FREE-ONLY and already at wle' (PRH_Base.v).
   The unit owner's ruling C2 (2026-10-31 04:19Z) struck the scratch notice that stood here, by a
   comment-only edit that keeps the header at 6 lines, so every line after it keeps its number. *)
(* fuzz_preset, program part (the kit): the ASan contract TEXTS of preset_file.c's writer (@246923f04ac0 :447-571):
   put, indent, put_string, write_value and pj_write, in cgif's per-function form (cgif_file lib/YC21.v:33-66; the fm port's
   FMH_Fn.v:101-180), over YCbqG's journal and PRH_Base.v's kit: fpre (YCbqG's afn_pre_x + the read-only view), the
   argument registers, the allocation traces in the image's universe (the writer grows its buffer through
   fuzz_realloc), the alloc.c ledger (prh_ledger), and SRr' segs RZ_cf to the return address. Every conclusion is
   `srealizes` through SRr' segs RZ_cf (lib/Reusable/YA0nH.v:163, over SRrG :27-30 at wle' :147).
   IMAGE-PARAMETRIC: the image is the listing class (YC4aP PAImg L); each entry is pa_sigma AS_<fn>; no image constant
   is named here (the addresses in comments are image A's, for the reader only).
   ALLOCATOR-PARAMETRIC: ARx is an explicit argument; the walks instantiate it at the allocator-model owner's ARcf segs B.
   The FUNCTIONAL content is preset's released plain contracts lib/Prog/{put,indent,put_string,write_value,pj_write}_c.v,
   restated over the pure models WriterSpec.v (spieces, newcap), WriterApp.v (wst, put1, w0) and WriterValue.v (wind,
   wvpieces, wdpieces, wdoc), and the tree predicate pj_nodeR of lib/A/PRH_Reader.v (the recursive-reader author; plain PjStruct.pj_node
   restated over val_mem / garr8 / writable_at, same shape) over mrestrict (w_H W) mem with lblk prh_lin Lam. No plain
   lemma is cited; the plain texts are not ported (they conclude in SR); no plain lib/Prog file other than the pure
   models (WriterSpec, WriterApp, WriterValue, Ledger) is Required.
   - THE WRITER STATE (struct pj_out, :447-452) is restated as prhWriter_out from the plain put_c.v:52-63 pj_out_ok.
     It lives in pj_write's own frame (`addi a0, sp, 8`, A 0x866ec), so put / indent / put_string / write_value write
     their CALLER's frame. Their post is the caller-window post fpostWR at wle' (PRH_Base.v; FMH_Fn.v:211-231 form):
     YCbqG's ajournal_xR at (STK + d) (spZ regs + d), with fwin, spZ regs <= o and o + 32 <= spZ regs + d; the struct's
     32 bytes are IN FP (prhWriter_cfp), so every other byte of [spZ regs, spZ regs + d) is kept. The callers chain d:
     pj_write passes d = its frame; a callee of write_value gets write_value's d plus write_value's frame; a tail call
     keeps d. pj_write itself uses fpostFm (no window; already at wle').
   - ALLOCATION OUTCOMES: the class-full allocator can refuse any fuzz_realloc; put then sets o->failed = 1 (:466-470)
     exactly as for the allocation fuzz_alloc_fail set to fail. The plain put1 (WriterApp.v:15-25) decides the outcome
     by cnt = fail alone; prhWriter_put1 adds the outcome bool of PRH_Base.v's prh_oks (a refused grow: failed, the
     text and the buffer kept, g_count + 1, g_fail_at kept, g_ran_out = 1 when its request newcap is at most g_most,
     g_peak raised to the bytes outside the buffer plus newcap: prhWriter_rpeak); prhWriter_putN consumes one
     outcome per grow (= per fuzz_realloc call; the plain WriterRet.v new_calls count). With every outcome true it is
     the plain putN.
   - Plain-only machinery dropped: call_pre_k / call_pre_t -> fpre; rf_ok / wr_room / wr_rooms -> the live room AT
     EACH EVENT of the call's own run, PRH_Base.prh_live_evs S (prhWriter_evs [] st P), for put / indent / put_string /
     write_value (the kit owner's entry-sum ruling, 2026-10-30; the note above prhWriter_out), and pj_write's entry
     budget blocks_bytes S + LIVE_pj_write .. <= LIVE_MAX (pj_write_c.v:58's peak); ro_agree -> arodata in
     fpre; guard_cells, off_errno, frm0 -> nothing; s_where's stack case -> dropped (src_rd puts a source below
     alloc_ceiling, and put_string's escape buffer is in its fake frame); the plain image cases -> kept_at's in_zs case.
   - room: room_live_cf (PRH_Base.v, owned by the allocator-model owner), room_cf at none; margins removed. All five texts allocate
     (put's fuzz_realloc; pj_write's fuzz_free): room_live_cf S on entry, room_live_cf S' in every post. None states
     the PRIMARY room_cf: no allocator call here is made at the entry state's allocator (put's fuzz_realloc follows
     its own checks; the callers' puts follow earlier ones), so each call's primary room comes from P8's preset_room
     through the driver's slot. Beside it the brief's live room and request bound (fuzz_realloc's own premises).
   - Allocator traces: prh_univ_closure (PRH_Base.v), dropped prh_malloc_univ, the realloc pair
     In [cf_pc_realloc_ra0] / In [cf_pc_realloc_ra0; pi_ret_realloc] (all five texts) and pj_write's literal free pair
     [pc_free_ra0] / [pc_free_ra0; pi_ret_sites F_pj_write RT_fuzz_free]; kept none. Every allocator call in this
     subtree has an EMPTY chain (fuzz_malloc / fuzz_realloc hold n in s0, pj_write holds pretty in s0; put_string, the
     one frame-pointer function here, makes no allocator call itself), so prh_univ_closure_lit covers each site.
   - Float state: kept by put / indent only. The only float write on musl's snprintf path is pop_arg's `fld fa0` (double
     arguments, A 0x960d8); put_string's %c and %04x conversions do not reach it (printf_core itself has no float
     instruction). The plain printf_post (printf_facts_c.v:118-130) allows fa0 and fcsr to change; it is wider than
     these paths.
   - pj_write's pretty is a C int that the callers pass as 0 or 1 (fuzz_preset.c :578-649). The text narrows the plain
     0 <= pretty < 2 ^ 64 to 0 <= pretty < 2 ^ 31: pj_write holds pretty in s0 at its fuzz_free call (A 0x866e4,
     0x86734), so the chain at that call is empty and the free's trace does not depend on pretty.
   NAMED GAPS (no text here; the walks need them):
   - SNPRINTF: put_string calls snprintf with TWO conversions: `\\%c` (.str.18, A 0x215c0, for the double quote (34)
     and the backslash (92), the byte in a3) and `\\u%04x` (.str.22, A 0x21640, for the other control bytes), into
     its 8-byte escape buffer, size 8. The fm port's snprintf statement (FMH_Rt.v:181-205 asnprintf_realizes) covers only
     literal, %s and %.*s pieces; the kit owner staffs the %c / %04x extension. The `\\n`, `\\t`, `\\r` escapes are
     __asan_memcpy of 3 bytes from .rodata (.str.19 / .str.20 / .str.21), not snprintf. musl's printf_core also reads
     the stack-protector cells.
   - THE WRITER'S READ-ONLY LITERALS: put's one-byte sources (the double quote, comma, the four brackets, newline),
     the two spaces, the separators `: ` and `:`, the words null / false / true (and `0` and the empty string for a
     NULL str, unreachable under pj_nodeR) and the 3-byte escape sources are
     .rodata globals at addresses the code forms with auipc; each must be src_rd and kept_at's in_zs case. No kit name
     gives these addresses (no numeral address in a text), so the walks need them as an image fact (FMH_Fn.v:45-60
     fm_img_facts form).
   - THE FAKE FRAME: put_string takes a frame_alloc_0 frame (A 0x87ea0) only when the runtime's use-after-return flag
     is nonzero: A 0x87e84 loads the GOT word at 0xa1b28 (listing v3 703cc4a8796d A_OBJ 1), and 0x87e8c `lw a2, 0(a2)`
     reads the 4-byte flag `__asan_option_detect_stack_use_after_return` at 0xaa8c0 (f0d2e8d4 .symtab,
     the ranout-image asan pin's nm listing the internal file fuzz_preset.nm.txt:443). It is NOT the shadow-base cell
     `__asan_shadow_memory_dynamic_address` (0xaa8b8, the internal file nm.txt:701, reached by the GOT word 0xa1ad0 at 0x87e88).
     Otherwise put_string carves the escape buffer from the real stack below sp. The texts state the fake-frame path
     (frames-count premise, YG0d.v:300 at cid 0); the walk takes the flag's value (1 on the rebuilt images, to be
     re-derived from the image) and `as_got_uar B = VAL (A_OBJ 1)`, a marked hypothesis until the core owner rules on
     pal_got_uar. The PALib witnesses of record are PALibA 88c72c8175cf (A', every field by vm_compute on AF0l
     dfca6bb1a8d7) and PALibB 5baa19c890f7 (B', pin-neutral, commit ed438196d17c): PAL,
     pal_pst_ok, pal_uar_img and pal_stack_malloc* are discharged by citing them (no kit text carries them).
   Statements only.
   THE MODEL-RUN POSITION (the kit owner's ruling, 2026-10-29): every text below that makes allocator calls in its
   subtree takes P8's premises at a position of the model run, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i
   rp_H0 rp_hist S (lib/Spec/PresetRoomPos.v, the one home; the driver-contract owner's PresetCfnA.v re-exports it), UNCONDITIONALLY
   at entry, and the run events its calls make as an ENTRY PREMISE (its own computed list); its post gives the
   position back at the EXACT advance, rp_i plus the number of events it made. The bare pair
   `exists rp_i' rp_hist', (rp_i <= rp_i')%nat /\ iface_room_pos .. rp_i' .. rp_hist' S'`, which this header once
   called load-bearing, is FALSE (PRH_Base.prh_run_at's note: three measurements) and unusable by a caller, which can
   never name the event at an existential rp_i'; no text of this file has it. The live-set bounds at each inner
   allocator call follow from the position by the driver-contract owner's counts_of_room_pos_rl / counts_of_room_pos_ok.
   (Binder names are rp_* because several texts already bind x and i.)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfTreeVis.
(* the re-hiding move's SRr' and wle' (YA0nH) and preset's zone (YGcfRehidePost.RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the writer's pure model with allocation outcomes ---- *)

(* the longest text the writer may build: plain put_c.v:17 WMAX *)
Definition prhWriter_WMAX : Z := 2 ^ 28.

(* the bytes one put needs: len + n + 1 (:458) *)
Definition prhWriter_need (st : WriterApp.wst) (b : list Z) : Z :=
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length b) + 1.

(* the put grows the buffer, so it calls fuzz_realloc (:456-465) *)
Definition prhWriter_grows (st : WriterApp.wst) (b : list Z) : bool :=
  (WriterApp.w_failed st =? 0) && (WriterApp.w_cap st <? prhWriter_need st b).

(* ---- THE WRITER'S RUN EVENT. put's grow is a fuzz_realloc of the buffer (:456-465): on the model's run it is
   HRe (cap + cf_head) (newcap + cf_head), and HMal (newcap + cf_head) when the buffer is empty (realloc (NULL, ..),
   PresetReqAt.v:54, :109). A text that makes the call states its event and its EXACT advance; the event is an ENTRY
   PREMISE and the advance unconditional, so a caller that calls put twice can compose (the kit owner's ruling,
   2026-10-29, on the image-B tx walk's counterexample for the tx family, which has the same shape here). ---- *)
Definition prhWriter_ev {cp : CfParams} (st : WriterApp.wst) (b : list Z) : PresetReqAt.hev :=
  if WriterApp.w_cap st =? 0
  then PresetReqAt.HMal (WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b) + cf_head)
  else PresetReqAt.HRe (WriterApp.w_cap st + cf_head)
         (WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b) + cf_head).

(* one put (:454-477) whose fuzz_realloc call (if it makes one) has outcome okb: the allocation set to fail fails
   whatever okb is (g_fail_at = SIZE_MAX, as plain put1); otherwise okb = false is a REFUSAL (failed, text and buffer
   kept, g_fail_at kept); okb = true grows to newcap. With okb = true it is plain WriterApp.put1. *)
Definition prhWriter_put1 (okb : bool) (st : WriterApp.wst) (b : list Z) : WriterApp.wst :=
  if prhWriter_grows st b then
    let c' := WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b) in
    let cnt' := (WriterApp.w_cnt st + 1) mod 2 ^ 64 in
    let calls' := WriterApp.w_calls st ++ [c'] in
    if WriterApp.w_cnt st =? WriterApp.w_fail st then
      WriterApp.mkW 1 (WriterApp.w_text st) (WriterApp.w_cap st) cnt' (2 ^ 64 - 1) calls'
    else if okb then
      WriterApp.mkW 0 (WriterApp.w_text st ++ b) c' cnt' (WriterApp.w_fail st) calls'
    else
      WriterApp.mkW 1 (WriterApp.w_text st) (WriterApp.w_cap st) cnt' (WriterApp.w_fail st) calls'
  else WriterApp.put1 st b.

(* a run of puts; the i-th fuzz_realloc call takes outcome nth i ok true (prh_oks's indexing) *)
Fixpoint prhWriter_putN (ok : list bool) (st : WriterApp.wst) (P : list (list Z)) : WriterApp.wst :=
  match P with
  | [] => st
  | b :: P' =>
      if prhWriter_grows st b then prhWriter_putN (tl ok) (prhWriter_put1 (hd true ok) st b) P'
      else prhWriter_putN ok (WriterApp.put1 st b) P'
  end.

(* the fuzz_realloc calls the run makes (each one harness allocation, g_count + 1) *)
Definition prhWriter_k (ok : list bool) (st : WriterApp.wst) (P : list (list Z)) : nat :=
  (length (WriterApp.w_calls (prhWriter_putN ok st P)) - length (WriterApp.w_calls st))%nat.

(* THE REQUESTS OF A RUN OF PUTS (prh_oks's ns): each fuzz_realloc call's user request, its newcap, in call order - the
   entries the run appends to w_calls (prhWriter_put1 appends c' on every arm of a grow, the chosen failure and a
   refusal included; WriterApp.put1 without a grow appends nothing), so its length is prhWriter_k ok st P *)
Definition prhWriter_reqs (ok : list bool) (st : WriterApp.wst) (P : list (list Z)) : list Z :=
  skipn (length (WriterApp.w_calls st)) (WriterApp.w_calls (prhWriter_putN ok st P)).

(* THE REFUSAL PEAK OF A RUN OF PUTS (PRH_Base.prh_refused_peak; #102's rule, the kit owner's ruling 2026-10-29). A
   refused grow of the buffer from cap_i to c (fuzz_realloc (buf, c): refused () runs after disown; realloc (NULL, c)
   when cap_i = 0) raises g_peak to the bytes outside the buffer plus c. Every grow before it was granted and replaced
   the buffer, and a run of puts allocates nothing else, so the bytes outside the buffer stay Ledger.lsum Lam -
   w_cap st, Lam and st the run's entry ledger and writer (the buffer (buf, w_cap st) is in Lam when w_cap st <> 0,
   prhWriter_out): the i-th call's hs is Ledger.lsum Lam - w_cap st + c_i. *)
Definition prhWriter_rpeak (ok : list bool) (Lam : list (Z * Z)) (st : WriterApp.wst) (P : list (list Z)) : Z :=
  prh_refused_peak ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P)
    (map (fun c => Ledger.lsum Lam - WriterApp.w_cap st + c) (prhWriter_reqs ok st P)).

(* the most fuzz_realloc calls the run can make: the run with every outcome accepting (the plain model's calls,
   WriterApp.putN). A refused grow sets failed and the run makes no further call, so any outcome list ok makes at most
   this many: prhWriter_k ok st P <= prhWriter_ngrow st P. No writer text charges it any more (room is an invariant);
   PRH_FnCheck.v's ck_rk_write still cites it. *)
Definition prhWriter_ngrow (st : WriterApp.wst) (P : list (list Z)) : nat := prhWriter_k [] st P.

(* ---- THE RUN EVENTS A RUN OF PUTS MAKES (the position sweep, the kit owner's ruling 2026-10-29). Under the outcomes
   ok of its fuzz_realloc calls (prhWriter_putN's indexing) a run of puts P from st makes one event per GRANTED grow,
   prhWriter_ev; the allocation set to fail (w_cnt = w_fail) and a refused grow make NONE (the model's
   PresetReqAt.rd_hev (EFail _) = [], w_starved), and after either the writer is failed, so every later put calls
   nothing. ok = [] is the all-granted run: a text's ENTRY PREMISE is that the run's next events are
   prhWriter_evs [] st P (the chosen failure is still taken there, since it is w_cnt = w_fail, not an outcome), and its
   post's EXACT ADVANCE is rp_i + length (prhWriter_evs ok st P) for the outcomes ok its post states. ---- *)
Fixpoint prhWriter_evs {cp : CfParams} (ok : list bool) (st : WriterApp.wst) (P : list (list Z))
  : list PresetReqAt.hev :=
  match P with
  | [] => []
  | b :: P' =>
      if prhWriter_grows st b then
        (if (WriterApp.w_cnt st =? WriterApp.w_fail st) || negb (hd true ok) then [] else [prhWriter_ev st b]) ++
        prhWriter_evs (tl ok) (prhWriter_put1 (hd true ok) st b) P'
      else prhWriter_evs ok (WriterApp.put1 st b) P'
  end.

(* pj_write's events: its puts' from the empty writer, then, if the writer failed with a buffer, its fuzz_free (buf)
   (:567-570). The model's w_evs / w_starved (PresetReqAt.v:115-121) are the case ok = []. *)
Definition prhWriter_pjw_evs {cp : CfParams} (ok : list bool) (cnt fail : Z) (P : list (list Z))
  : list PresetReqAt.hev :=
  let st' := prhWriter_putN ok (WriterApp.w0 cnt fail) P in
  prhWriter_evs ok (WriterApp.w0 cnt fail) P ++
  (if (WriterApp.w_failed st' =? 0) || (WriterApp.w_cap st' =? 0) then []
   else [PresetReqAt.HFr (WriterApp.w_cap st' + cf_head)]).

(* a failed writer makes no event *)
Lemma prhWriter_evs_failed {cp : CfParams} : forall P ok st,
  WriterApp.w_failed st <> 0 -> prhWriter_evs ok st P = [].
Proof.
  induction P as [|b P IH]; intros ok st H; [reflexivity|]. cbn [prhWriter_evs].
  assert (G : prhWriter_grows st b = false).
  { unfold prhWriter_grows. apply andb_false_intro1. apply Z.eqb_neq. exact H. }
  rewrite G. apply IH. unfold WriterApp.put1. rewrite (proj2 (Z.eqb_neq _ _) H). exact H.
Qed.

(* THE SUPPLY OF A CALLEE'S PREMISE from its caller's: the all-granted events of P1 ++ P2 split at the state the
   all-granted run of P1 leaves (then PRH_Base.prh_run_at_app_iff splits the position) *)
Lemma prhWriter_evs_app0 {cp : CfParams} : forall P1 P2 st,
  prhWriter_evs [] st (P1 ++ P2) = prhWriter_evs [] st P1 ++ prhWriter_evs [] (prhWriter_putN [] st P1) P2.
Proof.
  induction P1 as [|b P1 IH]; intros P2 st; cbn [app prhWriter_evs prhWriter_putN]; [reflexivity|].
  destruct (prhWriter_grows st b); cbn [hd tl]; rewrite IH; [rewrite app_assoc|]; reflexivity.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- THE LIVE ROOM AT EACH EVENT (the kit owner's entry-sum ruling, 2026-10-30 00:36Z by its `date -u`; the sources
   are at PRH_Base.prh_live_evs). put / indent / put_string / write_value take PRH_Base.prh_live_evs S E over their own
   all-granted events E = prhWriter_evs [] st P, the list their run premise already names: at EACH grow event of the
   run, the live bytes THERE (the entry's, moved by the earlier grows: each frees the buffer it replaces and adds its
   successor) plus that grow's SINGLE request newcap + cf_head are at most LIVE_MAX - fuzz_realloc's premise at that
   call (PRH_FnAlloc.v:647, at cnt <> fail). It REPLACES the entry sum `blocks_bytes S + LIVE_<fn> .. <= LIVE_MAX`
   (LIVE_<fn> was prhWriter_live st P := 2 * (newcap (w_cap st) (len text + len (concat P) + 1) + cf_head) minus the
   entry buffer), which ADDED THE ENTRY LIVE BYTES TO THE CALLEE'S OWN MAXIMUM, although the writer frees and reuses
   (each realloc frees the buffer it replaces) and at each allocation event the run is POSITIONED. A REPAIR, NOT A
   RELAXATION: NO PROOF USES THE SUM FORM TODAY (the S1 owner: no consumer), and it is NOT DISCHARGEABLE: w_cap is
   bounded only by 2 ^ 64 (prhWriter_out), and a put that does not grow asked blocks_bytes S + w_cap + cf_head.
   Wherever the sum held it implies this form (the old note's composition by arithmetic), so no caller loses. THE
   DISCHARGER IS PROVED: the live-bytes owner's entry_sum_ok / entry_sum_closed (M1 + M2 + M6), lib/Spec/PresetLiveBytes.v
   :1751, :1827; a caller discharges event j at the positioned event rp_i + j. THE CHOSEN FAILURE (w_cnt = w_fail) makes
   no event, and the leaf asks nothing there: fuzz_malloc / fuzz_realloc guard their live premise by cnt <> fail
   (PRH_FnAlloc.v:303 / :647, the peak-bytes-102 rule; the live-event walk's measurement that the unguarded leaf left a put walk
   stuck on that arm once this premise moved to the per-event form). ---- *)
(* pj_write KEEPS ITS ENTRY BUDGET (measured 2026-10-30; not the same case): its run starts with no buffer, so the
   budget is 2 * (C + cf_head) with C = newcap 0 (len (wdoc t p) + 1) <= 2 ^ 28 by the text's own WMAX premise - a
   bound, where the four callees' sums were unbounded in w_cap; its callers round_trip_text and
   check_reject_clean_starved carry it from their own budgets, which close at the harness entry (the DRV route,
   the kit owner's ruling 2026-10-30). *)
Definition LIVE_pj_write (t : PjTree.jv) (p : bool) : Z :=
  2 * (WriterSpec.newcap 0 (Z.of_nat (length (WriterValue.wdoc t p)) + 1) + cf_head).

(* ---- the writer state at o (struct pj_out, :447-452; plain put_c.v:52-63 pj_out_ok): buf, len, cap (size_t) and
   failed (int); the text is the first len bytes of the buffer, NUL-terminated, and every one of its cap user bytes is
   readable (fuzz_realloc's premise reads all k old bytes; its success arm gives the copied prefix plus `rest`); cap is
   0 (no buffer yet) or 4096 * 2 ^ j, and the buffer is a live harness block (buf, cap). While the writer has not
   failed, its buffer's user bytes are addressable (put's __asan_memcpy and NUL store write them; fuzz_realloc's
   success arm gives it). ---- *)
Definition prhWriter_out (W : world segs) (mem : word -> option byte) (Lam : list (Z * Z)) (o buf : Z)
  (st : WriterApp.wst) : Prop :=
  o mod 8 = 0 /\ 0 <= buf < 2 ^ 64 /\ 0 <= WriterApp.w_cap st < 2 ^ 64 /\
  val_mem segs (rdW W mem) o 8 buf /\
  val_mem segs (rdW W mem) (o + 8) 8 (Z.of_nat (length (WriterApp.w_text st))) /\
  val_mem segs (rdW W mem) (o + 16) 8 (WriterApp.w_cap st) /\
  val_mem segs (rdW W mem) (o + 24) 4 (WriterApp.w_failed st) /\
  (WriterApp.w_failed st = 0 \/ WriterApp.w_failed st = 1) /\
  WriterSpec.bytes_ok (WriterApp.w_text st) /\
  ((WriterApp.w_cap st = 0 /\ buf = 0 /\ WriterApp.w_text st = []) \/
   ((exists j, 0 <= j <= 51 /\ WriterApp.w_cap st = 4096 * 2 ^ j) /\ In (buf, WriterApp.w_cap st) Lam /\
    Z.of_nat (length (WriterApp.w_text st)) < WriterApp.w_cap st /\
    (exists rest, Z.of_nat (length (WriterApp.w_text st ++ 0 :: rest)) = WriterApp.w_cap st /\
       bytes_at W mem buf (WriterApp.w_text st ++ 0 :: rest)) /\
    (WriterApp.w_failed st = 0 ->
       range_addressable (aview segs (w_H W) mem) SHADOW_OFF buf (WriterApp.w_cap st) /\
       shadow_hull_vis (aview segs (w_H W) mem) buf (WriterApp.w_cap st)))).

(* the journal footprint: the buffer block, which a put writes (text, NUL) and fuzz_realloc may free *)
Definition prhWriter_fp (buf cap : Z) : list (Z * Z) :=
  if cap =? 0 then [] else ablocks_fp [(buf - cf_head, cap + cf_head)].

(* where a byte window the writer reads after an intervening call lives, with its shadow facts (PRH_Base.v kept_at),
   or in a live fake frame (put_string's escape buffer: ajournal_x keeps a frame's bytes and its shadow), and not in
   the buffer, which fuzz_realloc may free (plain put_c.v:65-68 s_where, x <> buf) *)
Definition prhWriter_src_home (ly : alayout) (S : astate) (Lam : list (Z * Z)) (buf cap s n : Z) : Prop :=
  (kept_at B Lam s n \/
   exists cid pos, In (cid, pos) (frames S) /\
     frame_addr ly cid pos <= s /\ s + n <= frame_addr ly cid pos + fs_frame_bytes cid) /\
  (cap = 0 \/ s + n <= buf \/ buf + cap <= s).

(* the footprint of a function that writes the struct in its caller's frame (PRH_Base.v fpostW): the struct's 32
   bytes, so every other byte of the caller window [spZ regs, spZ regs + d) is kept, and the buffer block *)
Definition prhWriter_cfp (o buf cap : Z) : list (Z * Z) := (o, o + 32) :: prhWriter_fp buf cap.

(* the tree root in a live fake frame of the entry (LLVMFuzzerTestOneInput's doc is in its class-1 frame, which
   round_trip_text / check_round_trip pass on; PRH_FnCheck.v ck_in_frame): the journal keeps an entry frame's bytes *)
Definition prhWriter_in_frame (ly : alayout) (S : astate) (v : Z) : Prop :=
  exists cid pos, In (cid, pos) (frames S) /\
    frame_addr ly cid pos <= v /\ v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid.

(* the tree's blocks are C data the runtime calls may read: each (a, k) of D is in the low or high application range
   with its granule slack, its k bytes addressable with a visible shadow hull, and the bytes up to the END OF ITS
   LAST GRANULE visible. This is what put_string's cstr_ok (keys, strings), write_value's strlen + put of a number's
   text (cstr_ok, src_rd) and write_value's own shadow-checked loads of kids[i] / keys[i] ask of a tree block.
   NARROWED to the allocator-model owner's body (the kit owner's approval): YGcfTreeVis.tree_vis_cf (lib/Reusable/YGcfTreeVis.v:42,
   the internal file HSMAP-DESIGN.md 4(b):650-656 word for word), which a8's tree_vis_of_blocks_cf (:57) PROVES from ARcf alone for a
   D whose blocks are harness blocks with hidden heads. So this premise is no longer the caller's to state by hand,
   and a lane's rt_slack_vis_law retires. The narrowing also REPAIRS a defect of the old body: it asked
   `a + k + 8 <= alloc_ceiling` and visibility to a + k + 8, which is FALSE for a block whose last granule ends at
   the ceiling; the granule form `(a + k + 7) / 8 * 8` is what the engine's rules actually ask (cstr_ok's last
   conjunct is the same round-up). Since 2026-10-29 src_rd's ceiling is `p + len` and cstr_ok's `p + len + 1`
   (the kit owner's rule), so this granule bound gives both directly, with no F21b hypothesis. *)
Definition prhWriter_tree_vis (W : world segs) (mem : word -> option byte) (D : list (Z * Z)) : Prop :=
  YGcfTreeVis.tree_vis_cf segs W mem D.

(* what a run of puts P leaves (plain WriterRet.v:264-294 wr_rel / wr_ret): for some outcomes ok of its fuzz_realloc
   calls (prh_oks over the run's requests prhWriter_reqs: the one set to fail fails, a refusal sets g_ran_out when its
   request is at most g_most), the writer state at o is the model's, the ledger counts the calls; either the capacity
   is unchanged with no refusal (same buffer, Lam, peak, blocks), or unchanged by a REFUSED grow (same buffer, Lam,
   blocks; g_peak raised by the refusal), or the buffer grew: the old buffer (if any) is gone from Lam and the blocks,
   the new one is the head of Lam, and g_peak is the max of the last granted grow (the earlier, smaller buffers of the
   run are each freed by the next realloc) and of a refused grow after it. prhWriter_ret_ok_peak_le (below) gives
   peak <= peak' for a consumer that needs only that. *)
Definition prhWriter_ret_ok (ok : list bool) (ly : alayout) (S : astate) (Lam : list (Z * Z)) (peak ran most own o buf : Z)
  (st : WriterApp.wst) (P : list (list Z))
  (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte)
  (md' : Model) : Prop :=
  exists ran' buf' Lam' peak',
    let st' := prhWriter_putN ok st P in
    prh_oks ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) (prhWriter_reqs ok st P) most ran ran' /\
    prhWriter_out W' mem' Lam' o buf' st' /\
    prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt st') (WriterApp.w_fail st') ran' most own /\
    ((WriterApp.w_cap st' = WriterApp.w_cap st /\ buf' = buf /\ Lam' = Lam /\ peak' = peak /\
      Permutation (ablocks B ly' S') (ablocks B ly S))
     \/
     (* THE CAPACITY KEPT BY A REFUSED GROW ((B), the kit owner's ruling 2026-10-29): the refused fuzz_realloc raises
        g_peak (PRH_FnAlloc.v tfuzz_realloc_specX's refused arm, live - k + n since realloc disowns first) while the
        capacity, the buffer and Lam stay. COUNTEREXAMPLE to the arm above alone: Lam = [(buf, 4096)], peak = live =
        4096, cap = 4096, len + n + 1 = 4097, so newcap 8192, the realloc refused: g_peak = 4096 - 4096 + 8192 = 8192,
        not 4096. *)
     (WriterApp.w_cap st' = WriterApp.w_cap st /\ buf' = buf /\ Lam' = Lam /\
      (exists i, (i < prhWriter_k ok st P)%nat /\ prh_refused ok (WriterApp.w_cnt st) (WriterApp.w_fail st) i = true) /\
      peak' = Z.max peak (prhWriter_rpeak ok Lam st P) /\
      Permutation (ablocks B ly' S') (ablocks B ly S))
     \/
     (WriterApp.w_cap st < WriterApp.w_cap st' /\
      exists l1 l2 b1 b2,
        ((WriterApp.w_cap st = 0 /\ l1 = [] /\ l2 = Lam /\ b1 = [] /\ b2 = ablocks B ly S) \/
         (WriterApp.w_cap st <> 0 /\ Lam = l1 ++ (buf, WriterApp.w_cap st) :: l2 /\
          ablocks B ly S = b1 ++ (buf - cf_head, WriterApp.w_cap st + cf_head) :: b2)) /\
        Lam' = (buf', WriterApp.w_cap st') :: l1 ++ l2 /\
        (* a grow of the same run REFUSED after the last granted one adds the refusal term. COUNTEREXAMPLE to the
           form without it: cap = 0, P = [10 bytes; 5000 bytes], ok = [true; false], cnt <> fail: the first grow to
           4096 granted, the second to 8192 refused after disown: g_peak = Ledger.lsum Lam + 8192, where
           Z.max peak (Ledger.lsum Lam + 4096) was stated. *)
        peak' = Z.max (Z.max peak (Ledger.lsum (l1 ++ l2) + WriterApp.w_cap st')) (prhWriter_rpeak ok Lam st P) /\
        Permutation (ablocks B ly' S') ((buf' - cf_head, WriterApp.w_cap st' + cf_head) :: b1 ++ b2))).
(* the same, its outcomes ok named: ok is shared with the position conjunct of the texts that state their exact
   advance (rp_i + length (prhWriter_evs ok st P)); prhWriter_ret is prhWriter_ret_ok under `exists ok`, the same term
   as before the split *)
Definition prhWriter_ret (ly : alayout) (S : astate) (Lam : list (Z * Z)) (peak ran most own o buf : Z) (st : WriterApp.wst)
  (P : list (list Z))
  (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte)
  (md' : Model) : Prop :=
  exists ok, prhWriter_ret_ok ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md'.

(* THE PEAK IS MONOTONE across a run of puts, whichever arm: the corollary for a consumer that needs only
   peak <= peak' (the ledger, the outcomes and the writer state kept as prhWriter_ret_ok states them) *)
Lemma prhWriter_ret_ok_peak_le : forall ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md',
  prhWriter_ret_ok ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' ->
  exists ran' buf' Lam' peak',
    prh_oks ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) (prhWriter_reqs ok st P) most ran ran' /\
    prhWriter_out W' mem' Lam' o buf' (prhWriter_putN ok st P) /\
    prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt (prhWriter_putN ok st P))
      (WriterApp.w_fail (prhWriter_putN ok st P)) ran' most own /\
    peak <= peak'.
Proof.
  intros ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' H.
  unfold prhWriter_ret_ok in H. cbv zeta in H.
  destruct H as (ran' & buf' & Lam' & peak' & K & OUT & LG & ARMS).
  exists ran', buf', Lam', peak'. split; [exact K|]. split; [exact OUT|]. split; [exact LG|].
  destruct ARMS as [(_ & _ & _ & E & _) | [(_ & _ & _ & _ & E & _) | (_ & l1 & l2 & b1 & b2 & _ & _ & E & _)]];
    subst peak'; lia.
Qed.

(* ---- THE FLOAT STATE (the kit owner's ruling 14:49Z): put_string's __wrap_snprintf (A 0x8805c) returns at SOME fx'
   (YGcallSnp.asnprintf_realizes_xrom), so a post that keeps fx (fpostWm / fpostm) is unreachable after a snprintf arm
   and no consumer of this unit reads the float state. put_string, write_value (through put_string) and pj_write
   (through write_value) post in the FLOAT form, fpostWFmR / fpostFm; put and indent reach no snprintf and keep
   fpostWmR (R forms at wle' segs RZ_cf). (The lanes' SNPK premise is thereby deleted, not re-proved.) ---- *)

(* ---- the five texts ---- *)

(* put (:454-477; plain put_c.v:118-132). failed: return. len + n + 1 <= cap: __asan_memcpy (buf + len, s, n),
   len += n, buf[len] = 0. Otherwise cap' = newcap (doubling from 4096, :460-464), fuzz_realloc (buf, cap') (A 0x86c30):
   NULL (the allocation set to fail, or a refusal) sets failed = 1 (:466-470); else buf = the new block, cap = cap',
   then the copy. The source is read by __asan_memcpy AFTER fuzz_realloc, so it is src_rd and lives where the call
   keeps it with its shadow (prhWriter_src_home). The request cap' + HEAD is at most WMAX + HEAD (plain
   newcap_wmax, from len + n + 1 <= WMAX). Write set: the struct (caller's frame, the window), the buffer block (FP),
   the statics (PST), errno on a refusal, the frame. *)
Definition tput_specX (CTX0 : list (list Z)) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk) most own,
  forall ly S Hp W regs mem md ch o s n d buf (st : WriterApp.wst) (bs : list Z) Lam peak ran,
  fpre B ARx STK_put ly S Hp W regs mem md ch -> room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* THE RUN HAS AT MOST 4 CALLS: A17's prefix bound needs it where this text pays fuzz_realloc's
     hull budget from its position (lib/A/PresetHullPay.v hull_budget_of_room_pos) *)
  (length rp_os <= 4)%nat ->
  (* THE CALL'S ALLOCATIONS ARE CONSUMER ALLOCATIONS OF THE RUN (the ENTRY-KEYED texts' named entry premise,
     the kit owner's ruling 2026-10-29, extended to the writer's callees with pj_write's DEAD-PJWRITE), over
     this call's own all-granted events (one when it grows and is not the allocation set to fail, else none). The
     grow's fuzz_realloc is then a consumer event, where a REAL refusal is excluded (fuzz_realloc's outcome clause,
     PRH_FnAlloc), so the post states DEAD-PUT. Supplied by the caller from its own window
     (PRH_Base.prh_cons_from_sub). *)
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [bs])) ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 s -> getr regs 12 = w64 n ->
  (* THE CHAIN FROM o, in the slice walker's MEASURED form (the S7a walk / the S7b walk; the kit owner's ruling, which WITHDREW the
     entry-view `spZ regs + 16 <= o` bound): this function holds the out struct o in s0 across its
     `jal fuzz_realloc`, so the callee's afn_pre_x needs a chain from o. put's stores before that call are
     FOURTEEN and ALL BELOW sp (sd ra -> sp-8, sd s0 -> sp-16, s1..s11 -> sp-24..sp-104, sd a0,0(sp) -> sp-112),
     nothing at or above sp, and s0 := o at A 0x86ba0 is unchanged to the call. So the cut on o against spZ regs
     covers every caller: CASE 1 (o >= sp + 16) is the only one that needs a caller chain, because all its reads
     are at or above o >= sp + 16 where put writes nothing, so the caller's entry-view chain carries over
     verbatim; CASE 2 (o = sp + 8, pj_write's own call, A 0x866d4 / 0x86718 / 0x86724) has word (o - 16) = put's
     own saved ra, a text address below alloc_ceiling, so bad_next fires and the walk builds the one-record
     chain with NO caller premise; CASE 3 (o = sp) likewise. NO relation on s0Z is needed, and pj_write - whose
     o is its own frame at sp + 8 - threads nothing up to its callers. *)
  (* TWO CASES (the kit owner's ruling on the slice walker's corrected measurement on d83eb25d): case 1, o at least 16 above
     the entry sp, takes the caller's entry-view chain from o; case 2, o = spZ regs + 8, which pj_write's call of
     write_value makes (A 0x8670c `jal write_value`, a0 = sp_pj + 8) and the top-level write_value's TAIL call of
     put_string makes (A 0x868a8 `j put_string`, after write_value restores sp) - there [o - 16] is this function's
     OWN saved ra, closed in its own walk by fpre's `raZ regs < YM05.alloc_ceiling`. *)
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (* THE FIRST RECORD FROM o, AS TWO WORDS (the kit owner's form (a), ruled 11:29Z; restated 2026-10-29 after two
     refuted spellings). The words at o - 8 (the saved ra) and o - 16 (the next fp) are caller-window words that
     NO put writes, and nfp < alloc_ceiling <= o makes bad_next fire, so the unwinder reads exactly this one
     record however often a loop rewrites the out struct [o, o + 32). REFUTED, so not to be proposed again:
     (1) an any-length chain `exists ch0, achain .. o ch0`: not transferable across a put that rewrites
     [o, o + 32), where a longer chain's later records can lie; (2) a one-record `exists r, achain .. o [r]`:
     it does NOT force bad_next, because fpchain's tail for a stopped chain is a READ at nfp - 8 (YG00.v:368-373)
     - the slice walker's witness at indent's loop call (A 0x881f0): word[o - 16] = o + 8 and word[o] = 0 at entry
     make `achain .. o [(o, ra, o + 8)]` hold, and after the first put grows the buffer word[o] >= 4096 and no
     one-record chain from o exists. The ra bound that closes CASE 2 is fpre's `raZ regs < YM05.alloc_ceiling`;
     its one-copy discharge is PRW_StepKit.pa_slot_lt_ceil (commit c3a0b928f54,
     lib/A/Prog/PRW_StepKit.v:235). *)
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview segs (w_H W) mem) (o - 8) = Some ra /\
       exists nfp, rdword (aview segs (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  src_rd W mem s bs -> Z.of_nat (length bs) = n ->
  prhWriter_src_home ly S Lam buf (WriterApp.w_cap st) s n ->
  (* ITS RUN EVENT, as an entry premise (see prhWriter_ev), supplied by the caller's own event list: the grow's
     fuzz_realloc event, unless this call is the allocation set to fail (w_cnt = w_fail), which makes NO event on
     the model's run (PresetReqAt.rd_hev (EFail _) = [], w_starved) *)
  (prhWriter_grows st bs = true -> WriterApp.w_cnt st <> WriterApp.w_fail st ->
     nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i = Some (prhWriter_ev st bs)) ->
  Z.of_nat (length (WriterApp.w_text st)) + n + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  (* THE LIVE ROOM AT EACH EVENT (PRH_Base.prh_live_evs; the note above prhWriter_out): was the entry sum
     `blocks_bytes S + LIVE_put st bs <= LIVE_MAX`, entry bytes plus the callee's maximum - no proof used it and it was
     not dischargeable; discharger the live-bytes owner's entry_sum_ok, proved (lib/Spec/PresetLiveBytes.v:1751) *)
  prh_live_evs S (prhWriter_evs [] st [bs]) ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.16): fpostWm is SHARED, so the post is its R
     form at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_put) regs mem md)
    (fpostWmR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) STK_put d (prhWriter_cfp o buf (WriterApp.w_cap st))
       regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\
       (* THE EXACT ADVANCE, keyed on the outcome the out struct records (failed, at o + 24): no grow, no event, the
          position unchanged; a grow that succeeds (failed' = 0) advances it by ONE; a grow whose fuzz_realloc returns
          NULL (the allocation set to fail, or a refusal; failed' = 1) makes no event and keeps it (the fuzz_realloc
          text's res = 0 arm). The bare pair this replaces was false (three measurements) and unusable (the position
          travels existentially, so a caller could never name the event at rp_i'). *)
       (prhWriter_grows st bs = false ->
          PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S') /\
       (prhWriter_grows st bs = true -> forall f', val_mem segs (rdW W' mem') (o + 24) 4 f' ->
          (f' = 0 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S') /\
          (* f' = 1, NOT f' <> 0: val_mem fixes only f' mod 2 ^ 32, so f' = 2 ^ 32 matches a stored failed = 0 (the
             grow GRANTED, the event's block live) and `f' <> 0` then asked the position at rp_i - FALSE (the slice walker's
             S7a walk: cap = 0, bs nonempty, w_cnt <> w_fail, event HMal (4096 + cf_head) at rp_i). prhWriter_out's
             failed is 0 or 1, so a caller loses nothing.
             THE HISTORY IS EXISTENTIAL (the kit owner's ruling, 2026-10-29, on the slice walker's measured mismatch): the
             arm's only allocator call is the chosen failure, and tfuzz_realloc_specX's arm for it gives
             `exists hist', iface_room_pos .. rp_i rp_H0 hist' S'`, not the entry's rp_hist, so the old `rp_hist S'`
             asked more than the callee states. The position (rp_i) is kept; only the history is the callee's. *)
          (f' = 1 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist' S')) /\
          (* DEAD-PUT (the refusal arm DEAD under prh_cons_from, above; three supports: PRH_Base's ENTRY-KEYED
             note): the outcome ok its post binds has no
             REFUSED grow; prh_granted admits the chosen failure (w_cnt = w_fail), which is NOT a refusal and which
             prh_cons_from does not exclude, so it claims no more and the f' = 1 arm stays (the chosen failure) *)
          exists ok, prhWriter_ret_ok ok ly S Lam peak ran most own o buf st [bs] ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st [bs]))).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tput_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. tputP_Q IS the text's post (tputP_Q_check fails to build if
   the two ever differ); tputP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition tputP_Q (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list chunk) (most own : Z) (ly : alayout) (S : astate) (o buf : Z) (st :
    WriterApp.wst) (bs : list Z) (Lam : list (Z * Z)) (peak ran : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  room_live_cf S' /\ (prhWriter_grows st bs = false -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist
      S') /\ (prhWriter_grows st bs = true -> forall f', val_mem segs (rdW W' mem') (o + 24) 4 f' -> (f' = 0 -> exists
      hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S') /\ (f' = 1 -> exists
      hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist' S')) /\ exists ok, prhWriter_ret_ok ok ly S
      Lam peak ran most own o buf st [bs] ly' S' Hp' W' regs' mem' md' /\ prh_granted ok (WriterApp.w_cnt st)
      (WriterApp.w_fail st) (prhWriter_k ok st [bs]).

Lemma tputP_Q_check : forall (CTX0 : list (list Z)), tput_specX CTX0 -> tput_specX CTX0.
Proof.
  intros CTX0 H. unfold tput_specX in *.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch o s n d buf st bs Lam peak ran HP0 HP1
      HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (tputP_Q rp_sm rp_x rp_os rp_i
      rp_H0 rp_hist most own ly S o buf st bs Lam peak ran) end.
  exact (H rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch o s n d buf st bs Lam peak ran HP0 HP1
      HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22).
Qed.

Record tputP_R (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i :
    nat) (rp_H0 : list Z) (rp_hist : list chunk) (most own : Z) (ly : alayout) (S : astate) (o buf : Z) (st :
    WriterApp.wst) (bs : list Z) (Lam : list (Z * Z)) (peak ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' :
    world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (ok : list bool) : Prop := {
  tputP_room : room_live_cf S';
  tputP_pos_keep : (prhWriter_grows st bs = false -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist
      S');
  tputP_pos_grow : (prhWriter_grows st bs = true -> forall f', val_mem segs (rdW W' mem') (o + 24) 4 f' -> (f' = 0 ->
      exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S') /\ (f' = 1 ->
      exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist' S'));
  tputP_ret_ok : prhWriter_ret_ok ok ly S Lam peak ran most own o buf st [bs] ly' S' Hp' W' regs' mem' md';
  tputP_granted : prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st [bs]) }.

Lemma tputP_R_of : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (rp_hist : list chunk) (most own : Z) (ly : alayout) (S : astate) (o buf : Z)
    (st : WriterApp.wst) (bs : list Z) (Lam : list (Z * Z)) (peak ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z)
    (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  tputP_Q rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' ->
  exists ok, tputP_R rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs'
      mem' md' ok.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' H.
      destruct H as (H0 & H1 & H2 & ok & H3 & H4).
  exists ok.
  exact {| tputP_room := H0; tputP_pos_keep := H1; tputP_pos_grow := H2; tputP_ret_ok := H3; tputP_granted := H4 |}.
Qed.

Lemma tputP_Q_of_R : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (rp_hist : list chunk) (most own : Z) (ly : alayout) (S : astate) (o buf : Z)
    (st : WriterApp.wst) (bs : list Z) (Lam : list (Z * Z)) (peak ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z)
    (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (ok : list bool),
  tputP_R rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' ok ->
  tputP_Q rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md'.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' ok HR.
  refine (conj (tputP_room HR) (conj (tputP_pos_keep HR) (conj (tputP_pos_grow HR) _))).
  exists ok.
  exact (conj (tputP_ret_ok HR) (tputP_granted HR)).
Qed.

(* the CONSEQUENTS of tputP_R's guarded conjuncts, NAMED: each conjunct of an implication's conclusion, read from
   the record through one lemma (a consumer that applies the guard and destructs its conclusion is not broken by the
   next conjunct appended there) *)

Lemma tputP_pos_grow_ok : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat *
    option nat)) (rp_i : nat) (rp_H0 : list Z) (rp_hist : list chunk) (most own : Z) (ly : alayout) (S : astate) (o buf
    : Z) (st : WriterApp.wst) (bs : list Z) (Lam : list (Z * Z)) (peak ran : Z) (ly' : alayout) (S' : astate) (Hp' :
    list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (ok : list bool),
  tputP_R rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' ok ->
  prhWriter_grows st bs = true -> forall f', val_mem segs (rdW W' mem') (o + 24) 4 f' ->
  (f' = 0 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S').
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' ok HR
      HP0 f' HP1.
  pose proof (tputP_pos_grow HR) as G.
  exact (proj1 (G HP0 f' HP1)).
Qed.

Lemma tputP_pos_grow_failed : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat *
    option nat)) (rp_i : nat) (rp_H0 : list Z) (rp_hist : list chunk) (most own : Z) (ly : alayout) (S : astate) (o buf
    : Z) (st : WriterApp.wst) (bs : list Z) (Lam : list (Z * Z)) (peak ran : Z) (ly' : alayout) (S' : astate) (Hp' :
    list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (ok : list bool),
  tputP_R rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' ok ->
  prhWriter_grows st bs = true -> forall f', val_mem segs (rdW W' mem') (o + 24) 4 f' ->
  (f' = 1 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist' S').
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' ok HR
      HP0 f' HP1.
  pose proof (tputP_pos_grow HR) as G.
  exact (proj2 (G HP0 f' HP1)).
Qed.

Local Unset Implicit Arguments.

(* indent (:514-523; plain indent_c.v:25-38): pretty = 0: nothing; else put a newline, then depth times put two
   spaces (the pieces WriterValue.wind; depth is a C int, sign-extended in a2: a negative depth puts no spaces). The
   literals are image bytes (named gap). *)
Definition tindent_specX (CTX0 : list (list Z)) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk) most own,
  forall ly S Hp W regs mem md ch o pretty depth d buf (st : WriterApp.wst) Lam peak ran,
  fpre B ARx STK_indent ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* THE RUN HAS AT MOST 4 CALLS: its put calls take it (tput_specX) *)
  (length rp_os <= 4)%nat ->
  (* THE CALL'S ALLOCATIONS ARE CONSUMER ALLOCATIONS OF THE RUN (the ENTRY-KEYED texts' named entry premise,
     the kit owner's ruling 2026-10-29, extended to the writer's callees with pj_write's DEAD-PJWRITE), over
     this call's own all-granted events; its puts' grows are then consumer events, so the post states
     DEAD-INDENT. Supplied by the caller from its own window (PRH_Base.prh_cons_from_sub). *)
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhWriter_evs [] st (WriterValue.wind (negb (pretty =? 0)) depth))) ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 pretty -> getr regs 12 = w64 depth ->
  0 <= pretty < 2 ^ 64 -> - 2 ^ 31 <= depth < 2 ^ 31 ->
  (* THE CHAIN FROM o, in the slice walker's MEASURED form (the S7a walk / the S7b walk; the kit owner's ruling, which WITHDREW the
     entry-view `spZ regs + 16 <= o` bound): this function holds the out struct o in s0 across its
     `jal fuzz_realloc`, so the callee's afn_pre_x needs a chain from o. put's stores before that call are
     FOURTEEN and ALL BELOW sp (sd ra -> sp-8, sd s0 -> sp-16, s1..s11 -> sp-24..sp-104, sd a0,0(sp) -> sp-112),
     nothing at or above sp, and s0 := o at A 0x86ba0 is unchanged to the call. So the cut on o against spZ regs
     covers every caller: CASE 1 (o >= sp + 16) is the only one that needs a caller chain, because all its reads
     are at or above o >= sp + 16 where put writes nothing, so the caller's entry-view chain carries over
     verbatim; CASE 2 (o = sp + 8, pj_write's own call, A 0x866d4 / 0x86718 / 0x86724) has word (o - 16) = put's
     own saved ra, a text address below alloc_ceiling, so bad_next fires and the walk builds the one-record
     chain with NO caller premise; CASE 3 (o = sp) likewise. NO relation on s0Z is needed, and pj_write - whose
     o is its own frame at sp + 8 - threads nothing up to its callers. *)
  (* ONE CASE, the plain cut (the kit owner's ruling): indent is called ONLY from inside write_value's frame, with
     o >= spZ regs + 184, so it never sees case 2. put / write_value / put_string differ because each is called at
     o = spZ + 8 by something above it. *)
  (* indent keeps the PLAIN cut (it is called only from inside write_value's frame, o >= spZ regs + 184) and the
     same case-1 premise unconditionally; see tput_specX's note on the first record from o *)
  spZ regs + 16 <= o ->
  (exists ra, rdword (aview segs (w_H W) mem) (o - 8) = Some ra /\
    exists nfp, rdword (aview segs (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  (* ITS RUN EVENTS, as an entry premise: the run's next events are those of its puts, all granted (prhWriter_evs);
     supplied by the caller's own list (prhWriter_evs_app0, PRH_Base.prh_run_at_app_iff) *)
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterValue.wind (negb (pretty =? 0)) depth)) ->
  Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wind (negb (pretty =? 0)) depth))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  (* THE LIVE ROOM AT EACH EVENT (PRH_Base.prh_live_evs; the note above prhWriter_out): was the entry sum
     `blocks_bytes S + LIVE_indent st (negb (pretty =? 0)) depth <= LIVE_MAX` - no proof used it and it was not
     dischargeable; discharger the live-bytes owner's entry_sum_ok, proved (lib/Spec/PresetLiveBytes.v:1751) *)
  prh_live_evs S (prhWriter_evs [] st (WriterValue.wind (negb (pretty =? 0)) depth)) ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.17): fpostWm is SHARED, so the post is its R
     form at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_indent) regs mem md)
    (fpostWmR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) STK_indent d (prhWriter_cfp o buf (WriterApp.w_cap st))
       regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\ 
          (* THE EXACT ADVANCE: the entry position plus the events its puts made under the outcomes ok of
            prhWriter_ret_ok (one per granted grow; the allocation set to fail and a refusal make none) *)
          exists ok, prhWriter_ret_ok ok ly S Lam peak ran most own o buf st (WriterValue.wind (negb (pretty =? 0)) depth) ly' S' Hp' W' regs' mem' md' /\
          (* DEAD-INDENT (the refusal arm DEAD under prh_cons_from, above; three supports: PRH_Base's ENTRY-KEYED
             note): every false outcome of ok is the chosen
             failure; prh_granted admits it (it is NOT a refusal), so it claims no more *)
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st)
            (prhWriter_k ok st (WriterValue.wind (negb (pretty =? 0)) depth)) /\
          exists hist',
            PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st (WriterValue.wind (negb (pretty =? 0)%Z) depth)))%nat rp_H0 hist' S')).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tindent_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. tindP_Q IS the text's post (tindP_Q_check fails to build if
   the two ever differ); tindP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition tindP_Q (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (most own : Z) (ly : alayout) (S : astate) (o pretty depth buf : Z) (st :
    WriterApp.wst) (Lam : list (Z * Z)) (peak ran : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  room_live_cf S' /\ exists ok, prhWriter_ret_ok ok ly S Lam peak ran most own o buf st (WriterValue.wind (negb (pretty
      =? 0)) depth) ly' S' Hp' W' regs' mem' md' /\ prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st)
      (prhWriter_k ok st (WriterValue.wind (negb (pretty =? 0)) depth)) /\ exists hist', PresetRoomPos.iface_room_pos
      rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st (WriterValue.wind (negb (pretty =? 0)%Z) depth)))%nat rp_H0
      hist' S'.

Lemma tindP_Q_check : forall (CTX0 : list (list Z)), tindent_specX CTX0 -> tindent_specX CTX0.
Proof.
  intros CTX0 H. unfold tindent_specX in *.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch o pretty depth d buf st Lam peak ran HP0
      HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (tindP_Q rp_sm rp_x rp_os rp_i
      rp_H0 most own ly S o pretty depth buf st Lam peak ran) end.
  exact (H rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch o pretty depth d buf st Lam peak ran
      HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21).
Qed.

Record tindP_R (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i :
    nat) (rp_H0 : list Z) (most own : Z) (ly : alayout) (S : astate) (o pretty depth buf : Z) (st : WriterApp.wst) (Lam
    : list (Z * Z)) (peak ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5
    word) (mem' : word -> option byte) (md' : Model) (ok : list bool) (hist' : list chunk) : Prop := {
  tindP_room : room_live_cf S';
  tindP_ret_ok : prhWriter_ret_ok ok ly S Lam peak ran most own o buf st (WriterValue.wind (negb (pretty =? 0)) depth)
      ly' S' Hp' W' regs' mem' md';
  tindP_granted : prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (WriterValue.wind (negb
      (pretty =? 0)) depth));
  tindP_pos : PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st (WriterValue.wind (negb
      (pretty =? 0)%Z) depth)))%nat rp_H0 hist' S' }.

Lemma tindP_R_of : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (most own : Z) (ly : alayout) (S : astate) (o pretty depth buf : Z) (st :
    WriterApp.wst) (Lam : list (Z * Z)) (peak ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  tindP_Q rp_sm rp_x rp_os rp_i rp_H0 most own ly S o pretty depth buf st Lam peak ran ly' S' Hp' W' regs' mem' md' ->
  exists ok hist', tindP_R rp_sm rp_x rp_os rp_i rp_H0 most own ly S o pretty depth buf st Lam peak ran ly' S' Hp' W'
      regs' mem' md' ok hist'.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 most own ly S o pretty depth buf st Lam peak ran ly' S' Hp' W' regs' mem' md' H.
      destruct H as (H0 & ok & H1 & H2 & hist' & H3).
  exists ok, hist'.
  exact {| tindP_room := H0; tindP_ret_ok := H1; tindP_granted := H2; tindP_pos := H3 |}.
Qed.

Lemma tindP_Q_of_R : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (most own : Z) (ly : alayout) (S : astate) (o pretty depth buf : Z) (st :
    WriterApp.wst) (Lam : list (Z * Z)) (peak ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (ok : list bool) (hist' : list chunk),
  tindP_R rp_sm rp_x rp_os rp_i rp_H0 most own ly S o pretty depth buf st Lam peak ran ly' S' Hp' W' regs' mem' md' ok
      hist' ->
  tindP_Q rp_sm rp_x rp_os rp_i rp_H0 most own ly S o pretty depth buf st Lam peak ran ly' S' Hp' W' regs' mem' md'.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 most own ly S o pretty depth buf st Lam peak ran ly' S' Hp' W' regs' mem' md' ok
      hist' HR.
  refine (conj (tindP_room HR) _).
  exists ok.
  refine (conj (tindP_ret_ok HR) (conj (tindP_granted HR) _)).
  exists hist'.
  exact (tindP_pos HR).
Qed.

Local Unset Implicit Arguments.

(* put_string (:484-512; plain put_string_c.v:43-57): the pieces WriterSpec.spieces bs: a double quote, then each run
   of plain bytes followed by the escape of a special byte (:494-508), the last run, a double quote. The escape is
   built in an 8-byte buffer in put_string's frame_alloc_0 fake frame (A 0x87ea0; released before the return, so the
   frames are the entry's again): `\\n` / `\\t` / `\\r` by __asan_memcpy of 3 .rodata bytes, the double quote and the
   backslash by snprintf `\\%c`, the other control bytes by snprintf `\\u%04x` (named gap); then strlen and put. The
   string s is read by put_string's own
   byte loads and by put's __asan_memcpy after earlier puts, so it is cstr_ok and lives where those calls keep it
   (kept_at: in the tree, a live harness block other than the buffer). *)
Definition tput_string_specX (CTX0 : list (list Z)) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk) most own,
  forall ly S Hp W regs mem md ch o s d buf (st : WriterApp.wst) (bs : list Z) Lam peak ran,
  fpre B ARx STK_put_string ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S -> prh_univ_closure B CTX0 ->
  (* THE RUN HAS AT MOST 4 CALLS: its put calls take it (tput_specX) *)
  (length rp_os <= 4)%nat ->
  (* THE CALL'S ALLOCATIONS ARE CONSUMER ALLOCATIONS OF THE RUN (the ENTRY-KEYED texts' named entry premise,
     the kit owner's ruling 2026-10-29, extended to the writer's callees with pj_write's DEAD-PJWRITE), over
     this call's own all-granted events; its puts' grows are then consumer events, so the post states
     DEAD-PUTSTRING. Supplied by the caller from its own window (PRH_Base.prh_cons_from_sub). *)
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st (WriterSpec.spieces bs))) ->
  getr regs 10 = w64 o -> getr regs 11 = w64 s ->
  (* THE CHAIN FROM o, in the slice walker's MEASURED form (the S7a walk / the S7b walk; the kit owner's ruling, which WITHDREW the
     entry-view `spZ regs + 16 <= o` bound): this function holds the out struct o in s0 across its
     `jal fuzz_realloc`, so the callee's afn_pre_x needs a chain from o. put's stores before that call are
     FOURTEEN and ALL BELOW sp (sd ra -> sp-8, sd s0 -> sp-16, s1..s11 -> sp-24..sp-104, sd a0,0(sp) -> sp-112),
     nothing at or above sp, and s0 := o at A 0x86ba0 is unchanged to the call. So the cut on o against spZ regs
     covers every caller: CASE 1 (o >= sp + 16) is the only one that needs a caller chain, because all its reads
     are at or above o >= sp + 16 where put writes nothing, so the caller's entry-view chain carries over
     verbatim; CASE 2 (o = sp + 8, pj_write's own call, A 0x866d4 / 0x86718 / 0x86724) has word (o - 16) = put's
     own saved ra, a text address below alloc_ceiling, so bad_next fires and the walk builds the one-record
     chain with NO caller premise; CASE 3 (o = sp) likewise. NO relation on s0Z is needed, and pj_write - whose
     o is its own frame at sp + 8 - threads nothing up to its callers. *)
  (* TWO CASES (the kit owner's ruling on the slice walker's corrected measurement on d83eb25d): case 1, o at least 16 above
     the entry sp, takes the caller's entry-view chain from o; case 2, o = spZ regs + 8, which pj_write's call of
     write_value makes (A 0x8670c `jal write_value`, a0 = sp_pj + 8) and the top-level write_value's TAIL call of
     put_string makes (A 0x868a8 `j put_string`, after write_value restores sp) - there [o - 16] is this function's
     OWN saved ra, closed in its own walk by fpre's `raZ regs < YM05.alloc_ceiling`. *)
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (* THE FIRST RECORD FROM o, AS TWO WORDS (the kit owner's form (a), ruled 11:29Z; restated 2026-10-29 after two
     refuted spellings). The words at o - 8 (the saved ra) and o - 16 (the next fp) are caller-window words that
     NO put writes, and nfp < alloc_ceiling <= o makes bad_next fire, so the unwinder reads exactly this one
     record however often a loop rewrites the out struct [o, o + 32). REFUTED, so not to be proposed again:
     (1) an any-length chain `exists ch0, achain .. o ch0`: not transferable across a put that rewrites
     [o, o + 32), where a longer chain's later records can lie; (2) a one-record `exists r, achain .. o [r]`:
     it does NOT force bad_next, because fpchain's tail for a stopped chain is a READ at nfp - 8 (YG00.v:368-373)
     - the slice walker's witness at indent's loop call (A 0x881f0): word[o - 16] = o + 8 and word[o] = 0 at entry
     make `achain .. o [(o, ra, o + 8)]` hold, and after the first put grows the buffer word[o] >= 4096 and no
     one-record chain from o exists. The ra bound that closes CASE 2 is fpre's `raZ regs < YM05.alloc_ceiling`;
     its one-copy discharge is PRW_StepKit.pa_slot_lt_ceil (commit c3a0b928f54,
     lib/A/Prog/PRW_StepKit.v:235). *)
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview segs (w_H W) mem) (o - 8) = Some ra /\
       exists nfp, rdword (aview segs (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  (* wv_s0: see twrite_value_specX's note (the S7b put_string walk's measurement: every call of this frame-pointer function
     extends the chain from the caller's s0) *)
  s0Z regs = o \/ s0Z regs < YM05.alloc_ceiling ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  cstr_ok W mem s bs ->
  kept_at B Lam s (Z.of_nat (length bs) + 1) ->
  (* ITS RUN EVENTS, as an entry premise: the run's next events are those of its puts, all granted (prhWriter_evs);
     supplied by the caller's own list (prhWriter_evs_app0, PRH_Base.prh_run_at_app_iff) *)
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterSpec.spieces bs)) ->
  (WriterApp.w_cap st = 0 \/ s + Z.of_nat (length bs) + 1 <= buf \/ buf + WriterApp.w_cap st <= s) ->
  Z.of_nat (length (frames S)) < fs_frames 0 ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (WriterSpec.wstr bs)) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  (* THE LIVE ROOM AT EACH EVENT (PRH_Base.prh_live_evs; the note above prhWriter_out): was the entry sum
     `blocks_bytes S + LIVE_put_string st bs <= LIVE_MAX` - no proof used it and it was not dischargeable; discharger
     the live-bytes owner's entry_sum_ok, proved (lib/Spec/PresetLiveBytes.v:1751) *)
  prh_live_evs S (prhWriter_evs [] st (WriterSpec.spieces bs)) ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.18): fpostWFm is SHARED, so the post is its R
     form at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_put_string) regs mem md)
    (fpostWFmR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) STK_put_string d (prhWriter_cfp o buf (WriterApp.w_cap st))
       regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\ 
          (* THE EXACT ADVANCE: the entry position plus the events its puts made under the outcomes ok of
            prhWriter_ret_ok (one per granted grow; the allocation set to fail and a refusal make none) *)
          exists ok, prhWriter_ret_ok ok ly S Lam peak ran most own o buf st (WriterSpec.spieces bs) ly' S' Hp' W' regs' mem' md' /\
          (* DEAD-PUTSTRING (the refusal arm DEAD under prh_cons_from, above; three supports: PRH_Base's
             ENTRY-KEYED note): every false outcome of ok is the
             chosen failure; prh_granted admits it (it is NOT a refusal), so it claims no more *)
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (WriterSpec.spieces bs)) /\
          exists hist',
            PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st (WriterSpec.spieces bs)))%nat rp_H0 hist' S')).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tput_string_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. tpusP_Q IS the text's post (tpusP_Q_check fails to build if
   the two ever differ); tpusP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition tpusP_Q (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (most own : Z) (ly : alayout) (S : astate) (o buf : Z) (st : WriterApp.wst) (bs :
    list Z) (Lam : list (Z * Z)) (peak ran : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  room_live_cf S' /\ exists ok, prhWriter_ret_ok ok ly S Lam peak ran most own o buf st (WriterSpec.spieces bs) ly' S'
      Hp' W' regs' mem' md' /\ prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st
      (WriterSpec.spieces bs)) /\ exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length
      (prhWriter_evs ok st (WriterSpec.spieces bs)))%nat rp_H0 hist' S'.

Lemma tpusP_Q_check : forall (CTX0 : list (list Z)), tput_string_specX CTX0 -> tput_string_specX CTX0.
Proof.
  intros CTX0 H. unfold tput_string_specX in *.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch o s d buf st bs Lam peak ran HP0 HP1 HP2
      HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (tpusP_Q rp_sm rp_x rp_os rp_i
      rp_H0 most own ly S o buf st bs Lam peak ran) end.
  exact (H rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch o s d buf st bs Lam peak ran HP0 HP1
      HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23).
Qed.

Record tpusP_R (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i :
    nat) (rp_H0 : list Z) (most own : Z) (ly : alayout) (S : astate) (o buf : Z) (st : WriterApp.wst) (bs : list Z)
    (Lam : list (Z * Z)) (peak ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5
    word) (mem' : word -> option byte) (md' : Model) (ok : list bool) (hist' : list chunk) : Prop := {
  tpusP_room : room_live_cf S';
  tpusP_ret_ok : prhWriter_ret_ok ok ly S Lam peak ran most own o buf st (WriterSpec.spieces bs) ly' S' Hp' W' regs'
      mem' md';
  tpusP_granted : prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (WriterSpec.spieces bs));
  tpusP_pos : PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st (WriterSpec.spieces
      bs)))%nat rp_H0 hist' S' }.

Lemma tpusP_R_of : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (most own : Z) (ly : alayout) (S : astate) (o buf : Z) (st : WriterApp.wst) (bs
    : list Z) (Lam : list (Z * Z)) (peak ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs'
    : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  tpusP_Q rp_sm rp_x rp_os rp_i rp_H0 most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' ->
  exists ok hist', tpusP_R rp_sm rp_x rp_os rp_i rp_H0 most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem'
      md' ok hist'.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' H. destruct H
      as (H0 & ok & H1 & H2 & hist' & H3).
  exists ok, hist'.
  exact {| tpusP_room := H0; tpusP_ret_ok := H1; tpusP_granted := H2; tpusP_pos := H3 |}.
Qed.

Lemma tpusP_Q_of_R : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (most own : Z) (ly : alayout) (S : astate) (o buf : Z) (st : WriterApp.wst) (bs
    : list Z) (Lam : list (Z * Z)) (peak ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs'
    : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (ok : list bool) (hist' : list chunk),
  tpusP_R rp_sm rp_x rp_os rp_i rp_H0 most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' ok hist' ->
  tpusP_Q rp_sm rp_x rp_os rp_i rp_H0 most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md'.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 most own ly S o buf st bs Lam peak ran ly' S' Hp' W' regs' mem' md' ok hist' HR.
  refine (conj (tpusP_room HR) _).
  exists ok.
  refine (conj (tpusP_ret_ok HR) (conj (tpusP_granted HR) _)).
  exists hist'.
  exact (tpusP_pos HR).
Qed.

Local Unset Implicit Arguments.

(* write_value (:525-556; plain write_value_c.v:46-63), at most n nested calls of itself (the tree's depth, plain
   WV_K uses PjTree.depth): the pieces WriterValue.wvpieces t pretty depth: the literal, the number's text, the
   string (put_string, a TAIL CALL, A 0x868a8), or the bracketed items / members, each preceded by a comma from the
   second on and by indent (depth + 1), an object's key by put_string and `: ` / `:`; indent (depth) before the closing
   bracket of a non-empty one; the closing bracket is a TAIL CALL of put (A 0x86b00). The tree is read only: pj_nodeR
   over prh_lin Lam holds after; its node v is on the real stack between sp and the stack top (ly_stk_hi: the shadow of
   a real-stack byte is kept only through alx_zshadow_byte, which needs a < ly_stk_hi; the image-A writer walk's measurement of
   write_value's re-reads of v's shadow after put / indent, A 0x86818 .. 0x86a98), in a live harness block other than the buffer,
   or in a live fake frame, with its 56 bytes addressable; its blocks D are live harness blocks other than the buffer,
   visible as C data (prhWriter_tree_vis), and its bytes miss the struct. A tag above 6 writes nothing (A 0x867c0);
   pj_nodeR excludes it. *)
Definition twrite_value_specX (CTX0 : list (list Z)) (n : nat) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk) most own,
  forall ly S Hp W regs mem md ch o v pretty dep d buf (st : WriterApp.wst) (t : PjTree.jv) D Lam peak ran,
  fpre B ARx (STK_write_value n) ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* THE RUN HAS AT MOST 4 CALLS: its put / indent / put_string calls take it (tput_specX) *)
  (length rp_os <= 4)%nat ->
  (* THE CALL'S ALLOCATIONS ARE CONSUMER ALLOCATIONS OF THE RUN (the ENTRY-KEYED texts' named entry premise,
     the kit owner's ruling 2026-10-29, extended to the writer's callees with pj_write's DEAD-PJWRITE), over
     this call's own all-granted events; its puts' grows are then consumer events, so the post states
     DEAD-WRITEVALUE. Supplied by the caller from its own window (PRH_Base.prh_cons_from_sub). *)
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhWriter_evs [] st (WriterValue.wvpieces t (negb (pretty =? 0)) dep))) ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 dep ->
  0 <= pretty < 2 ^ 64 -> 0 <= dep < 2 ^ 31 -> dep + Z.of_nat (PjTree.depth t) <= 2 ^ 31 - 1 ->
  (PjTree.depth t <= n)%nat ->
  (* THE CHAIN FROM o, in the slice walker's MEASURED form (the S7a walk / the S7b walk; the kit owner's ruling, which WITHDREW the
     entry-view `spZ regs + 16 <= o` bound): this function holds the out struct o in s0 across its
     `jal fuzz_realloc`, so the callee's afn_pre_x needs a chain from o. put's stores before that call are
     FOURTEEN and ALL BELOW sp (sd ra -> sp-8, sd s0 -> sp-16, s1..s11 -> sp-24..sp-104, sd a0,0(sp) -> sp-112),
     nothing at or above sp, and s0 := o at A 0x86ba0 is unchanged to the call. So the cut on o against spZ regs
     covers every caller: CASE 1 (o >= sp + 16) is the only one that needs a caller chain, because all its reads
     are at or above o >= sp + 16 where put writes nothing, so the caller's entry-view chain carries over
     verbatim; CASE 2 (o = sp + 8, pj_write's own call, A 0x866d4 / 0x86718 / 0x86724) has word (o - 16) = put's
     own saved ra, a text address below alloc_ceiling, so bad_next fires and the walk builds the one-record
     chain with NO caller premise; CASE 3 (o = sp) likewise. NO relation on s0Z is needed, and pj_write - whose
     o is its own frame at sp + 8 - threads nothing up to its callers. *)
  (* TWO CASES (the kit owner's ruling on the slice walker's corrected measurement on d83eb25d): case 1, o at least 16 above
     the entry sp, takes the caller's entry-view chain from o; case 2, o = spZ regs + 8, which pj_write's call of
     write_value makes (A 0x8670c `jal write_value`, a0 = sp_pj + 8) and the top-level write_value's TAIL call of
     put_string makes (A 0x868a8 `j put_string`, after write_value restores sp) - there [o - 16] is this function's
     OWN saved ra, closed in its own walk by fpre's `raZ regs < YM05.alloc_ceiling`. *)
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (* THE FIRST RECORD FROM o, AS TWO WORDS (the kit owner's form (a), ruled 11:29Z; restated 2026-10-29 after two
     refuted spellings). The words at o - 8 (the saved ra) and o - 16 (the next fp) are caller-window words that
     NO put writes, and nfp < alloc_ceiling <= o makes bad_next fire, so the unwinder reads exactly this one
     record however often a loop rewrites the out struct [o, o + 32). REFUTED, so not to be proposed again:
     (1) an any-length chain `exists ch0, achain .. o ch0`: not transferable across a put that rewrites
     [o, o + 32), where a longer chain's later records can lie; (2) a one-record `exists r, achain .. o [r]`:
     it does NOT force bad_next, because fpchain's tail for a stopped chain is a READ at nfp - 8 (YG00.v:368-373)
     - the slice walker's witness at indent's loop call (A 0x881f0): word[o - 16] = o + 8 and word[o] = 0 at entry
     make `achain .. o [(o, ra, o + 8)]` hold, and after the first put grows the buffer word[o] >= 4096 and no
     one-record chain from o exists. The ra bound that closes CASE 2 is fpre's `raZ regs < YM05.alloc_ceiling`;
     its one-copy discharge is PRW_StepKit.pa_slot_lt_ceil (commit c3a0b928f54,
     lib/A/Prog/PRW_StepKit.v:235). *)
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview segs (w_H W) mem) (o - 8) = Some ra /\
       exists nfp, rdword (aview segs (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  (* wv_s0 (the S7b write_value walk's gap, the kit owner's ruling): a container's CLOSING bracket is a TAIL put (A 0x86b00)
     after write_value restored s0, so that call needs a chain from the CALLER's s0 at the TAIL memory, and fpre
     gives it only at the entry memory; the opening put (A 0x86804) rewrote [o, o + 32). Counterexample without
     this premise: s0 = o + 8 with word(o) = buf = 0 at entry (entry chain [] by fpchain's stop read) and
     word(o - 8) a valid fp f with f - 8 unmapped; after the put grows the buffer word(o) >= 4096 and no chain
     from o + 8 exists. Every real caller has s0 = o (write_value's self call, A 0x86a50; form (a)'s words at
     [o - 16, o) carry it) or s0 = pretty < 2 ^ 31 < alloc_ceiling (pj_write, A 0x866e4; achain's first arm, no
     read). tput_string_specX takes the SAME premise for a different reason (the S7b put_string walk's measurement):
     put_string has no tail put (its closing quote is a normal `jal put`, A 0x880f0, before `ret` at A 0x88190 -
     measured on the A twin f0d2e8d4's neutral listing), but it is a FRAME-POINTER function (`addi s0, sp, 192`,
     A 0x87e6c) that saves the caller's s0, so every call it makes pushes a record onto the chain from the
     CALLER's s0, and from put #2 on a record of that chain inside [o, o + 32) can break. Its callers satisfy it:
     write_value's tail `j put_string` (A 0x868a8) passes write_value's entry s0, and its inner call s0 = o.
     A PREMISE, NOT A DEFECT: no real caller violates it and both disjuncts discharge at once. *)
  s0Z regs = o \/ s0Z regs < YM05.alloc_ceiling ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  (* ITS RUN EVENTS, as an entry premise: the run's next events are those of its puts, all granted (prhWriter_evs);
     supplied by the caller's own list (prhWriter_evs_app0, PRH_Base.prh_run_at_app_iff) *)
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterValue.wvpieces t (negb (pretty =? 0)) dep)) ->
  pj_nodeR segs (rdW W mem) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/ (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/
   prhWriter_in_frame ly S v) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 56 ->
  prhWriter_tree_vis W mem D ->
  (forall a k, In (a, k) D -> In (a, k) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  Z.of_nat (length (frames S)) < fs_frames 0 ->
  Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wvpieces t (negb (pretty =? 0)) dep))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  (* THE LIVE ROOM AT EACH EVENT (PRH_Base.prh_live_evs; the note above prhWriter_out): was the entry sum
     `blocks_bytes S + LIVE_write_value st t (negb (pretty =? 0)) dep <= LIVE_MAX` - no proof used it and it was not
     dischargeable; discharger the live-bytes owner's entry_sum_ok, proved (lib/Spec/PresetLiveBytes.v:1751) *)
  prh_live_evs S (prhWriter_evs [] st (WriterValue.wvpieces t (negb (pretty =? 0)) dep)) ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.19): fpostWFm is SHARED, so the post is its R
     form at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_write_value) regs mem md)
    (fpostWFmR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) (STK_write_value n) d
       (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
          room_live_cf S' /\ 
          pj_nodeR segs (rdW W' mem') (prh_lin Lam) v t D /\
          (* THE EXACT ADVANCE: the entry position plus the events its puts made under the outcomes ok of
            prhWriter_ret_ok (one per granted grow; the allocation set to fail and a refusal make none) *)
          exists ok, prhWriter_ret_ok ok ly S Lam peak ran most own o buf st (WriterValue.wvpieces t (negb (pretty =? 0)) dep) ly' S' Hp' W' regs' mem' md' /\
          (* DEAD-WRITEVALUE (the refusal arm DEAD under prh_cons_from, above; three supports: PRH_Base's
             ENTRY-KEYED note): every false outcome of ok is the
             chosen failure; prh_granted admits it (it is NOT a refusal), so it claims no more *)
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st)
            (prhWriter_k ok st (WriterValue.wvpieces t (negb (pretty =? 0)) dep)) /\
          exists hist',
            PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st (WriterValue.wvpieces t (negb (pretty =? 0)%Z) dep)))%nat rp_H0 hist' S')).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== twrite_value_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. twvP_Q IS the text's post (twvP_Q_check fails to build if
   the two ever differ); twvP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition twvP_Q (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i
    : nat) (rp_H0 : list Z) (most own : Z) (ly : alayout) (S : astate) (o v pretty dep buf : Z) (st : WriterApp.wst) (t
    : PjTree.jv) (D Lam : list (Z * Z)) (peak ran : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  room_live_cf S' /\ pj_nodeR segs (rdW W' mem') (prh_lin Lam) v t D /\ exists ok, prhWriter_ret_ok ok ly S Lam peak
      ran most own o buf st (WriterValue.wvpieces t (negb (pretty =? 0)) dep) ly' S' Hp' W' regs' mem' md' /\
      prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (WriterValue.wvpieces t (negb
      (pretty =? 0)) dep)) /\ exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhWriter_evs
      ok st (WriterValue.wvpieces t (negb (pretty =? 0)%Z) dep)))%nat rp_H0 hist' S'.

Lemma twvP_Q_check : forall (CTX0 : list (list Z)) (n : nat), twrite_value_specX CTX0 n -> twrite_value_specX CTX0 n.
Proof.
  intros CTX0 n H. unfold twrite_value_specX in *.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch o v pretty dep d buf st t D Lam peak ran
      HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23
      HP24 HP25 HP26 HP27 HP28 HP29 HP30 HP31 HP32.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (twvP_Q rp_sm rp_x rp_os rp_i
      rp_H0 most own ly S o v pretty dep buf st t D Lam peak ran) end.
  exact (H rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch o v pretty dep d buf st t D Lam peak
      ran HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21 HP22 HP23
      HP24 HP25 HP26 HP27 HP28 HP29 HP30 HP31 HP32).
Qed.

Record twvP_R (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i :
    nat) (rp_H0 : list Z) (most own : Z) (ly : alayout) (S : astate) (o v pretty dep buf : Z) (st : WriterApp.wst) (t :
    PjTree.jv) (D Lam : list (Z * Z)) (peak ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (ok : list bool) (hist' : list chunk) : Prop := {
  twvP_room : room_live_cf S';
  twvP_node : pj_nodeR segs (rdW W' mem') (prh_lin Lam) v t D;
  twvP_ret_ok : prhWriter_ret_ok ok ly S Lam peak ran most own o buf st (WriterValue.wvpieces t (negb (pretty =? 0))
      dep) ly' S' Hp' W' regs' mem' md';
  twvP_granted : prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (WriterValue.wvpieces t
      (negb (pretty =? 0)) dep));
  twvP_pos : PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st (WriterValue.wvpieces t
      (negb (pretty =? 0)%Z) dep)))%nat rp_H0 hist' S' }.

Lemma twvP_R_of : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (most own : Z) (ly : alayout) (S : astate) (o v pretty dep buf : Z) (st :
    WriterApp.wst) (t : PjTree.jv) (D Lam : list (Z * Z)) (peak ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z)
    (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  twvP_Q rp_sm rp_x rp_os rp_i rp_H0 most own ly S o v pretty dep buf st t D Lam peak ran ly' S' Hp' W' regs' mem' md'
      ->
  exists ok hist', twvP_R rp_sm rp_x rp_os rp_i rp_H0 most own ly S o v pretty dep buf st t D Lam peak ran ly' S' Hp'
      W' regs' mem' md' ok hist'.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 most own ly S o v pretty dep buf st t D Lam peak ran ly' S' Hp' W' regs' mem' md'
      H. destruct H as (H0 & H1 & ok & H2 & H3 & hist' & H4).
  exists ok, hist'.
  exact {| twvP_room := H0; twvP_node := H1; twvP_ret_ok := H2; twvP_granted := H3; twvP_pos := H4 |}.
Qed.

Lemma twvP_Q_of_R : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (most own : Z) (ly : alayout) (S : astate) (o v pretty dep buf : Z) (st :
    WriterApp.wst) (t : PjTree.jv) (D Lam : list (Z * Z)) (peak ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z)
    (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (ok : list bool) (hist' : list
    chunk),
  twvP_R rp_sm rp_x rp_os rp_i rp_H0 most own ly S o v pretty dep buf st t D Lam peak ran ly' S' Hp' W' regs' mem' md'
      ok hist' ->
  twvP_Q rp_sm rp_x rp_os rp_i rp_H0 most own ly S o v pretty dep buf st t D Lam peak ran ly' S' Hp' W' regs' mem' md'.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 most own ly S o v pretty dep buf st t D Lam peak ran ly' S' Hp' W' regs' mem' md'
      ok hist' HR.
  refine (conj (twvP_room HR) (conj (twvP_node HR) _)).
  exists ok.
  refine (conj (twvP_ret_ok HR) (conj (twvP_granted HR) _)).
  exists hist'.
  exact (twvP_pos HR).
Qed.

Local Unset Implicit Arguments.

(* pj_write (:558-571; plain pj_write_c.v:94-108), at most n nested write_value calls: the struct is in its own frame
   (zeroed by __asan_memset, A 0x866f8), write_value (o, v, pretty, 0), put a newline if pretty; failed: fuzz_free (buf)
   (A 0x86734; buf may be NULL) and NULL; else buf. The document is WriterValue.wdoc t pretty (the pieces wdpieces).
   It reaches fuzz_free with s0 = pretty (A 0x866e4: an integer below alloc_ceiling, so the chain at the call is
   empty) and fuzz_free tail-calls the free wrapper with pj_write's return site: the free's trace is the pc0-filtered
   prh_trace pc_free_ra0 r [] for r in pi_ret_sites F_pj_write RT_fuzz_free (or [pc_free_ra0] when the frame check fails), both
   in prh_univ_closure (prh_univ_closure_lit), so the entry chain does not enter it. Write set: its frame, the new
   block (not pre-existing: FP is empty), the statics (PST), errno on a refusal. Success: the text in a new live
   harness block (q, cap) at the head
   of Lam. Failure: NULL, the buffer (if any) freed, Lam unchanged, g_peak as the last granted grow and a refused grow
   left it (prhWriter_rpeak). *)
Definition tpj_write_specX (CTX0 : list (list Z)) (n : nat) : Prop :=
  forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk) most own,
  forall ly S Hp W regs mem md ch v pretty (t : PjTree.jv) D Lam peak cnt fail ran,
  fpre B ARx (STK_pj_write n) ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 ->
  room_live_cf S -> PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* THE RUN HAS AT MOST 4 CALLS: its callees take it (twrite_value_specX), and it pays any post-form
     callee's hull budget from its position (lib/A/PresetHullPay.v hull_budget_of_room_pos) *)
  (length rp_os <= 4)%nat ->
  (* THE RUN'S STRTOD MODEL IS KEYED (the unit owner's ruling HP_sm, one of six: tcheck_reject_clean_starved,
     tround_trip_text, tcheck_round_trip, tpj_set, tpj_string, tpj_write): the events of these six are spelled over
     the reader, so their CONTENT fixes the run's strtod model, and each writes ReaderRes.jr_strtod where rp_sm stood -
     no rp_sm binder, no `rp_sm = ReaderRes.jr_strtod` premise. A text carries exactly the constraints its content
     needs, no more and no fewer: the eight writer / tx texts above (tput, tindent, tput_string, twrite_value, and
     PRH_FnTx's ttx_put, ttx_string, ttx_line, ttx_value) keep rp_sm free. *)
  (* THE CALL'S ALLOCATIONS ARE CONSUMER ALLOCATIONS OF THE RUN (the kit owner's ruling 2026-10-29, the NAMED
     entry premise of the ENTRY-KEYED texts, here as in the three check texts). With the entry position and the run
     premise, P8 (PresetCfnA.preset_no_refusal; a NULL of malloc_cf is primary-only, YG0dcf.malloc_cf_null_post) and
     the engine's granted paths (PRH_Base.prh_rpost_granted over amreal, YG0d.v:73-92) exclude a REAL refusal at
     every allocation of the call (each grow's fuzz_realloc of the buffer), so the post states the refusal arm DEAD
     (DEAD-PJWRITE). Supplied by the caller (round_trip_text, check_reject_clean_starved) from its own
     prh_cons_from (PRH_Base.prh_cons_from_app_iff splits its window). *)
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i
    (length (prhWriter_pjw_evs [] cnt fail (WriterValue.wdpieces t (negb (pretty =? 0))))) ->
  getr regs 10 = w64 v -> getr regs 11 = w64 pretty -> 0 <= pretty < 2 ^ 31 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (* ITS RUN EVENTS, as an entry premise: its puts' all granted, then the fuzz_free (buf) of a failed writer with a
     buffer (prhWriter_pjw_evs; the model's w_evs / w_starved); supplied by its caller *)
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (prhWriter_pjw_evs [] cnt fail (WriterValue.wdpieces t (negb (pretty =? 0)))) ->
  pj_nodeR segs (rdW W mem) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/ (exists x y, In (x, y) Lam /\ x <= v /\ v + 56 <= x + y) \/
   prhWriter_in_frame ly S v) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 56 ->
  prhWriter_tree_vis W mem D ->
  (forall a k, In (a, k) D -> In (a, k) Lam) ->
  (PjTree.depth t <= n)%nat -> Z.of_nat (PjTree.depth t) <= 2 ^ 31 - 1 ->
  Z.of_nat (length (frames S)) < fs_frames 0 ->
  Z.of_nat (length (WriterValue.wdoc t (negb (pretty =? 0)))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  blocks_bytes S + LIVE_pj_write t (negb (pretty =? 0)) <= LIVE_MAX ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.20); fpostFm is already at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_pj_write) regs mem md)
    (fpostFm B ARx SK (STK_pj_write n) [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       exists ok ran' q Lam' peak',
       let P := WriterValue.wdpieces t (negb (pretty =? 0)) in
       let st' := prhWriter_putN ok (WriterApp.w0 cnt fail) P in
       prh_oks ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) (prhWriter_reqs ok (WriterApp.w0 cnt fail) P) most
         ran ran' /\
       getr regs' 10 = w64 q /\
       room_live_cf S' /\
       (* DEAD-PJWRITE (the refusal arm DEAD under prh_cons_from, above; three supports: PRH_Base's ENTRY-KEYED
          note): no grow of the outcomes ok was REFUSED -
          every false outcome is the chosen failure (prh_granted). prh_granted already admits the chosen failure
          (cnt + i = fail), which is NOT a refusal and which prh_cons_from does not exclude, so the conjunct needs no
          window condition and claims no more: the failed arm below stays, reached by the chosen failure alone. *)
       prh_granted ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) /\
       (* THE EXACT ADVANCE, when no grow was REFUSED (prh_granted): the entry position plus the events made under ok.
          After a refusal there is no position of the model's run to state: the instance then frees the buffer at
          :567-570 while the all-granted run holds it and grows it next (a refusal is excluded once, globally, by
          the driver) *)
       (prh_granted ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) ->
          exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os (rp_i + length (prhWriter_pjw_evs ok cnt fail P))%nat
            rp_H0 hist' S') /\
       pj_nodeR segs (rdW W' mem') (prh_lin Lam) v t D /\
       prhWriter_tree_vis W' mem' D /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt st') (WriterApp.w_fail st') ran' most own /\
       ((WriterApp.w_failed st' = 0 /\ q <> 0 /\ ~ In (q - cf_head, WriterApp.w_cap st' + cf_head) (ablocks B ly S) /\
         Lam' = (q, WriterApp.w_cap st') :: Lam /\ peak' = Z.max peak (Ledger.lsum Lam + WriterApp.w_cap st') /\
         Permutation (ablocks B ly' S') ((q - cf_head, WriterApp.w_cap st' + cf_head) :: ablocks B ly S) /\
         Z.of_nat (length (WriterValue.wdoc t (negb (pretty =? 0)))) < WriterApp.w_cap st' /\
         bytes_at W' mem' q (WriterValue.wdoc t (negb (pretty =? 0)) ++ [0]))
        \/
        (WriterApp.w_failed st' <> 0 /\ q = 0 /\ Lam' = Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
         (* THE REFUSAL TERM (#102, prhWriter_rpeak). COUNTEREXAMPLE to the form without it: the first grow,
            fuzz_realloc (NULL, 4096), refused with cnt <> fail: the capacity stays 0 and g_peak = Ledger.lsum Lam + 4096,
            where peak' = peak was stated; on the cap' <> 0 arm a later grow refused raises g_peak past
            Ledger.lsum Lam + cap' in the same way. *)
         ((WriterApp.w_cap st' = 0 /\ peak' = Z.max peak (prhWriter_rpeak ok Lam (WriterApp.w0 cnt fail) P)) \/
          (WriterApp.w_cap st' <> 0 /\
           peak' = Z.max (Z.max peak (Ledger.lsum Lam + WriterApp.w_cap st'))
             (prhWriter_rpeak ok Lam (WriterApp.w0 cnt fail) P))))))).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== tpj_write_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. tpwP_Q IS the text's post (tpwP_Q_check fails to build if
   the two ever differ); tpwP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition tpwP_A1 (ly : alayout) (S : astate) (pretty : Z) (t : PjTree.jv) (Lam : list (Z * Z)) (peak : Z) (ly' :
    alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (q : Z) (Lam' : list (Z * Z)) (peak' : Z)
    (st' : WriterApp.wst) : Prop :=
  WriterApp.w_failed st' = 0 /\ q <> 0 /\ ~ In (q - cf_head, WriterApp.w_cap st' + cf_head) (ablocks B ly S) /\ Lam' =
      (q, WriterApp.w_cap st') :: Lam /\ peak' = Z.max peak (Ledger.lsum Lam + WriterApp.w_cap st') /\ Permutation
      (ablocks B ly' S') ((q - cf_head, WriterApp.w_cap st' + cf_head) :: ablocks B ly S) /\ Z.of_nat (length
      (WriterValue.wdoc t (negb (pretty =? 0)))) < WriterApp.w_cap st' /\ bytes_at W' mem' q (WriterValue.wdoc t (negb
      (pretty =? 0)) ++ [0]).

Definition tpwP_A21 (Lam : list (Z * Z)) (peak cnt fail : Z) (ok : list bool) (peak' : Z) (P : list (list Z)) (st' :
    WriterApp.wst) : Prop :=
  WriterApp.w_cap st' = 0 /\ peak' = Z.max peak (prhWriter_rpeak ok Lam (WriterApp.w0 cnt fail) P).

Definition tpwP_A22 (Lam : list (Z * Z)) (peak cnt fail : Z) (ok : list bool) (peak' : Z) (P : list (list Z)) (st' :
    WriterApp.wst) : Prop :=
  WriterApp.w_cap st' <> 0 /\ peak' = Z.max (Z.max peak (Ledger.lsum Lam + WriterApp.w_cap st')) (prhWriter_rpeak ok
      Lam (WriterApp.w0 cnt fail) P).

Definition tpwP_A2 (ly : alayout) (S : astate) (Lam : list (Z * Z)) (peak cnt fail : Z) (ly' : alayout) (S' : astate)
    (ok : list bool) (q : Z) (Lam' : list (Z * Z)) (peak' : Z) (P : list (list Z)) (st' : WriterApp.wst) : Prop :=
  WriterApp.w_failed st' <> 0 /\ q = 0 /\ Lam' = Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\ (tpwP_A21
      Lam peak cnt fail ok peak' P st' \/ tpwP_A22 Lam peak cnt fail ok peak' P st').

Definition tpwP_Q (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z)
    (most own : Z) (ly : alayout) (S : astate) (v pretty : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (peak cnt fail ran
    : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  exists ok ran' q Lam' peak', let P := WriterValue.wdpieces t (negb (pretty =? 0)) in let st' := prhWriter_putN ok
      (WriterApp.w0 cnt fail) P in prh_oks ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) (prhWriter_reqs ok
      (WriterApp.w0 cnt fail) P) most ran ran' /\ getr regs' 10 = w64 q /\ room_live_cf S' /\ prh_granted ok cnt fail
      (prhWriter_k ok (WriterApp.w0 cnt fail) P) /\ (prh_granted ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P)
      -> exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os (rp_i + length (prhWriter_pjw_evs ok
      cnt fail P))%nat rp_H0 hist' S') /\ pj_nodeR segs (rdW W' mem') (prh_lin Lam) v t D /\ prhWriter_tree_vis W' mem'
      D /\ prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt st') (WriterApp.w_fail st') ran' most own /\
      (tpwP_A1 ly S pretty t Lam peak ly' S' W' mem' q Lam' peak' st' \/ tpwP_A2 ly S Lam peak cnt fail ly' S' ok q
      Lam' peak' P st').

Lemma tpwP_Q_check : forall (CTX0 : list (list Z)) (n : nat), tpj_write_specX CTX0 n -> tpj_write_specX CTX0 n.
Proof.
  intros CTX0 n H. unfold tpj_write_specX in *.
  intros rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch v pretty t D Lam peak cnt fail ran HP0 HP1 HP2
      HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (tpwP_Q rp_x rp_os rp_i rp_H0 most
      own ly S v pretty t D Lam peak cnt fail ran) end.
  exact (H rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch v pretty t D Lam peak cnt fail ran HP0 HP1
      HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21).
Qed.

Record tpwP_R (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z) (most
    own : Z) (ly : alayout) (S : astate) (v pretty : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (peak cnt fail ran : Z)
    (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte)
    (ok : list bool) (ran' q : Z) (Lam' : list (Z * Z)) (peak' : Z) (P : list (list Z)) (st' : WriterApp.wst) : Prop :=
    {
  tpwP_oks : prh_oks ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) (prhWriter_reqs ok (WriterApp.w0 cnt fail)
      P) most ran ran';
  tpwP_ret : getr regs' 10 = w64 q;
  tpwP_room : room_live_cf S';
  tpwP_granted : prh_granted ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P);
  tpwP_pos : (prh_granted ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) -> exists hist',
      PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os (rp_i + length (prhWriter_pjw_evs ok cnt fail P))%nat
      rp_H0 hist' S');
  tpwP_node : pj_nodeR segs (rdW W' mem') (prh_lin Lam) v t D;
  tpwP_tree_vis : prhWriter_tree_vis W' mem' D;
  tpwP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt st') (WriterApp.w_fail st') ran' most own;
  tpwP_arm : (tpwP_A1 ly S pretty t Lam peak ly' S' W' mem' q Lam' peak' st' \/ tpwP_A2 ly S Lam peak cnt fail ly' S'
      ok q Lam' peak' P st') }.

Lemma tpwP_R_of : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 :
    list Z) (most own : Z) (ly : alayout) (S : astate) (v pretty : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (peak cnt
    fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word ->
    option byte) (md' : Model),
  tpwP_Q rp_x rp_os rp_i rp_H0 most own ly S v pretty t D Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' ->
  exists ok ran' q Lam' peak', let P := WriterValue.wdpieces t (negb (pretty =? 0)) in let st' := prhWriter_putN ok
      (WriterApp.w0 cnt fail) P in tpwP_R rp_x rp_os rp_i rp_H0 most own ly S v pretty t D Lam peak cnt fail ran ly' S'
      Hp' W' regs' mem' ok ran' q Lam' peak' P st'.
Proof.
  intros rp_x rp_os rp_i rp_H0 most own ly S v pretty t D Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' H.
      destruct H as (ok & ran' & q & Lam' & peak' & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  exists ok, ran', q, Lam', peak'.
  intros P.
  intros st'.
  exact {| tpwP_oks := H0; tpwP_ret := H1; tpwP_room := H2; tpwP_granted := H3; tpwP_pos := H4; tpwP_node := H5;
      tpwP_tree_vis := H6; tpwP_ledger := H7; tpwP_arm := H8 |}.
Qed.

Lemma tpwP_Q_of_R : forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 :
    list Z) (most own : Z) (ly : alayout) (S : astate) (v pretty : Z) (t : PjTree.jv) (D Lam : list (Z * Z)) (peak cnt
    fail ran : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word ->
    option byte) (md' : Model) (ok : list bool) (ran' q : Z) (Lam' : list (Z * Z)) (peak' : Z),
  let P := WriterValue.wdpieces t (negb (pretty =? 0)) in let st' := prhWriter_putN ok (WriterApp.w0 cnt fail) P in
      tpwP_R rp_x rp_os rp_i rp_H0 most own ly S v pretty t D Lam peak cnt fail ran ly' S' Hp' W' regs' mem' ok ran' q
      Lam' peak' P st' ->
  tpwP_Q rp_x rp_os rp_i rp_H0 most own ly S v pretty t D Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md'.
Proof.
  intros rp_x rp_os rp_i rp_H0 most own ly S v pretty t D Lam peak cnt fail ran ly' S' Hp' W' regs' mem' md' ok ran' q
      Lam' peak' P st' HR.
  exists ok, ran', q, Lam', peak'.
  intros P_l.
  intros st__l.
  exact (conj (tpwP_oks HR) (conj (tpwP_ret HR) (conj (tpwP_room HR) (conj (tpwP_granted HR) (conj (tpwP_pos HR) (conj
      (tpwP_node HR) (conj (tpwP_tree_vis HR) (conj (tpwP_ledger HR) (tpwP_arm HR))))))))).
Qed.

Record tpwP_R1 (ly : alayout) (S : astate) (pretty : Z) (t : PjTree.jv) (Lam : list (Z * Z)) (peak : Z) (ly' : alayout)
    (S' : astate) (W' : world segs) (mem' : word -> option byte) (q : Z) (Lam' : list (Z * Z)) (peak' : Z) (st' :
    WriterApp.wst) : Prop := {
  tpwP1_ok : WriterApp.w_failed st' = 0;
  tpwP1_nonnull : q <> 0;
  tpwP1_fresh : ~ In (q - cf_head, WriterApp.w_cap st' + cf_head) (ablocks B ly S);
  tpwP1_lam : Lam' = (q, WriterApp.w_cap st') :: Lam;
  tpwP1_peak : peak' = Z.max peak (Ledger.lsum Lam + WriterApp.w_cap st');
  tpwP1_ablocks : Permutation (ablocks B ly' S') ((q - cf_head, WriterApp.w_cap st' + cf_head) :: ablocks B ly S);
  tpwP1_fits : Z.of_nat (length (WriterValue.wdoc t (negb (pretty =? 0)))) < WriterApp.w_cap st';
  tpwP1_bytes : bytes_at W' mem' q (WriterValue.wdoc t (negb (pretty =? 0)) ++ [0]) }.

Lemma tpwP_R1_of : forall (ly : alayout) (S : astate) (pretty : Z) (t : PjTree.jv) (Lam : list (Z * Z)) (peak : Z) (ly'
    : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (q : Z) (Lam' : list (Z * Z)) (peak' : Z)
    (st' : WriterApp.wst),
  tpwP_A1 ly S pretty t Lam peak ly' S' W' mem' q Lam' peak' st' ->
  tpwP_R1 ly S pretty t Lam peak ly' S' W' mem' q Lam' peak' st'.
Proof.
  intros ly S pretty t Lam peak ly' S' W' mem' q Lam' peak' st' H. destruct H as (H0 & H1 & H2 & H3 & H4 & H5 & H6 &
      H7).
  exact {| tpwP1_ok := H0; tpwP1_nonnull := H1; tpwP1_fresh := H2; tpwP1_lam := H3; tpwP1_peak := H4; tpwP1_ablocks :=
      H5; tpwP1_fits := H6; tpwP1_bytes := H7 |}.
Qed.

Lemma tpwP_A1_of_R : forall (ly : alayout) (S : astate) (pretty : Z) (t : PjTree.jv) (Lam : list (Z * Z)) (peak : Z)
    (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (q : Z) (Lam' : list (Z * Z)) (peak' :
    Z) (st' : WriterApp.wst),
  tpwP_R1 ly S pretty t Lam peak ly' S' W' mem' q Lam' peak' st' ->
  tpwP_A1 ly S pretty t Lam peak ly' S' W' mem' q Lam' peak' st'.
Proof.
  intros ly S pretty t Lam peak ly' S' W' mem' q Lam' peak' st' HR.
  exact (conj (tpwP1_ok HR) (conj (tpwP1_nonnull HR) (conj (tpwP1_fresh HR) (conj (tpwP1_lam HR) (conj (tpwP1_peak HR)
      (conj (tpwP1_ablocks HR) (conj (tpwP1_fits HR) (tpwP1_bytes HR)))))))).
Qed.

Record tpwP_R21 (Lam : list (Z * Z)) (peak cnt fail : Z) (ok : list bool) (peak' : Z) (P : list (list Z)) (st' :
    WriterApp.wst) : Prop := {
  tpwP21_cap0 : WriterApp.w_cap st' = 0;
  tpwP21_peak : peak' = Z.max peak (prhWriter_rpeak ok Lam (WriterApp.w0 cnt fail) P) }.

Lemma tpwP_R21_of : forall (Lam : list (Z * Z)) (peak cnt fail : Z) (ok : list bool) (peak' : Z) (P : list (list Z))
    (st' : WriterApp.wst),
  tpwP_A21 Lam peak cnt fail ok peak' P st' ->
  tpwP_R21 Lam peak cnt fail ok peak' P st'.
Proof.
  intros Lam peak cnt fail ok peak' P st' H. destruct H as (H0 & H1).
  exact {| tpwP21_cap0 := H0; tpwP21_peak := H1 |}.
Qed.

Lemma tpwP_A21_of_R : forall (Lam : list (Z * Z)) (peak cnt fail : Z) (ok : list bool) (peak' : Z) (P : list (list Z))
    (st' : WriterApp.wst),
  tpwP_R21 Lam peak cnt fail ok peak' P st' ->
  tpwP_A21 Lam peak cnt fail ok peak' P st'.
Proof.
  intros Lam peak cnt fail ok peak' P st' HR.
  exact (conj (tpwP21_cap0 HR) (tpwP21_peak HR)).
Qed.

Record tpwP_R22 (Lam : list (Z * Z)) (peak cnt fail : Z) (ok : list bool) (peak' : Z) (P : list (list Z)) (st' :
    WriterApp.wst) : Prop := {
  tpwP22_capnz : WriterApp.w_cap st' <> 0;
  tpwP22_peak : peak' = Z.max (Z.max peak (Ledger.lsum Lam + WriterApp.w_cap st')) (prhWriter_rpeak ok Lam
      (WriterApp.w0 cnt fail) P) }.

Lemma tpwP_R22_of : forall (Lam : list (Z * Z)) (peak cnt fail : Z) (ok : list bool) (peak' : Z) (P : list (list Z))
    (st' : WriterApp.wst),
  tpwP_A22 Lam peak cnt fail ok peak' P st' ->
  tpwP_R22 Lam peak cnt fail ok peak' P st'.
Proof.
  intros Lam peak cnt fail ok peak' P st' H. destruct H as (H0 & H1).
  exact {| tpwP22_capnz := H0; tpwP22_peak := H1 |}.
Qed.

Lemma tpwP_A22_of_R : forall (Lam : list (Z * Z)) (peak cnt fail : Z) (ok : list bool) (peak' : Z) (P : list (list Z))
    (st' : WriterApp.wst),
  tpwP_R22 Lam peak cnt fail ok peak' P st' ->
  tpwP_A22 Lam peak cnt fail ok peak' P st'.
Proof.
  intros Lam peak cnt fail ok peak' P st' HR.
  exact (conj (tpwP22_capnz HR) (tpwP22_peak HR)).
Qed.

Record tpwP_R2 (ly : alayout) (S : astate) (Lam : list (Z * Z)) (peak cnt fail : Z) (ly' : alayout) (S' : astate) (ok :
    list bool) (q : Z) (Lam' : list (Z * Z)) (peak' : Z) (P : list (list Z)) (st' : WriterApp.wst) : Prop := {
  tpwP2_failed : WriterApp.w_failed st' <> 0;
  tpwP2_null : q = 0;
  tpwP2_lam : Lam' = Lam;
  tpwP2_ablocks : Permutation (ablocks B ly' S') (ablocks B ly S);
  tpwP2_peak : (tpwP_A21 Lam peak cnt fail ok peak' P st' \/ tpwP_A22 Lam peak cnt fail ok peak' P st') }.

Lemma tpwP_R2_of : forall (ly : alayout) (S : astate) (Lam : list (Z * Z)) (peak cnt fail : Z) (ly' : alayout) (S' :
    astate) (ok : list bool) (q : Z) (Lam' : list (Z * Z)) (peak' : Z) (P : list (list Z)) (st' : WriterApp.wst),
  tpwP_A2 ly S Lam peak cnt fail ly' S' ok q Lam' peak' P st' ->
  tpwP_R2 ly S Lam peak cnt fail ly' S' ok q Lam' peak' P st'.
Proof.
  intros ly S Lam peak cnt fail ly' S' ok q Lam' peak' P st' H. destruct H as (H0 & H1 & H2 & H3 & H4).
  exact {| tpwP2_failed := H0; tpwP2_null := H1; tpwP2_lam := H2; tpwP2_ablocks := H3; tpwP2_peak := H4 |}.
Qed.

Lemma tpwP_A2_of_R : forall (ly : alayout) (S : astate) (Lam : list (Z * Z)) (peak cnt fail : Z) (ly' : alayout) (S' :
    astate) (ok : list bool) (q : Z) (Lam' : list (Z * Z)) (peak' : Z) (P : list (list Z)) (st' : WriterApp.wst),
  tpwP_R2 ly S Lam peak cnt fail ly' S' ok q Lam' peak' P st' ->
  tpwP_A2 ly S Lam peak cnt fail ly' S' ok q Lam' peak' P st'.
Proof.
  intros ly S Lam peak cnt fail ly' S' ok q Lam' peak' P st' HR.
  exact (conj (tpwP2_failed HR) (conj (tpwP2_null HR) (conj (tpwP2_lam HR) (conj (tpwP2_ablocks HR) (tpwP2_peak HR))))).
Qed.

Local Unset Implicit Arguments.

End c.
