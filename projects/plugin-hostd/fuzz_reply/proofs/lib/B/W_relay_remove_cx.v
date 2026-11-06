(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the SEGMENT INTERFACE of the IMAGE-B walk of fuzz_reply's relay_remove
   (fuzz_reply.asan-ubsan 0x841fc .. 0x84408, 131 instructions), the twin of lib/A/W_relay_remove_cx.v (lib/A input:
   a working branch 6a1bcf9f403).  Hand-written, not generated: image B's relay_remove is a different function
   (UBSan trap mode), so only the FORM carries over (W_kit.v header: the kit relocates, the walks do not).  Nothing is
   proved here: the file fixes the Section hypotheses, the entry context, the cut predicates over concrete machine
   states and the statement of every segment, so that the segments are proved in parallel.

   IMAGE B AGAINST IMAGE A.
   - Frame 48 bytes, six saves (s4 0(sp), s3 8, s2 16, s1 24, s0 32, ra 40); NO fake frame (image A takes a class-0
     fake frame for the wake byte; image B keeps the byte in wake's own frame), so the journal owns no frame
     (own = []).  s5 .. s11 are never written and so kept in their registers.
   - The wake test is a TAIL CALL: 0x843e8 `j wake` after the epilogue; wake's contract is lib/B/W_wake_c.v wk_spec
     (WAKE below).  fd < 0 returns at 0x842b8 without the lock and without wake.
   - UBSan traps (`unimp` at 0x843ec; 14 trap edges, TRAPS-ALL.md (sha256 c90982171c9b; internal record)): in the scan, the pointer-overflow
     check of g_src + 56k (0x84270 `bltu a0,a1`), the null-consistency xor (0x8427c), and the one-time flags a3 =
     (G0 <> 0) and a4 = (G0 <> 0 && G0 mod 8 = 0) computed at 0x8425c-0x84268 (0x84280 `beqz a4`); in MATCH, the same
     checks for each reload of g_src + 56i (0x84300 .. 0x84340), the int32 decrement of g_nsrc (0x84384) and the
     memcpy's index checks (0x843a0 .. 0x843b4).  The trap kit is lib/B/W_traps.v (a working branch).
   - g_src is loaded ONCE before the loop (0x8424c, into a1); the scan's shadow check computes (a0 >> 3) + s2 itself.

   CUT POINTS
     RRL k   0x8426c  the scan loop's head at index k (s3 = 56 k), the lock held, nothing changed yet;
     RRM i   0x842d8  the scan found fd at index i (a0 = G0 + 56 i), nothing changed yet;
     RRU oi  0x843c0  the unlock tail (also the empty table 0x84240 and the scan's exit 0x842a0): oi = None, no entry
                      has fd and nothing changed; oi = Some i, entry i handled (MATCH's memcpy returns here).
   SEGMENTS
     PRO    0x841fc -> RRL 0 | RRU None | rr_post (fd < 0)     the saves, the GOT load of the shadow base, the lock
     SCAN   RRL k -> RRL (S k) | RRM k | RRU None             one step of the scan loop: NO CALLS, NO STORES
     SCANS  the scan loop by induction on |es| - k            composition of SCAN
     MATCH  RRM i -> RRU (Some i)                             drain, gestures_end, free, g_nsrc -= 1, __asan_memcpy
     TAIL   RRU oi -> rr_post                                 unlock, the epilogue, the tail call of wake
   Every segment concludes `SRr SEGS W1 c1 (rPOST cx)` and takes its continuations in the same form.

   STATEMENT TEXT: RBASE is exactly the kit's rr_spec premise list (lib/B/W_contract.v at bkit 416c8ab2a27, from
   kitin c0b1d3382c2, which carries rg_place and lib/A 1744b876fbd's capacity conjuncts).  C3 (the peak form, the
   image-A twin's 475b8a2b569) removed both capacity conjuncts (`rxcap cx < MMAX` and `blocks_bytes + tr_alloc +
   4 * max cap tr_max <= LIVE_MAX`): the callees' room premises (dr_spec, ge_room, gse_room) are stated over their
   traces' peak (W_contract.v tr_peak), so rr_spec asks only tr_max tr < MMAX and blocks_bytes S + tr_peak tr <=
   LIVE_MAX, and RBASE, RHELD and W_rr_match_cx.v rmbud carry the peak form (the kit is W_tr_peak.v).
   CONSUMER NOTE (the B top's call of relay_remove): rr_spec's room premises at the call are `tr_max tr < MMAX` and
   `blocks_bytes S + tr_peak tr <= LIVE_MAX`, with tr = rr_tr c mx |O| cap FD es h; the two premises `cap < MMAX` and
   `blocks_bytes S + tr_alloc tr + 4 * Z.max cap (tr_max tr) <= LIVE_MAX` are gone. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record)) in the room form, the
   image-A twin's (a Theorem Labs lane, commit f4cd818e98d, lib/A/W_relay_remove_cx.v) over image B's walk (lane RRX): the
   segment interface over ANY allocator relation ARx with its laws, IN PLACE (the AR theorem is dropped, a Theorem Labs lane
   10:34Z).  Section c takes the generic relation (PST / ARx / hl / LAWS / HP0), the frame twins' hypotheses of
   W_frame_x.v (IMGC at image B's top 0x5fc000, BLKN, OWNLOW, WFx / WFL, SFREE, SMALLOC, ASMP / ASF / FFL: wake's fake
   frame, W_wake_x.v), the PST facts PSTR / PSTG (rr_gcells, below) and every callee in its _x room form (dr_spec_x,
   gse_spec_x, afree_cf_rule_c_x / afree_null_cf_rule_c_x, alock_realizes_x / aunlock_realizes_x, aintrin_realizes_x /
   amemcpy_same_realizes_x, and image B's tail-called wake by W_wake_c_x.v wk_spec_x).  The entry record rcx gains the
   ghost set rxHp (after rxS) and the room budget rxkr; RBASE is rr_spec_x's premises EXACTLY (afn_pre_x at RR_STK_x,
   W_contract_x.v's relay_remove budget, then the AR premises, then the room record: rp_RM RP S
   (Z.to_nat (tr_cost MT_rk tr) + kr) and cnt_ok_pk RP (rr_pk tr)), RCTX its last premise, the post rPOST is
   rr_post_x.  The cut predicates' journal is ajournal_gx_x at RR_STK_x with the head set after each state, and they
   carry the room budget as they carry the meter: RHELD (RRL / RRM / RRU None) the whole budget
   rp_RM RP S1 (Z.to_nat (tr_cost MT_rk (rtr cx)) + kr) and the entry's count fact cnt_ok_pk RP (rr_pk (rtr cx)) at
   the current blocks; RDONE (RRU (Some i)) what is left after the last free, rp_RM RP S1 kr.  Image B against the
   image-A twin: no HV4 (image B reads g_wake[1] in wake, W_wake_x.v's HV8 / HWK / HERRS, taken by W_relay_remove.v);
   HH53 / HH54 are B's listing slots of A's HH59 / HH60; RCTX is B's closed singleton. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame W_wake_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x W_wake_c_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
(* route R (the Section wR below): SRrG, and the R contract texts of drain / gestures_end (a Theorem Labs lane) and of
   relay_remove (a Theorem Labs lane) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_relayB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ---- The walk's program counters (B text base 0x82344; AF_fr_relay_remove = 0x1eb8). ---- *)
Definition A_rr_entry : Z := AF_fr_relay_remove.            (* 0x841fc, the entry *)
Definition A_rr_entryP : Z := BASE + A_rr_entry.
Definition A_rr_scan : Z := AF_fr_relay_remove + 0x70.      (* 0x8426c, the scan loop's head *)
Definition A_rr_match : Z := AF_fr_relay_remove + 0xdc.     (* 0x842d8, fd found *)
Definition A_rr_unlock : Z := AF_fr_relay_remove + 0x1c4.   (* 0x843c0, the unlock tail *)

(* The callee-saved registers in their frame slots 0(sp) (s4) .. 40(sp) (ra), sp = the entry sp - 48. *)
Definition RR_SAVED : list (bv 5) := [20%bv; 19%bv; 18%bv; 9%bv; 8%bv; 1%bv].

(* The register images of g_nsrc and g_src: s1 = the auipc at 0x84238 (g_nsrc = s1 - 1304, listing A_HI 53) and
   s4 = the auipc at 0x84248 (g_src = s4 - 1288, listing A_HI 54). *)
Definition RR_HI_NSRC : Z := 1304.
Definition RR_HI_SRC : Z := 1288.

(* the relay's and the output's global cells and errno (HRGP's list): the cells the walk carries across its calls (the
   image-A twin's rr_gcells, verbatim) *)
Definition rr_gcells (B : asyms) (RG : rep_globals) : list (Z * Z) :=
[(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
 (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
 (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
 (as_errno B, as_errno B + 4)].

(* ---- THE GENERIC WALK (route (b), step 3): relay_remove over any allocator relation ARx with its laws, stated as
   W_contract_x.rr_spec_x.  The Section is the image-A twin's (lib/A/W_relay_remove_cx.v at f4cd818e98d) with image
   B's names for image B's objects: HH53 / HH54 (A's HH59 / HH60), IMGC at image B's top 0x5fc000 (W_wake_x.v,
   W_gestures_end.v), no HV4, and WAKE (image B tail-calls wake). ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* route R: the world relation of the Section wR twins below, declared right after ARx so that it is their argument
   right after ARx (a Theorem Labs lane, 23:04Z); no strict text uses it *)
Variable R : world SEGS -> world SEGS -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the allocator rules on the _c form (W_journal.v Section hc; a Theorem Labs lane 21:24Z): one table CTX_AFREE for free and
   free(NULL), which enter the same interceptor pc0.  Image B's relay_remove keeps NO frame pointer: at its free
   (0x8435c, ra 0x84360 = entry + 0x164) s0 holds fd, an integer below alloc_ceiling, so chain_pre's chain is cut by
   the register and the trace is the CLOSED singleton [0x84360] (a Theorem Labs lane 21:32Z; K0's B CTX_AFREE row, lib/B/YCk0.v:19).  The
   kit's B rr_spec_x takes it as its LAST premise `In [pc + 356] CTX_AFREE` (W4's b_facts, a Theorem Labs lane 21:5xZ); RCTX
   below carries it to MATCH's free (no ly_top conjunct: the chain is []). *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'). ---- *)
(* the generic relation's laws and its empty head set (CONVERSION.md (sha256 1015972e02a9; internal record) 1.) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (image B's top, W_wake_x.v's form), a live block's
   size non-negative (BLKN, W_kit_x.v), the owned-low law OWNLOW, the model invariant WFx with its law WFL and the two
   facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC); ASMP / ASF / FFL are the class-0
   fake frame's laws (image B's relay_remove takes none: wake does, W_wake_x.v) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis HG : gx_ok SEGS B (G_RR B RG).
(* the register images of g_nsrc / g_src (the abstract placement does not fix them against the objects; PB_fr on
   AsanUbsan discharges both by vm_compute, as the image-A twin's HH59 / HH60) *)
Hypothesis HH53 : VAL (A_HI 53) = rg_nsrc RG + RR_HI_NSRC.
Hypothesis HH54 : VAL (A_HI 54) = rg_src RG + RR_HI_SRC.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are unowned image bytes (the image-A twin's HRGP / HRGI, verbatim) *)
Hypothesis HRGP : zpairwise_disjoint
[(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
 (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
 (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
 (as_errno B, as_errno B + 4)].
Hypothesis HRGI : forall a,
(rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* no read-only image byte is owned by the runtime: rom_view survives the calls (W_journal_x.v ajournal_gx_rom_view_x) *)
Hypothesis HROMO : rom_out SEGS B (G_RR B RG).
Hypothesis MLAW : ameter_laws MT.
(* the meter does not see a change of the fake-frame state alone (KF-COUNT, the image-A twin's MO_FR): sound, since
   the seat's post state is a set_fs (Reusable/YG01.v stack_malloc_post) and the release is stack_free_state, a set_fs;
   image B meets it at wake's return (W_wake_c_x.v wk_post_x's seat fact S' = set_fs f S) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the runtime entries relay_remove calls, at their SIGMA pcs (image B calls free's interceptor directly, WS_free) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy).
(* the program functions relay_remove calls: drain, gestures_end (the kit's _x specs) and wake (W_wake_c_x.v) *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x8435c with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* B only: wake, tail-called at 0x843e8 (image A inlines it); W_relay_remove.v builds it by W_wake_x.v pb_wake_x *)
Hypothesis WAKE : wk_spec_x B PST ARx RG (BASE + AF_fr_wake).
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* The program statics PST hold no byte the walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x) and no byte of the relay's / output's cells or
   errno (rr_gcells, HRGP's list).  At PST := [] both hold trivially (the image-A twin's PSTR / PSTG, verbatim). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, Exists (fun r => fst r <= a < snd r) (rr_gcells B RG) -> ~ Exists (in_zr a) PST.

(* ---- The callees' journals, lifted to relay_remove's globals: drain's at G_DR, gestures_end's at G_SL and wake's
   at [] are journals at G_RR (W_journal_x.v ajournal_gx_G_mono_x). ---- *)
Lemma rr_G_DR_RR : forall a, inG (G_DR B RG) a -> inG (G_RR B RG) a.
Proof. intros a Ha. unfold G_RR, inG in *. apply Exists_cons_tl. apply Exists_cons_tl. exact Ha. Qed.
Lemma rr_G_SL_RR : forall a, inG (G_SL B RG) a -> inG (G_RR B RG) a.
Proof. intros a Ha. apply rr_G_DR_RR. unfold G_DR, inG in *. apply Exists_cons_tl. exact Ha. Qed.
Lemma rr_lift_DR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_x; [exact rr_G_DR_RR | eassumption]. Qed.
Lemma rr_lift_SL : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_SL B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_x; [exact rr_G_SL_RR | eassumption]. Qed.
Lemma rr_lift_WK : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx [] XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_x; [intros a Ha; exfalso; exact (inG_nil a Ha) | eassumption]. Qed.
(* the room round: a count fact moves along a Permutation of the blocks (the image-A twin's, verbatim) *)
Lemma rr_cnt_perm : forall pk l l', Permutation l l' -> cnt_ok_pk RP pk l -> cnt_ok_pk RP pk l'.
Proof.
intros pk l l' HP HC. apply (cnt_ok_pk_mono RP pk pk l l'); [|exact HC].
intros P. rewrite (ReplyCnt.acnt_perm P _ _ HP). lia.
Qed.

(* ---- The entry context. ----
   One record for everything rr_spec_x quantifies over at the entry (the ghost set rxHp after rxS, the room budget
   rxkr last), so that every segment statement takes one argument and the cut predicates read the entry off it. *)
Record rcx : Type := mkRcx {
  rxregs : bvmap 5 word;
  rxly : alayout; rxS : astate; rxHp : list Z; rxW : world SEGS; rxmem : word -> option byte; rxmd : Model;
  rxch : list (Z * Z * Z);
  rxG0 : Z; rxFD : Z; rxes : list rentry; rxj : nat; rxh : hsrc;
  rxc : ctl; rxO : list byte; rxmx : Z; rxcap : Z; rxout : Z;
  rxrest : list (Z * Z); rxkr : nat }.

Definition rsp0 (cx : rcx) : Z := spZ (rxregs cx).
Definition rN (cx : rcx) : Z := Z.of_nat (length (rxes cx)).
Definition rFP (cx : rcx) : list (Z * Z) := rr_fp (rxG0 cx) (rxFD cx) (rxes cx) (rxh cx) (rxcap cx) (rxout cx).
Definition rtr (cx : rcx) := rr_tr (rxc cx) (rxmx cx) (Z.of_nat (length (rxO cx))) (rxcap cx) (rxFD cx) (rxes cx) (rxh cx).
Definition rnth (cx : rcx) (i : nat) : rentry := nth i (rxes cx) relay_remove_b_c.no_entry.
Definition rPOST (cx : rcx) : world SEGS -> config -> Prop :=
rr_post_x B PST ARx MT RP RG (rxregs cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx)
  (rxG0 cx) (rxFD cx) (rxes cx) (rxj cx) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rxcap cx) (rxout cx) (rxkr cx).

(* RBASE: exactly rr_spec_x's premises at the entry (W_contract_x.v), with the Permutation's `rest` taken from the
   context, the room record (rp_RM at the trace's counting-meter cost plus kr, the count premise at rr_pk) last; the
   caller-context premise is RCTX. *)
Definition RBASE (cx : rcx) : Prop :=
afn_pre_x SEGS B ARx RR_STK_x (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxregs cx) (rxmem cx) (rxmd cx) (rxch cx) /\
rsp0 cx mod 32 = 0 /\ count_cid 0 (frames (rxS cx)) < fs_frames 0 /\ rg_place B RG /\
getr (rxregs cx) 10 = w64 (rxFD cx) /\ - 2 ^ 31 <= rxFD cx < 2 ^ 31 /\
alock_at RG (rxW cx) (rxmem cx) false /\ awake_at RG (rxW cx) (rxmem cx) /\
arelay_at B RG (rxly cx) (rxS cx) (rxW cx) (rxmem cx) (rxG0 cx) (rxes cx) /\
aout_at B RG (rxly cx) (rxS cx) (rxW cx) (rxmem cx) (rxc cx) (rxO cx) (rxmx cx) (Z.of_nat (length (rxO cx)))
  (rxcap cx) (rxout cx) /\
rom_view SEGS (rxW cx) (rxmem cx) /\
(forall i, (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx -> re_eof (rnth cx i) = 0 ->
   dr_src_ok B RG (rxly cx) (rxS cx) (rxW cx) (rxmem cx) (rnth cx i) (rxh cx) (rxj cx)) /\
Permutation (ablocks B (rxly cx) (rxS cx))
  ((rxG0 cx, ATABLE) :: concat (map aentry_blks (rxes cx)) ++
   (if rr_drains (rxFD cx) (rxes cx) then asrc_blks (rxh cx) else []) ++ aout_blks (rxcap cx) (rxout cx) ++ rxrest cx) /\
tr_max (rtr cx) < MMAX /\ blocks_bytes (rxS cx) + tr_peak (rtr cx) <= LIVE_MAX /\
mo_ok MT (rxS cx) (tr_cost MT (rtr cx)) /\
rp_RM RP (rxS cx) (Z.to_nat (tr_cost MT_rk (rtr cx)) + rxkr cx) /\
cnt_ok_pk RP (rr_pk (rtr cx)) (ablocks B (rxly cx) (rxS cx)).

(* RCTX: rr_spec_x's caller-context premise at the entry, read by MATCH's free at 0x8435c (ra 0x84360 = entry +
   0x164): a closed one-entry row (image B's relay_remove keeps no frame pointer) *)
Definition RCTX (cx : rcx) : Prop := In [A_rr_entryP + 356] CTX_AFREE.

(* ---- The frame. ----
   After the saves: sp = the entry sp - 48, the six callee-saved registers in their slots (no fake frame). *)
Definition rr_saved (cx : rcx) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
forall i, (i < 6)%nat ->
val_mem SEGS (arm W1 m1) (rsp0 cx - RR_FRAME + 8 * Z.of_nat i) 8 (bv_unsigned (getr (rxregs cx) (nth i RR_SAVED 0%bv))).

(* The registers every cut after the saves holds: sp, gp, tp, and s5 .. s11 (never written by relay_remove). *)
Definition rregs_base (cx : rcx) (regs1 : bvmap 5 word) : Prop :=
spZ regs1 = rsp0 cx - RR_FRAME /\
getr regs1 3 = getr (rxregs cx) 3 /\ getr regs1 4 = getr (rxregs cx) 4 /\
forall r : bv 5, 21 <= bv_unsigned r <= 27 -> getr regs1 r = getr (rxregs cx) r.
(* ... and, after the lock: s0 = fd, s1 = g_nsrc's register image, s2 = the shadow offset (ld from the GOT at
   0x84228), s4 = g_src's register image *)
Definition rregs_held (cx : rcx) (regs1 : bvmap 5 word) : Prop :=
rregs_base cx regs1 /\
getr regs1 8 = w64 (rxFD cx) /\ getr regs1 9 = w64 (rg_nsrc RG + RR_HI_NSRC) /\
getr regs1 18 = w64 SHADOW_OFF /\ getr regs1 20 = w64 (rg_src RG + RR_HI_SRC).

(* ---- What holds while the lock is held. ----
   RLIVE: the journal from the entry (at G_RR, RR_STK_x, rr_fp; ajournal_gx_x, the head set Hp1 after S1) owning no
   frame, the .rodata view, the presence of image bytes, the saved registers, g_lock held and g_wake[1] = -1 (wake's
   premise at the tail). *)
Definition RLIVE (cx : rcx) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte)
(md1 : Model) (k1 : Z) : Prop :=
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 /\
rom_view SEGS W1 m1 /\ apres_kept B (rxW cx) (rxmem cx) W1 m1 /\
rr_saved cx W1 m1 /\
alock_at RG W1 m1 true /\ awake_at RG W1 m1.

(* RHELD: the lock taken and nothing else changed (the image-A twin's, over this RLIVE); the room round: the whole
   budget (the trace's counting-meter cost plus kr) and the entry's count fact at the current blocks. *)
Definition RHELD (cx : rcx) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte)
(md1 : Model) (k1 : Z) : Prop :=
RLIVE cx ly1 S1 Hp1 W1 m1 md1 k1 /\
arelay_at B RG ly1 S1 W1 m1 (rxG0 cx) (rxes cx) /\
aout_at B RG ly1 S1 W1 m1 (rxc cx) (rxO cx) (rxmx cx) (Z.of_nat (length (rxO cx))) (rxcap cx) (rxout cx) /\
Permutation (ablocks B ly1 S1)
  ((rxG0 cx, ATABLE) :: concat (map aentry_blks (rxes cx)) ++
   (if rr_drains (rxFD cx) (rxes cx) then asrc_blks (rxh cx) else []) ++ aout_blks (rxcap cx) (rxout cx) ++ rxrest cx) /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept (rxW cx) (rxmem cx) W1 m1 a) /\
(forall i, (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx -> re_eof (rnth cx i) = 0 ->
   dr_src_ok B RG ly1 S1 W1 m1 (rnth cx i) (rxh cx) (rxj cx)) /\
mo_le MT (rxS cx) S1 0 /\ blocks_bytes S1 + tr_peak (rtr cx) <= LIVE_MAX /\
rp_RM RP S1 (Z.to_nat (tr_cost MT_rk (rtr cx)) + rxkr cx) /\
cnt_ok_pk RP (rr_pk (rtr cx)) (ablocks B ly1 S1).

(* RDONE: entry i (the one with fd) handled (the image-A twin's, over this RLIVE); the room round: what rr_post_x
   passes on, kr. *)
Definition RDONE (cx : rcx) (i : nat) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS)
(m1 : word -> option byte) (md1 : Model) (k1 : Z) : Prop :=
RLIVE cx ly1 S1 Hp1 W1 m1 md1 k1 /\
(i < length (rxes cx))%nat /\ re_fd (rnth cx i) = rxFD cx /\
mo_le MT (rxS cx) S1 (tr_cost MT (rtr cx)) /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
   (rr_drains (rxFD cx) (rxes cx) = true ->
    ~ (rg_s RG + ASRC * Z.of_nat (rxj cx) <= a < rg_s RG + ASRC * Z.of_nat (rxj cx) + ASRC)) ->
   abyte_kept (rxW cx) (rxmem cx) W1 m1 a) /\
rr_found B RG (rxly cx) (rxS cx) (rxW cx) (rxmem cx) ly1 S1 W1 m1
  (rxG0 cx) (rxes cx) i (rxj cx) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rxcap cx) (rxout cx) /\
rp_RM RP S1 (rxkr cx).

(* ---- The cut predicates. ---- *)

(* RRL k (0x8426c): the scan loop's head at entry k < |es| of the table g_src = G0, none of entries 0 .. k-1 has fd.
   a1 = G0 (loaded once, 0x8424c), a2 = 56 |es| (0x84250-0x84258), a3 = 1 (G0 <> 0, 0x8425c), a4 = 1 (G0 <> 0 and
   G0 mod 8 = 0, 0x84260-0x84268), s3 = 56 k. *)
Definition RRL (cx : rcx) (k : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1,
c1 = cfg_at SEGS (BASE + A_rr_scan) regs1 m1 md1 /\
rregs_held cx regs1 /\
getr regs1 11 = w64 (rxG0 cx) /\ getr regs1 12 = w64 (AENT * rN cx) /\
getr regs1 13 = w64 1 /\ getr regs1 14 = w64 1 /\
getr regs1 19 = w64 (AENT * Z.of_nat k) /\
0 <= rxFD cx /\ (k < length (rxes cx))%nat /\
(forall i, (i < k)%nat -> re_fd (rnth cx i) <> rxFD cx) /\
RHELD cx ly1 S1 Hp1 W1 m1 md1 k1.

(* RRM i (0x842d8): entry i has fd (the first that has it; arelay_at's NoDup makes it the only one).
   a0 = G0 + 56 i, s3 = 56 i. *)
Definition RRM (cx : rcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1,
c1 = cfg_at SEGS (BASE + A_rr_match) regs1 m1 md1 /\
rregs_held cx regs1 /\
getr regs1 10 = w64 (rxG0 cx + AENT * Z.of_nat i) /\ getr regs1 19 = w64 (AENT * Z.of_nat i) /\
0 <= rxFD cx /\ (i < length (rxes cx))%nat /\ re_fd (rnth cx i) = rxFD cx /\
RHELD cx ly1 S1 Hp1 W1 m1 md1 k1.

(* RRU oi (0x843c0): the unlock tail.  None: no entry has fd and nothing changed; Some i: entry i handled (RDONE).
   Only the base registers are live here (the epilogue reloads s0 .. s4 and ra from their slots). *)
Definition RRU (cx : rcx) (oi : option nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1,
c1 = cfg_at SEGS (BASE + A_rr_unlock) regs1 m1 md1 /\
rregs_base cx regs1 /\ 0 <= rxFD cx /\
match oi with
| None => RHELD cx ly1 S1 Hp1 W1 m1 md1 k1 /\ (forall e, In e (rxes cx) -> re_fd e <> rxFD cx)
| Some i => RDONE cx i ly1 S1 Hp1 W1 m1 md1 k1
end.

(* ---- The segment statements. ---- *)

(* PRO: the six saves, the fd < 0 test 0x84218 (fd < 0: the epilogue 0x842b8 and the return, in this segment), the
   GOT load of the shadow base (0x84220-0x84228), pthread_mutex_lock (g_lock) 0x84234, g_nsrc <= 0 0x84240 (-> RRU
   None) and the scan's setup 0x84244-0x84268 (-> RRL 0). *)
Definition rr_pro_stmt : Prop :=
forall cx,
RBASE cx ->
(forall W2 c2, RRL cx 0 W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
(forall W2 c2, RRU cx None W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
SRr SEGS (rxW cx) (cfg_at SEGS A_rr_entryP (rxregs cx) (rxmem cx) (rxmd cx)) (rPOST cx).

(* SCAN: one step of the scan loop 0x8426c-0x842a4 at entry k: a0 = G0 + 56 k, its traps (0x84270 overflow,
   0x8427c null consistency, 0x84280 the flag a4: NOT taken), the shadow check of entry k's fd field (0x8428c lb,
   0x84290 bnez, 0x842a8-0x842b0: the report call 0x842b4 is NOT taken), the fd load 0x84294, the match test 0x84298
   (-> RRM k), and the step 0x8429c-0x842a4 (s3 += 56; the last entry -> RRU None, else -> RRL (S k)).  No call, no
   store: memory, journal and world are unchanged. *)
Definition rr_scan_stmt : Prop :=
forall cx k W1 c1,
RBASE cx -> RRL cx k W1 c1 ->
(forall W2 c2, RRL cx (S k) W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
(forall W2 c2, RRM cx k W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
(forall W2 c2, RRU cx None W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
SRr SEGS W1 c1 (rPOST cx).

(* SCANS: the scan loop, by induction on |es| - k. *)
Definition rr_scans_stmt : Prop :=
rr_scan_stmt ->
forall cx k W1 c1,
RBASE cx -> RRL cx k W1 c1 ->
(forall i W2 c2, RRM cx i W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
(forall W2 c2, RRU cx None W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
SRr SEGS W1 c1 (rPOST cx).

(* MATCH: RRM i 0x842d8 -> the shadow check of the eof field (0x842d8-0x842e8, 0x843f0-0x84400 not taken), drain
   when open (0x842f4), g_src reloaded and checked (0x842f8-0x84310), gestures_end (0x84314), g_src reloaded and
   checked (0x84318-0x84340), the shadow check of the buf field (0x84344-0x84354, 0x84404 not taken), free (s->buf)
   (0x8435c), g_src reloaded and checked, g_nsrc -= 1 with its int32 check (0x8437c-0x8439c) and g_src[i] =
   g_src[g_nsrc] by __asan_memcpy (0x843bc; onto itself when i is the last entry) -> RRU (Some i). *)
Definition rr_match_stmt : Prop :=
forall cx i W1 c1,
RBASE cx -> RCTX cx -> RRM cx i W1 c1 ->
(forall W2 c2, RRU cx (Some i) W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
SRr SEGS W1 c1 (rPOST cx).

(* TAIL: RRU oi 0x843c0 -> pthread_mutex_unlock (g_lock) (0x843c8), the epilogue 0x843cc-0x843e4 and the tail call
   `j wake` 0x843e8 (WAKE: wake returns to relay_remove's caller with g_wake[1] still -1) -> rr_post. *)
Definition rr_tail_stmt : Prop :=
forall cx oi W1 c1,
RBASE cx -> RRU cx oi W1 c1 ->
SRr SEGS W1 c1 (rPOST cx).

(* The walk: the segments give relay_remove's generic contract (SCAN is passed to SCANS).  rr_spec_x takes
   `In [pc + 356] CTX_AFREE` LAST; W_rr_all.v passes it as RCTX. *)
Definition rr_all_stmt : Prop :=
rr_pro_stmt -> rr_scan_stmt -> rr_scans_stmt -> rr_match_stmt -> rr_tail_stmt ->
rr_spec_x B PST ARx MT RP MMAX RG CTX_AFREE A_rr_entryP.

(* ---- ROUTE R (a Theorem Labs lane's route-R lift crew, group G8b-relayrm-B; G4's form, lib/B/W_bx_order_x.v): the segment
   interface at a world relation R.  R / R_refl / R_trans / WLE_R, RO / RO_ARx and the R free rules are
   lib/B/W_gestures_end.v's Section wR texts; drain and gestures_end at R are a Theorem Labs lane's W_contract_xR.v dr_spec_xR /
   gse_spec_xR; relay_remove's post and contract at R are a Theorem Labs lane's W_contract_xR_relayB.v rr_post_xR / rr_spec_xR.
   Against the strict texts only these change: ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R,
   rr_post_x -> rr_post_xR .. R, rr_spec_x -> rr_spec_xR .. R, and each cut predicate or statement that carries one
   of them -> its _xR twin.  RBASE and RCTX (the entry's premises: no journal, no step relation) stay strict.  At
   R := wle each twin IS its strict text (the X_wle lemmas after the Section, by conversion); a strict cut predicate
   gives its R twin at every R that contains wle (the X_xR_of_x lemmas, from WLE_R).
   Census rows (a Theorem Labs lane's G8b-relayrm-B.tsv (sha256 4c7c7e01243b; internal record)) -> twins: :198 AFREE -> AFREE_R, :202 DRAIN -> DRAIN_R,
   :203 GSE -> GSE_R, :205 AFREEN -> AFREEN_R, :225 rr_lift_DR -> rr_lift_DR_xR, :229 rr_lift_SL -> rr_lift_SL_xR,
   :233 rr_lift_WK -> rr_lift_WK_xR, :260 rPOST -> rPOST_xR, :312 RLIVE -> RLIVE_xR, :322 RHELD -> RHELD_xR,
   :339 RDONE -> RDONE_xR, :380 RRU -> RRU_xR (RRL / RRM, no rows, -> RRL_xR / RRM_xR), :394 rr_pro_stmt,
   :406 rr_scan_stmt, :415 rr_scans_stmt, :428 rr_match_stmt, :436 rr_tail_stmt, :443 rr_all_stmt -> their _xR. ---- *)
Section wR.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* the R free rules' call-boundary premise RO, from the journal's ARx at the call state (part 3c removed their memnorm
   premise) *)
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
(* :198 AFREE at R *)
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* :202 DRAIN, :203 GSE at R (W_contract_xR.v) *)
Hypothesis DRAIN_R : dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE_R : gse_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* :205 AFREEN at R *)
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.

(* :225 rr_lift_DR, :229 rr_lift_SL, :233 rr_lift_WK at R (W_journal_x.v ajournal_gx_G_mono_xR) *)
Lemma rr_lift_DR_xR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_xR; [exact rr_G_DR_RR | eassumption]. Qed.
Lemma rr_lift_SL_xR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_SL B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_xR; [exact rr_G_SL_RR | eassumption]. Qed.
Lemma rr_lift_WK_xR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R [] XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_xR; [intros a Ha; exfalso; exact (inG_nil a Ha) | eassumption]. Qed.

(* :260 rPOST at R: rr_post_xR (W_contract_xR_relayB.v) *)
Definition rPOST_xR (cx : rcx) : world SEGS -> config -> Prop :=
rr_post_xR B PST ARx R MT RP RG (rxregs cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx)
  (rxG0 cx) (rxFD cx) (rxes cx) (rxj cx) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rxcap cx) (rxout cx) (rxkr cx).

(* :312 RLIVE at R *)
Definition RLIVE_xR (cx : rcx) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte)
(md1 : Model) (k1 : Z) : Prop :=
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 /\
rom_view SEGS W1 m1 /\ apres_kept B (rxW cx) (rxmem cx) W1 m1 /\
rr_saved cx W1 m1 /\
alock_at RG W1 m1 true /\ awake_at RG W1 m1.

(* :322 RHELD at R *)
Definition RHELD_xR (cx : rcx) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte)
(md1 : Model) (k1 : Z) : Prop :=
RLIVE_xR cx ly1 S1 Hp1 W1 m1 md1 k1 /\
arelay_at B RG ly1 S1 W1 m1 (rxG0 cx) (rxes cx) /\
aout_at B RG ly1 S1 W1 m1 (rxc cx) (rxO cx) (rxmx cx) (Z.of_nat (length (rxO cx))) (rxcap cx) (rxout cx) /\
Permutation (ablocks B ly1 S1)
  ((rxG0 cx, ATABLE) :: concat (map aentry_blks (rxes cx)) ++
   (if rr_drains (rxFD cx) (rxes cx) then asrc_blks (rxh cx) else []) ++ aout_blks (rxcap cx) (rxout cx) ++ rxrest cx) /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept (rxW cx) (rxmem cx) W1 m1 a) /\
(forall i, (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx -> re_eof (rnth cx i) = 0 ->
   dr_src_ok B RG ly1 S1 W1 m1 (rnth cx i) (rxh cx) (rxj cx)) /\
mo_le MT (rxS cx) S1 0 /\ blocks_bytes S1 + tr_peak (rtr cx) <= LIVE_MAX /\
rp_RM RP S1 (Z.to_nat (tr_cost MT_rk (rtr cx)) + rxkr cx) /\
cnt_ok_pk RP (rr_pk (rtr cx)) (ablocks B ly1 S1).

(* :339 RDONE at R *)
Definition RDONE_xR (cx : rcx) (i : nat) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS)
(m1 : word -> option byte) (md1 : Model) (k1 : Z) : Prop :=
RLIVE_xR cx ly1 S1 Hp1 W1 m1 md1 k1 /\
(i < length (rxes cx))%nat /\ re_fd (rnth cx i) = rxFD cx /\
mo_le MT (rxS cx) S1 (tr_cost MT (rtr cx)) /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
   (rr_drains (rxFD cx) (rxes cx) = true ->
    ~ (rg_s RG + ASRC * Z.of_nat (rxj cx) <= a < rg_s RG + ASRC * Z.of_nat (rxj cx) + ASRC)) ->
   abyte_kept (rxW cx) (rxmem cx) W1 m1 a) /\
rr_found B RG (rxly cx) (rxS cx) (rxW cx) (rxmem cx) ly1 S1 W1 m1
  (rxG0 cx) (rxes cx) i (rxj cx) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rxcap cx) (rxout cx) /\
rp_RM RP S1 (rxkr cx).

(* RRL at R (no census row; it carries RHELD) *)
Definition RRL_xR (cx : rcx) (k : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1,
c1 = cfg_at SEGS (BASE + A_rr_scan) regs1 m1 md1 /\
rregs_held cx regs1 /\
getr regs1 11 = w64 (rxG0 cx) /\ getr regs1 12 = w64 (AENT * rN cx) /\
getr regs1 13 = w64 1 /\ getr regs1 14 = w64 1 /\
getr regs1 19 = w64 (AENT * Z.of_nat k) /\
0 <= rxFD cx /\ (k < length (rxes cx))%nat /\
(forall i, (i < k)%nat -> re_fd (rnth cx i) <> rxFD cx) /\
RHELD_xR cx ly1 S1 Hp1 W1 m1 md1 k1.

(* RRM at R (no census row; it carries RHELD) *)
Definition RRM_xR (cx : rcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1,
c1 = cfg_at SEGS (BASE + A_rr_match) regs1 m1 md1 /\
rregs_held cx regs1 /\
getr regs1 10 = w64 (rxG0 cx + AENT * Z.of_nat i) /\ getr regs1 19 = w64 (AENT * Z.of_nat i) /\
0 <= rxFD cx /\ (i < length (rxes cx))%nat /\ re_fd (rnth cx i) = rxFD cx /\
RHELD_xR cx ly1 S1 Hp1 W1 m1 md1 k1.

(* :380 RRU at R *)
Definition RRU_xR (cx : rcx) (oi : option nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1,
c1 = cfg_at SEGS (BASE + A_rr_unlock) regs1 m1 md1 /\
rregs_base cx regs1 /\ 0 <= rxFD cx /\
match oi with
| None => RHELD_xR cx ly1 S1 Hp1 W1 m1 md1 k1 /\ (forall e, In e (rxes cx) -> re_fd e <> rxFD cx)
| Some i => RDONE_xR cx i ly1 S1 Hp1 W1 m1 md1 k1
end.

(* :394 PRO at R *)
Definition rr_pro_stmt_xR : Prop :=
forall cx,
RBASE cx ->
(forall W2 c2, RRL_xR cx 0 W2 c2 -> SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
(forall W2 c2, RRU_xR cx None W2 c2 -> SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
SRrG SEGS R (rxW cx) (cfg_at SEGS A_rr_entryP (rxregs cx) (rxmem cx) (rxmd cx)) (rPOST_xR cx).

(* :406 SCAN at R *)
Definition rr_scan_stmt_xR : Prop :=
forall cx k W1 c1,
RBASE cx -> RRL_xR cx k W1 c1 ->
(forall W2 c2, RRL_xR cx (S k) W2 c2 -> SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
(forall W2 c2, RRM_xR cx k W2 c2 -> SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
(forall W2 c2, RRU_xR cx None W2 c2 -> SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
SRrG SEGS R W1 c1 (rPOST_xR cx).

(* :415 SCANS at R *)
Definition rr_scans_stmt_xR : Prop :=
rr_scan_stmt_xR ->
forall cx k W1 c1,
RBASE cx -> RRL_xR cx k W1 c1 ->
(forall i W2 c2, RRM_xR cx i W2 c2 -> SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
(forall W2 c2, RRU_xR cx None W2 c2 -> SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
SRrG SEGS R W1 c1 (rPOST_xR cx).

(* :428 MATCH at R *)
Definition rr_match_stmt_xR : Prop :=
forall cx i W1 c1,
RBASE cx -> RCTX cx -> RRM_xR cx i W1 c1 ->
(forall W2 c2, RRU_xR cx (Some i) W2 c2 -> SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
SRrG SEGS R W1 c1 (rPOST_xR cx).

(* :436 TAIL at R *)
Definition rr_tail_stmt_xR : Prop :=
forall cx oi W1 c1,
RBASE cx -> RRU_xR cx oi W1 c1 ->
SRrG SEGS R W1 c1 (rPOST_xR cx).

(* :443 the walk at R: the segments at R give relay_remove's contract at R (W_contract_xR_relayB.v rr_spec_xR) *)
Definition rr_all_stmt_xR : Prop :=
rr_pro_stmt_xR -> rr_scan_stmt_xR -> rr_scans_stmt_xR -> rr_match_stmt_xR -> rr_tail_stmt_xR ->
rr_spec_xR B PST ARx R MT RP MMAX RG CTX_AFREE A_rr_entryP.

(* a strict cut predicate (and the strict post) gives its R twin, at every R that contains wle *)
Lemma rPOST_xR_of_x : forall cx W' c', rPOST cx W' c' -> rPOST_xR cx W' c'.
Proof.
intros cx W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', k. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma RLIVE_xR_of_x : forall cx ly1 S1 Hp1 W1 m1 md1 k1,
RLIVE cx ly1 S1 Hp1 W1 m1 md1 k1 -> RLIVE_xR cx ly1 S1 Hp1 W1 m1 md1 k1.
Proof.
intros cx ly1 S1 Hp1 W1 m1 md1 k1 (HJ & REST). split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma RHELD_xR_of_x : forall cx ly1 S1 Hp1 W1 m1 md1 k1,
RHELD cx ly1 S1 Hp1 W1 m1 md1 k1 -> RHELD_xR cx ly1 S1 Hp1 W1 m1 md1 k1.
Proof.
intros cx ly1 S1 Hp1 W1 m1 md1 k1 (HL & REST). split; [exact (RLIVE_xR_of_x _ _ _ _ _ _ _ _ HL) | exact REST].
Qed.
Lemma RDONE_xR_of_x : forall cx i ly1 S1 Hp1 W1 m1 md1 k1,
RDONE cx i ly1 S1 Hp1 W1 m1 md1 k1 -> RDONE_xR cx i ly1 S1 Hp1 W1 m1 md1 k1.
Proof.
intros cx i ly1 S1 Hp1 W1 m1 md1 k1 (HL & REST). split; [exact (RLIVE_xR_of_x _ _ _ _ _ _ _ _ HL) | exact REST].
Qed.
Lemma RRL_xR_of_x : forall cx k W1 c1, RRL cx k W1 c1 -> RRL_xR cx k W1 c1.
Proof.
intros cx k W1 c1 (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & H).
exists regs1, ly1, S1, Hp1, m1, md1, k1.
repeat match type of H with ?A /\ ?B => let Ha := fresh "Ha" in destruct H as [Ha H]; split; [exact Ha|] end.
exact (RHELD_xR_of_x _ _ _ _ _ _ _ _ H).
Qed.
Lemma RRM_xR_of_x : forall cx i W1 c1, RRM cx i W1 c1 -> RRM_xR cx i W1 c1.
Proof.
intros cx i W1 c1 (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & H).
exists regs1, ly1, S1, Hp1, m1, md1, k1.
repeat match type of H with ?A /\ ?B => let Ha := fresh "Ha" in destruct H as [Ha H]; split; [exact Ha|] end.
exact (RHELD_xR_of_x _ _ _ _ _ _ _ _ H).
Qed.
Lemma RRU_xR_of_x : forall cx oi W1 c1, RRU cx oi W1 c1 -> RRU_xR cx oi W1 c1.
Proof.
intros cx oi W1 c1 (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & Hc & Hr & HFD & H).
exists regs1, ly1, S1, Hp1, m1, md1, k1. split; [exact Hc|]. split; [exact Hr|]. split; [exact HFD|].
destruct oi as [i|].
- exact (RDONE_xR_of_x _ _ _ _ _ _ _ _ _ H).
- destruct H as [HH Hn]. split; [exact (RHELD_xR_of_x _ _ _ _ _ _ _ _ HH) | exact Hn].
Qed.
End wR.


End c.

(* At R := wle each R twin is its strict text, by conversion (route R's rule: one text); R is the twins' argument
   right after ARx. *)
Section wle.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Variable CTX_AFREE : list (list Z).
Lemma rPOST_wle : rPOST B PST ARx MT RP RG = rPOST_xR B PST ARx (@wle SEGS) MT RP RG.
Proof. reflexivity. Qed.
Lemma RLIVE_wle : RLIVE B PST ARx RG = RLIVE_xR B PST ARx (@wle SEGS) RG.
Proof. reflexivity. Qed.
Lemma RHELD_wle : RHELD B PST ARx MT RP RG = RHELD_xR B PST ARx (@wle SEGS) MT RP RG.
Proof. reflexivity. Qed.
Lemma RDONE_wle : RDONE B PST ARx MT RP RG = RDONE_xR B PST ARx (@wle SEGS) MT RP RG.
Proof. reflexivity. Qed.
Lemma RRL_wle : RRL B PST ARx MT RP RG = RRL_xR B PST ARx (@wle SEGS) MT RP RG.
Proof. reflexivity. Qed.
Lemma RRM_wle : RRM B PST ARx MT RP RG = RRM_xR B PST ARx (@wle SEGS) MT RP RG.
Proof. reflexivity. Qed.
Lemma RRU_wle : RRU B PST ARx MT RP RG = RRU_xR B PST ARx (@wle SEGS) MT RP RG.
Proof. reflexivity. Qed.
Lemma rr_pro_stmt_wle : rr_pro_stmt B PST ARx MT RP MMAX RG = rr_pro_stmt_xR B PST ARx (@wle SEGS) MT RP MMAX RG.
Proof. reflexivity. Qed.
Lemma rr_scan_stmt_wle : rr_scan_stmt B PST ARx MT RP MMAX RG = rr_scan_stmt_xR B PST ARx (@wle SEGS) MT RP MMAX RG.
Proof. reflexivity. Qed.
Lemma rr_scans_stmt_wle : rr_scans_stmt B PST ARx MT RP MMAX RG = rr_scans_stmt_xR B PST ARx (@wle SEGS) MT RP MMAX RG.
Proof. reflexivity. Qed.
Lemma rr_match_stmt_wle : rr_match_stmt B PST ARx MT RP MMAX RG CTX_AFREE =
  rr_match_stmt_xR B PST ARx (@wle SEGS) MT RP MMAX RG CTX_AFREE.
Proof. reflexivity. Qed.
Lemma rr_tail_stmt_wle : rr_tail_stmt B PST ARx MT RP MMAX RG = rr_tail_stmt_xR B PST ARx (@wle SEGS) MT RP MMAX RG.
Proof. reflexivity. Qed.
Lemma rr_all_stmt_wle : rr_all_stmt B PST ARx MT RP MMAX RG CTX_AFREE =
  rr_all_stmt_xR B PST ARx (@wle SEGS) MT RP MMAX RG CTX_AFREE.
Proof. reflexivity. Qed.
End wle.
End b.
End a.
