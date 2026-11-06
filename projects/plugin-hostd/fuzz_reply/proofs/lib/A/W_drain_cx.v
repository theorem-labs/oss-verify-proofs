(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the SEGMENT INTERFACE of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x830dc .. 0x83de4, 834 instructions), in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites), lib/A/AC8b.v (a loop over concrete cut states) and
   lib/A/ACfj.v (segments joined at cut points), and of this lane's W_send_line_cx.v.
   Nothing is proved here: the file fixes the Section hypotheses, the entry context, the cut predicates over
   concrete machine states and the statement of every segment, so that the segments are proved in parallel.

   drain (s) is relay.c:171-224 with gesture_seen (relay.c:89-121) inlined and the harness's fuzz_recv
   (fuzz_reply.c:240-276) with source_of, reference_feed (217-238) and list_drop (153-158) inlined.
   Its contract is W_contract.v Section s7: dr_spec B MT MMAX RG (BASE + AF_fr_drain), post dr_post.
   The functional half is the plain proof's (lib/Prog/drain_b_c.v drain_run and lib/A/W_drain_model.v, the copy
   of lib/Prog/drain_b.v:22-336 of its pure round model); the memory half is W_journal.v's ajournal_gx at
   G_DR and the allocator's live-state meter MT.

   CUT POINTS (eight shared predicates; the plain proof's are drain_b.v DI/DRB/DRE/DLL/DLN/DLR/DGS):
     DI    0x831f8  the outer loop's head (for (;;)), in the round state s
     DEND  0x83bbc  no pending text: the closed / EAGAIN tail
     DRB   0x8347c  reference_feed's byte loop, after k of the n bytes
     DE    0x835ac  the byte loop left: the harness side of the round done, the drop and the lines to come
     DLL   0x836bc  the line [p, q) found in the relay's buffer
     DGS   0x837c8  gesture_seen's held-array search, for a begin or an end
     DLN   0x836f4  the line done: on to the next
     DLR   0x83a4c  no further line: the rest of the buffer moved down
   and the two ends: the eof store 0x83b64 and the epilogue 0x83b80 (dr_epi_stmt, generic as W_send_line_cx.v's
   sl_epi).  The byte loop gets its own cut (DRB) because it is a loop with a program call (list_push) and needs
   its own induction, exactly like the line loop; without it the segment from DI would be a third of the walk.

   THE MODEL.  A round's requests are the plain model's trace (Prog/RelayRunT.v rev over sptr).  The walk never
   reads a trace address, only the sizes, through the meter; so every cut predicate quantifies the base and the
   addresses (jb, a) existentially and keeps three facts about what is still to come: the requests `tl`, that the
   rounds from here leave drain's final state (dlater), and the budget (dbud: what the meter has already spent,
   what the rest costs, the live bytes and the largest request).

   STATEMENT GAPS (facts the machine has that the first text lacked; each found at a prover's unprovable goal, each
   fixed by stating the fact, never by weakening; lane notes NOTES.md (sha256 7134ee3e0e22; internal record)):
   - dr_all / dr_outer took composition statements nothing could feed (a Theorem Labs lane, DrAll): *_concl (7cbd5dbb9bf).
   - dr_top's EINTR re-entry unguarded, OUTER had no measure (DrOuter): ds_eintr guard (7cbd5dbb9bf).
   - DRB allowed k = dnum s1 though the byte loop is a do-while (a Theorem Labs lane): k < dnum s1 (2e0fc283c2c).
   - HV9 / HV12 / HSM (DrPro), HROMO (DrLinea), HGO (GsFree): placement / off-static facts of the header.
   - dlit_at's hull visibility (a Theorem Labs lane, LINEB: ASTRNCMP / ASTRCMP's achecked premise needs
     shadow_hull_vis of the literal at 0x83768 / 0x837a8 / 0x837c0; azs gives range_addressable only, and no AR law
     covers image shadow).  Counter-case: an image whose literal lies in a zero-shadow range but whose 64-byte hull
     reaches an unmapped shadow byte satisfies the old dlit_at.
   - dlit_at's azs conjunct was FALSE for all three literals (measured against AF0m's Tfib_zero_shadow: an ASan
     global literal has a partial last granule and a redzone; .str.5's second granule is 06, .str.6 / .str.7's first
     are 06 / 04).  dlit_at now states the one ashp (W_shadow_pin.v: range_addressable over exactly the literal's
     bytes plus the shadow hull, in every AR state - a theorem of AR's const pins, not an envelope); the string
     sites need exactly that.  Only dr_lineb closed through the false conjunct; it now takes ashp. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The trace type of the plain model (Prog/RelayRunF.v trF / adrF), named here without importing RelayRunF
   (whose ContractT chain redefines getr / mkst). *)
#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ---- The walk's program counters (listing slot = (addr - 0x822ec) / 4; AF_fr_drain = 0xdf0). ---- *)
Definition A_drain : Z := AF_fr_drain.                (* 0x830dc, the entry *)
Definition A_drainP : Z := BASE + A_drain.
Definition A_dr_top : Z := AF_fr_drain + 0x11c.       (* 0x831f8, the outer loop's head *)
Definition A_dr_feed : Z := AF_fr_drain + 0x3a0.      (* 0x8347c, reference_feed's byte loop *)
Definition A_dr_fed : Z := AF_fr_drain + 0x4d0.       (* 0x835ac, the byte loop left *)
Definition A_dr_line : Z := AF_fr_drain + 0x5e0.      (* 0x836bc, the line loop's head *)
Definition A_dr_next : Z := AF_fr_drain + 0x618.      (* 0x836f4, on to the next line *)
Definition A_dr_seen : Z := AF_fr_drain + 0x6ec.      (* 0x837c8, gesture_seen's held search *)
Definition A_dr_rest : Z := AF_fr_drain + 0x970.      (* 0x83a4c, no further line *)
Definition A_dr_end : Z := AF_fr_drain + 0xae0.       (* 0x83bbc, no pending text: closed / EAGAIN *)
Definition A_dr_eof : Z := AF_fr_drain + 0xa88.       (* 0x83b64, s->eof = 1 *)
Definition A_dr_epi : Z := AF_fr_drain + 0xaa4.       (* 0x83b80, the epilogue *)

(* The callee-saved registers in their frame slots 232(sp) (s11) .. 328(sp) (ra). *)
Definition DR_SAVED : list (bv 5) :=
[27%bv; 26%bv; 25%bv; 24%bv; 23%bv; 22%bv; 21%bv; 20%bv; 19%bv; 18%bv; 9%bv; 8%bv; 1%bv].

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the instance's laws *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
(* the walk's globals are .data / .bss cells, never read-only image bytes (the pinned placement decides it) *)
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
(* a ROM byte survives a callee's journal (W_journal.v rom_out / ajournal_gx_rom_view): it is not a walk global,
   errno or the sink's overflow head, and if it is an allocator static it is pinned as an AR const cell
   (rom_pinned; W1 45a3cc9bdd0).  The instance discharges it at the pinned placement by vm_compute. *)
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
(* aout_at's three read-only cells are program globals off the allocator's statics, so an allocator or program
   call keeps them (found by GsFree at free #2: they are not in G_DR; send_line's W_send_line_cx.v HGO) *)
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* the runtime entries drain calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v) *)
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
(* memchr: the shared general text (dis-7's amemchr_realizesM, lib/Rt/MemchrDef.v; proved on our image by R3 as
   memchr_icpt_realizesM): both drain sites scan inside one live block's requested size for all n bytes.
   Its constant window is the musl memchr's masks at 0x10350 .. 0x10370, read-only image bytes (HCROM). *)
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
(* the allocator's site rules (W_journal.v), at the trampolines the program calls *)
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
(* The granule-tail fact a key's strlen needs (the rest of a live block's last 8-byte granule is mapped) is NOT a
   hypothesis: it is W_alloc_tail.v's alloc_tail, a theorem of AR for every B (a Theorem Labs lane).  Segment files that still
   carry `Hypothesis ALLOC_TAIL` take it as a premise, and W_drain_pb.v supplies it from alloc_tail. *)
(* the callees drain calls as a program: send_line (W7) and list_push (W2, in its G-generic form; drain
   instantiates it at list_push's own globals, the 16 bytes of h->expected at HA + 64, and lifts the callee's
   journal to G_DR with ajournal_gx_G_mono) *)
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
(* instance facts: errno is tp - 164 (W_sites.v aerrno_realizes) and its 4 bytes have zero shadow *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
(* errno's 4 bytes are writable image bytes in the segments' own view (a .bss cell of the RW LOAD), so aout_at's
   errno cell stays writable across an allocator call whatever the call leaves present (the allocator rules keep
   errno's view but exclude it from presence; found by DropWhole at free #1).  Decided at the pinned placement. *)
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
(* the 4 * 96 bytes of g_s are a zero-shadow range of the image (a plain global, no redzone between the slots) *)
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
(* placement: g_s is reached by PAddHi (A_OBJ 22), so no rebase is needed for it *)
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
(* the string literals of gesture_seen, in .rodata: their bytes (as the image holds them), and their exact bytes
   addressable with a visible shadow hull in every allocator state (ashp; the string sites' achecked premise).
   .str.5 "param_gesture" (A_OBJ 21, 0x20f20, 13 bytes + NUL), .str.6 "begin" (A_OBJ 23, 0x20f40),
   .str.7 "end" (A_OBJ 24, 0x20f60).  The bytes are stated against the image, and `rom_view` (a premise of
   dr_spec, carried by the cut predicates) turns them into what the walk reads.  The instance discharges ashp by
   RomOutPlace's ashp_gesture_14_fr / ashp_begin_6_fr / ashp_end_4_fr (W_shadow_pin_fr.v). *)
Definition dlit_at (i : nat) (l : list Z) : Prop :=
(forall k, (k < length l)%nat ->
   seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ i) + Z.of_nat k)) = option_map (Z_to_bv 8) (nth_error l k)) /\
(forall x, VAL (A_OBJ i) <= x < VAL (A_OBJ i) + Z.of_nat (length l) -> YG0d.in_rom SEGS x) /\
ashp B (VAL (A_OBJ i)) (Z.of_nat (length l)).
Hypothesis HLIT5 : dlit_at 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at 24 (W_END ++ [0]).
(* placement: the cells drain reads or writes are pairwise disjoint ((lo, hi) extents, as extent_of_region makes
   them; the pinned placement decides it by vm_compute).  G_DR's cells are g_s (4 * 96 bytes), the six of G_SL
   and errno; the runtime's two static cells (the GOT slot of the shadow base and the cell) are read, never
   written; the three literals are read-only. *)
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
(* g_s lies in the image band (the walk computes shadow addresses of its fields) *)
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
(* the instance's request bound: the largest request drain makes is the expected list's vector, 32 * cap bytes
   with cap < 2 ^ 26; MMAX <= 2 ^ 30 gives list_push's growth premise `lp_vbytes l < MMAX` directly *)
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
(* placement of the three output cells aout_at reads that are not in G_DR's g_s range (the facts W_send_line_entry.v
   states, HV9 / HV12 / HSM): a segment that stores to its frame moves aout_at across the store with them. *)
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- `amem_range x 8`, which every string site takes (W_sites.v, W6 0dd2925324a). ----
   Where it comes from at drain's four kinds of string argument:
   - a line in the relay's buffer (strrchr 0x83750, strncmp 0x83768, strcmp 0x837a8 / 0x837c0, strncmp 0x83864):
     the buffer is a live block (aentry_okx's `In (re_buf e, re_cap e) (ablocks ...)`), and the argument lies
     in it or one byte past it, so amem_range_near_block applies.  The eight bytes need NOT fit in the block:
     the band's ceiling (ASAN_CEIL <= 0x7fffff800000) leaves 8 MiB below kHighMemEnd.
   - a held key (strlen 0x83850, strncmp 0x83864): aentry_okx's Forall gives its block.
   - a text of the harness's lists: asrc_at gives its block.
   - a string literal (strncmp 0x83768, strcmp 0x837a8 / 0x837c0): amem_range_img from HLIT*'s extent. *)
Lemma amem_range_of_in_app : forall a n, in_app a n -> amem_range a n.
Proof.
intros a n (H0 & [H | [H1 H2]]); pose proof (@ASAN_CEIL_range rc) as (Hc & _);
unfold amem_range, in_app, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
[left; lia | right; lia].
Qed.
Lemma amem_range_near_block : forall ly S W mem md q n a,
AR SEGS B ly S W mem md -> In (q, n) (ablocks B ly S) -> q <= a -> a <= q + req_size n -> amem_range a 8.
Proof.
intros ly S W mem md q n a HAR Hin H1 H2.
destruct (al_blocks SEGS B LAWS ly S W mem md q n HAR Hin) as (_ & H4096 & Hceil & Hap & _).
pose proof (@ASAN_CEIL_range rc) as (Hc & _).
destruct Hap as (Ha0 & [HL | [HH1 HH2]]);
unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
[left; lia | right; lia].
Qed.
(* an address in the image band (a .rodata literal) *)
Lemma amem_range_img : forall a n, 0x10000 <= a -> 0 <= n -> a + n <= 0x5fb000 -> amem_range a n.
Proof. intros a n H1 H2 H3. unfold amem_range, kLowMemEnd. left. lia. Qed.

(* ---- The relay entry in the line loop's form. ----
   W_rep.v's aentry_ok with `no NUL in s->buf [0, s->used)` and `s->used <= 6000` replaced by
   `s->used <= s->cap`: between the memcpy and the move-down the buffer holds the bytes handed over, which do
   contain NULs (plain drain_b.v:2640 entry_okx). *)
Definition aentry_okx (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (e : rentry) : Prop :=
(re_eof e = 0 \/ re_eof e = 1) /\ (re_skip e = 0 \/ re_skip e = 1) /\
length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\
0 <= re_fd e < 2 ^ 31 /\
(re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
Z.of_nat (length (re_U e)) = re_used e /\ re_used e <= re_cap e /\
((re_cap e = 0 /\ re_buf e = 0 /\ re_used e = 0) \/
 (0 < re_cap e /\ In (re_buf e, re_cap e) (ablocks B ly S) /\
  Z.of_nat (length (re_junk e)) = re_cap e - re_used e /\
  garr8 SEGS (arm W mem) (re_buf e) (bzs (re_U e ++ re_junk e)))) /\
re_nheld e < 2 ^ 26 /\
((re_hp e = 0 /\ re_keys e = []) \/
 (re_hp e <> 0 /\ In (re_hp e, re_kh e) (ablocks B ly S) /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e /\
  garr8 SEGS (arm W mem) (re_hp e) (bzs (key_ptrs (re_keys e))))) /\
NoDup (map key_addr (re_keys e)) /\
NoDup (map key_text (re_keys e)) /\
Forall (fun k =>
  In (key_addr k, Z.of_nat (length (key_text k)) + 1) (ablocks B ly S) /\
  garr8 SEGS (arm W mem) (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])) /\
  ~ In (Z_to_bv 8 0) (key_text k) /\ 14 <= Z.of_nat (length (key_text k)) <= APARTIAL) (re_keys e).

Lemma aentry_okx_of_ok : forall ly S W mem e,
aentry_ok B ly S W mem e -> aentry_okx ly S W mem e.
Proof.
intros ly S W mem e H. unfold aentry_okx.
assert (HC : re_used e <= re_cap e).
{ destruct H as (_ & _ & _ & _ & _ & H6 & _ & H8 & _ & H10 & _).
  destruct H10 as [(A1 & A2 & A3)|(A1 & _)]; unfold APARTIAL in *; lia. }
unfold aentry_ok in H. tauto.
Qed.

Lemma aentry_ok_of_okx : forall ly S W mem e,
aentry_okx ly S W mem e -> ~ In (Z_to_bv 8 0) (re_U e) -> re_used e <= APARTIAL ->
aentry_ok B ly S W mem e.
Proof.
intros ly S W mem e H HN HU. unfold aentry_ok. unfold aentry_okx in H. tauto.
Qed.

(* ---- The entry context. ----
   One record for everything dr_spec quantifies over at the entry, so that every segment statement takes one
   argument and the cut predicates read the entry off it. *)
Record dcx : Type := mkDcx {
  dxregs : bvmap 5 word;
  dxly : alayout; dxS : astate; dxW : world SEGS; dxmem : word -> option byte; dxmd : Model;
  dxch : list (Z * Z * Z);
  dxG : Z; dxSA : Z; dxe : rentry; dxj : nat; dxh : hsrc;
  dxc : ctl; dxO : list byte; dxmx : Z; dxno : Z; dxcap : Z; dxout : Z;
  dxrest : list (Z * Z) }.

(* what the entry decides *)
Definition dHA (cx : dcx) : Z := rg_s RG + ASRC * Z.of_nat (dxj cx).
Definition dsp0 (cx : dcx) : Z := spZ (dxregs cx).
Definition dSTR (cx : dcx) : lstate := hs_state (dxh cx).            (* the reference splitter at the entry *)
Definition dPS (cx : dcx) : list Z := bzs (pending_stream (dxh cx)). (* the bytes the harness will hand over *)
Definition dlive (cx : dcx) : bool := dr_live (dxc cx) (dxh cx).
Definition dFP (cx : dcx) : list (Z * Z) := dr_fp (dxSA cx) (dxe cx) (dxh cx) (dxcap cx) (dxout cx).
Definition dfin (cx : dcx) : drain_b_c.dstate :=
dr_fin (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx).
Definition dtrc (cx : dcx) : dtrace := dr_tr (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx).
Definition dcost (cx : dcx) : Z := dr_cost MT (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx).
Definition ds0 (cx : dcx) : drain_b_c.dstate :=
drain_b_c.drain_init (dxno cx) (dxcap cx) (dxe cx) (dxh cx).
Definition dPOST (cx : dcx) : world SEGS -> config -> Prop :=
dr_post B MT RG (dxregs cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx)
  (dxSA cx) (dHA cx) (dxe cx) (dxh cx) (dxc cx) (dxO cx) (dxmx cx) (dxno cx) (dxcap cx) (dxout cx).

(* DBASE: exactly dr_spec's premises at the entry, with the Permutation's `rest` taken from the context. *)
Definition DBASE (cx : dcx) : Prop :=
afn_pre SEGS B DRAIN_STK (dxly cx) (dxS cx) (dxW cx) (dxregs cx) (dxmem cx) (dxmd cx) (dxch cx) /\
getr (dxregs cx) 10 = w64 (dxSA cx) /\
In (dxG cx, ATABLE) (ablocks B (dxly cx) (dxS cx)) /\
dxG cx <= dxSA cx /\ dxSA cx + AENT <= dxG cx + ATABLE /\
garr8 SEGS (arm (dxW cx) (dxmem cx)) (dxSA cx) (bzs (entry_bytes (dxe cx))) /\
awr (dxW cx) (dxmem cx) (dxSA cx) AENT /\
aentry_ok B (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxe cx) /\
(dxj cx < 4)%nat /\
asrc_at B (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dHA cx) (dxh cx) /\
aothers_at RG (dxW cx) (dxmem cx) (dxj cx) (re_fd (dxe cx)) /\
hs_fd (dxh cx) = re_fd (dxe cx) /\ re_skip (dxe cx) = hs_overlong (dxh cx) /\
(re_skip (dxe cx) = 0 -> bzs (re_U (dxe cx)) = bzs (hs_W (dxh cx))) /\
aout_at B RG (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxc cx) (dxO cx) (dxmx cx) (dxno cx) (dxcap cx) (dxout cx) /\
rom_view SEGS (dxW cx) (dxmem cx) /\
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) /\
Z.of_nat (length (pending_stream (dxh cx))) < 2 ^ 26 /\
hl_cap (hs_expected (dxh cx)) < 2 ^ 26 /\
re_nheld (dxe cx) + Z.of_nat (length (pending_stream (dxh cx))) < 2 ^ 26 /\
tr_max (dtrc cx) < MMAX /\
blocks_bytes (dxS cx) + tr_peak (dtrc cx) <= LIVE_MAX /\
mo_ok MT (dxS cx) (dcost cx).

(* ---- What the walk still owes the allocator. ---- *)
(* The rounds still to come from the round state s1, with base jb and addresses a: their requests are tl, and
   they leave drain's final state (the state does not depend on jb or a, W_drain_model.v drun_state). *)
Definition dlater (cx : dcx) (s1 : drain_b_c.dstate) (jb : nat) (a : drain_b_c.dadr) (tl : dtrace) : Prop :=
exists fuel : nat,
(dneed s1 <= fuel)%nat /\ dwf s1 /\
fst (drain_b_c.drain_run fuel (dlive cx) (dxmx cx) s1 jb a) = tl /\
fst (snd (drain_b_c.drain_run fuel (dlive cx) (dxmx cx) s1 jb a)) = dfin cx.

(* The meter: `spent` is what the walk has charged so far, tl what is still to come.  dr_spec's three resource
   premises, carried forward: the cost fits in dr_cost, the live bytes plus the peak of the requests still to come
   (tr_peak, C3) in LIVE_MAX, every request under MMAX. *)
Definition dbud (cx : dcx) (S1 : astate) (spent : Z) (tl : dtrace) : Prop :=
mo_le MT (dxS cx) S1 spent /\ 0 <= spent /\
spent + tr_cost MT tl <= dcost cx /\
blocks_bytes S1 + tr_peak tl <= LIVE_MAX /\
tr_max tl < MMAX.

(* The addresses after a round's lines (plain drain_b.v anext) and after its pushes (plain apush). *)
Definition danext (a : drain_b_c.dadr) (r : dadrF * dadrF * list dadrF) : drain_b_c.dadr :=
drain_b_c.DA (fst (fst r)) (drain_b_c.da_buf a) (snd (fst r)) (snd r) (drain_b_c.da_pend a)
  (drain_b_c.da_ev a) (drain_b_c.da_erecs a).
Definition dapush (a : drain_b_c.dadr) (vr : dadrF * list dadrF) : drain_b_c.dadr :=
drain_b_c.DA (drain_b_c.da_out a) (drain_b_c.da_buf a) (drain_b_c.da_hp a) (drain_b_c.da_keys a)
  (drain_b_c.da_pend a) (fst vr) (snd vr).

(* The line loop's rest and the rounds after it: the lines rl still to relay from g_nout = no, g_capout = oc,
   held keys H in an array of ka bytes, at base jb with g_out at o, the array at ha and the keys at ks; then the
   rounds from s2 with the addresses ab (plain drain_b.v lrest / MTR). *)
Definition dlfut (cx : dcx) (s2 : drain_b_c.dstate) (ab : drain_b_c.dadr) (no oc : Z) (H : list (list Z)) (ka : Z)
(rl : list (list Z)) (jb : nat) (o ha : dadrF) (ks : list dadrF) (tl : dtrace) : Prop :=
let lr := drain_b_c.lines_run (dlive cx) (dxmx cx) no oc H ka rl jb o ha ks in
exists tl2 : dtrace,
dlater cx s2 (jb + dnret (fst (fst lr)))%nat (danext ab (snd lr)) tl2 /\
tl = fst (fst lr) ++ tl2.

(* gesture_seen (H, ka, l) still to come, then the lines rl (plain drain_b.v srest). *)
Definition dsfut (cx : dcx) (s2 : drain_b_c.dstate) (ab : drain_b_c.dadr) (H : list (list Z)) (ka : Z)
(l : list Z) (no oc : Z) (rl : list (list Z)) (jb : nat) (o ha : dadrF) (ks : list dadrF) (tl : dtrace) : Prop :=
let sn := drain_b_c.seen_tr H ka l jb ha ks in
exists tl2 : dtrace,
dlfut cx s2 ab no oc (seen_arr H l) (seen_ka H ka l) rl (jb + dnret (fst (fst sn)))%nat o
  (fst (snd sn)) (snd (snd sn)) tl2 /\
tl = fst (fst sn) ++ tl2.

(* A round after its pushes: the list_drop of a used-up head text, then the relay's lines, then the rounds from
   the next state (W_drain_model.v ddrop / dlines / dnext). *)
Definition drfut (cx : dcx) (s1 : drain_b_c.dstate) (jb : nat) (a : drain_b_c.dadr) (tl : dtrace) : Prop :=
exists tl2 : dtrace,
dlfut cx (dnext (dlive cx) (dxmx cx) s1)
  (if dwhole s1 then drain_b_c.DA (drain_b_c.da_out a) (drain_b_c.da_buf a) (drain_b_c.da_hp a)
     (drain_b_c.da_keys a) (skipn 1 (drain_b_c.da_pend a)) (drain_b_c.da_ev a) (drain_b_c.da_erecs a) else a)
  (drain_b_c.ds_no s1) (drain_b_c.ds_ocap s1) (drain_b_c.ds_H s1) (drain_b_c.ds_ka s1) (drl s1)
  (jb + dnret (ddrop s1 a))%nat (drain_b_c.da_out a) (drain_b_c.da_hp a) (drain_b_c.da_keys a) tl2 /\
tl = ddrop s1 a ++ tl2.

(* A round whose reference_feed has pushed the lines of the first k of its n bytes: the pushes of the lines of
   the rest, then the round's rest (plain drain_b.v DPU). *)
Definition dpfut (cx : dcx) (s1 : drain_b_c.dstate) (k : nat) (jb : nat) (a : drain_b_c.dadr)
(v : dadrF) (rs : list dadrF) (tl : dtrace) : Prop :=
let done := lines (drain_b_c.ds_ref s1) (firstn k (ddata s1)) in
let pu := drain_b_c.pushes_run (drain_b_c.ds_en s1 + Z.of_nat (length done))
            (pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) done)
            (lines (feed (drain_b_c.ds_ref s1) (firstn k (ddata s1))) (skipn k (ddata s1))) jb v rs in
exists tl2 : dtrace,
drfut cx s1 (jb + dnret (fst (fst pu)))%nat (dapush a (snd pu)) tl2 /\
tl = fst (fst pu) ++ tl2.

(* ---- The memory core of every cut. ----
   The journal from the entry, the relay entry at SA in the line loop's form, the harness source at HA, the
   other three slots of g_s kept, the controller's output after `sent` lines, and the blocks.  (plain
   drain_b.v DC / LCORE, with relay_post / entry_okw / DBLK / DGLB / DOUT replaced by the ASan forms.) *)
Definition dctl (cx : dcx) (tot ev : Z) : ctl :=
let off := send_line_c.send_off (ct_cl (dxc cx)) (ct_br (dxc cx)) tot in
CTL (ct_cl (dxc cx)) (if off then ct_br (dxc cx) else ct_dd (dxc cx)) (ct_dd (dxc cx))
  (if off then ct_ei (dxc cx) else 0) ev.

Definition dr_saved (W1 : world SEGS) (m1 : word -> option byte) (spX : Z) (regsE : bvmap 5 word) : Prop :=
forall i, (i < 13)%nat ->
val_mem SEGS (arm W1 m1) (spX + 232 + 8 * Z.of_nat i) 8 (bv_unsigned (getr regsE (nth i DR_SAVED 0%bv))).

(* The prologue's constants in the frame: the field addresses of the relay entry, the shadow addresses of its
   cells, the shifted field addresses of g_s (the scan loop adds the shadow base and 12 i), (s & 7) + 3 and
   6001 (drain.s (sha256 fee9ca707eed; internal record) 0x830dc-0x831f4, DRAIN-MAP.md (sha256 b4a6c615b22f; internal record)). *)
Definition dr_frame (cx : dcx) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
let spX := dsp0 cx - DRAIN_FRAME in
let SA := dxSA cx in
let GS := rg_s RG in
val_mem SEGS (arm W1 m1) (spX + 208) 8 (SA + 8) /\
val_mem SEGS (arm W1 m1) (spX + 96) 8 (SA + 48) /\
val_mem SEGS (arm W1 m1) (spX + 128) 8 (SA + 40) /\
val_mem SEGS (arm W1 m1) (spX + 88) 8 (SA mod 8 + 3) /\
val_mem SEGS (arm W1 m1) (spX + 184) 8 6001 /\
val_mem SEGS (arm W1 m1) (spX + 120) 8 ((GS + 40) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 112) 8 ((GS + 48) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 104) 8 ((GS + 56) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 144) 8 ((GS + 32) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 152) 8 ((GS + 24) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 168) 8 ((GS + 12) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 136) 8 ((GS + 16) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 160) 8 (shadow_addr (SA + 32)) /\
val_mem SEGS (arm W1 m1) (spX + 224) 8 (shadow_addr (SA + 24)) /\
val_mem SEGS (arm W1 m1) (spX + 216) 8 (shadow_addr (SA + 16)) /\
val_mem SEGS (arm W1 m1) (spX + 176) 8 (shadow_addr SA) /\
dr_saved W1 m1 spX (dxregs cx).

Definition DMEM (cx : dcx) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte)
(md1 : Model) (k1 : Z) (e1 : rentry) (h1 : hsrc) (s1 : drain_b_c.dstate) (out1 ev1 : Z)
(sent : list (list Z)) (LB1 : list byte) : Prop :=
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m1 md1 k1 /\
rom_view SEGS W1 m1 /\ apres_kept B (dxW cx) (dxmem cx) W1 m1 /\ frames S1 = frames (dxS cx) /\
dr_frame cx W1 m1 /\
garr8 SEGS (arm W1 m1) (dxSA cx) (bzs (entry_bytes e1)) /\ awr W1 m1 (dxSA cx) AENT /\
aentry_okx ly1 S1 W1 m1 e1 /\
asrc_at B ly1 S1 W1 m1 (dHA cx) h1 /\
aothers_at RG W1 m1 (dxj cx) (re_fd (dxe cx)) /\
(forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA cx <= x < dHA cx + ASRC) ->
   abyte_kept (dxW cx) (dxmem cx) W1 m1 x) /\
aout_at B RG ly1 S1 W1 m1 (dctl cx (Z.of_nat (length (with_nul sent))) ev1)
  (if dlive cx then dxO cx ++ LB1 else dxO cx) (dxmx cx)
  (if dlive cx then drain_b_c.ds_no s1 else dxno cx) (drain_b_c.ds_ocap s1) out1 /\
(dlive cx = false -> out1 = dxout cx /\ drain_b_c.ds_ocap s1 = dxcap cx) /\
Permutation (ablocks B ly1 S1)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx).

(* The round state read off the relay entry and the harness source (plain drain_b.v DLINK). *)
Definition DLINK (s1 : drain_b_c.dstate) (e1 : rentry) (h1 : hsrc) : Prop :=
re_cap e1 = drain_b_c.ds_cap s1 /\ bzs (re_U e1) = drain_b_c.ds_u s1 /\
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) /\
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 /\ drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 /\
hs_eintr h1 = (if drain_b_c.ds_eintr s1 then 1 else 0) /\
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend s1 /\
hs_off h1 = drain_b_c.ds_off s1 /\ hs_state h1 = drain_b_c.ds_ref s1 /\
hl_n (hs_expected h1) = drain_b_c.ds_en s1 /\ hl_cap (hs_expected h1) = drain_b_c.ds_ecap s1 /\ dwf s1.

(* What drain never changes, and the held keys' array (plain drain_b.v DSAME / DKH). *)
Definition DSAME (cx : dcx) (e1 : rentry) (h1 : hsrc) : Prop :=
re_fd e1 = re_fd (dxe cx) /\ re_eof e1 = re_eof (dxe cx) /\
hs_fd h1 = hs_fd (dxh cx) /\ hs_open h1 = hs_open (dxh cx) /\ hs_closed h1 = hs_closed (dxh cx) /\
hl_v (hs_pending h1) = hl_v (hs_pending (dxh cx)) /\
hl_cap (hs_pending h1) = hl_cap (hs_pending (dxh cx)) /\
hs_partial h1 = hs_partial (dxh cx) /\ hs_held h1 = hs_held (dxh cx) /\
((re_hp e1 = re_hp (dxe cx) /\ re_kh e1 = re_kh (dxe cx)) \/ re_kh e1 <= 2 ^ 30).

(* What the rounds so far did with the bytes D handed over: the reference splitter and the relay agree on D's
   lines, the expected list gained them, the relay sent `sent` and its held keys were updated with `kl`
   (plain drain_b.v DHIST / DHISTg; nk is the number of key updates still to come in this round). *)
Definition DHIST (cx : dcx) (s1 : drain_b_c.dstate) (D F : list Z) (sent kl : list (list Z)) (h1 : hsrc)
(LB1 : list byte) (nk : Z) : Prop :=
dPS cx = D ++ pstream s1 /\ drain_b_c.ds_ref s1 = feed (dSTR cx) D /\
map snd (hl_recs (hs_expected h1)) =
  map snd (hl_recs (hs_expected (dxh cx))) ++ map (map (Z_to_bv 8)) (lines (dSTR cx) F) /\
firstn (length (hl_recs (hs_expected (dxh cx)))) (hl_recs (hs_expected h1)) = hl_recs (hs_expected (dxh cx)) /\
hl_cap (hs_expected h1) <= Z.max 8 (Z.max (hl_cap (hs_expected (dxh cx))) (2 * hl_n (hs_expected h1))) /\
drain_b_c.ds_no s1 = dxno cx + Z.of_nat (length (with_nul sent)) /\
bzs LB1 = with_nul sent /\
NoDup (drain_b_c.ds_H s1) /\
same_set (drain_b_c.ds_H s1) (upds (drain_b_c.keys_texts (re_keys (dxe cx))) kl) /\
Z.of_nat (length (drain_b_c.ds_H s1)) + nk + Z.of_nat (length (pstream s1)) < 2 ^ 26 /\
drain_b_c.ds_en s1 + Z.of_nat (length (pstream s1)) < 2 ^ 27.

(* The relay's buffer in the line loop: the bytes it held, then the bytes handed over (plain drain_b.v dW). *)
Definition dW (s1 : drain_b_c.dstate) : list Z := drain_b_c.ds_u s1 ++ ddata s1.

(* The round state seen from the line loop (plain drain_b.v dvirt): the relay's fields from the loop, the
   harness's from drain_run's next state. *)
Definition dvirt (cx : dcx) (s1 : drain_b_c.dstate) (sk : bool) (H : list (list Z)) (ka no oc : Z)
: drain_b_c.dstate :=
let s2 := dnext (dlive cx) (dxmx cx) s1 in
drain_b_c.DS (drain_b_c.ds_cap s1) (dW s1) sk H ka false
  (drain_b_c.ds_pend s2) (drain_b_c.ds_off s2) (drain_b_c.ds_ref s2) (drain_b_c.ds_en s2)
  (drain_b_c.ds_ecap s2) no oc.

(* The line loop after the prefix [0, p) of the buffer (plain drain_b.v drlp / dskp / drlq / dlrun / ...). *)
Definition drlp (s1 : drain_b_c.dstate) (p : nat) : list (list Z) :=
snd (scan (drain_b_c.ds_skip s1) [] (firstn p (dW s1))).
Definition dskp (s1 : drain_b_c.dstate) (p : nat) : bool :=
if Nat.eqb p 0 then drain_b_c.ds_skip s1 else false.
Definition drlq (s1 : drain_b_c.dstate) (p : nat) : list (list Z) :=
snd (scan (dskp s1 p) [] (skipn p (dW s1))).
Definition dlrun (cx : dcx) (s1 : drain_b_c.dstate) (p : nat) : Z * list (list Z) * Z :=
lrun (dlive cx) (dxmx cx) (drain_b_c.ds_no s1) (drain_b_c.ds_ocap s1) (drain_b_c.ds_H s1)
  (drain_b_c.ds_ka s1) (drlp s1 p).
Definition dlno (s1 : drain_b_c.dstate) (p : nat) : Z :=
drain_b_c.ds_no s1 + Z.of_nat (length (with_nul (drlp s1 p))).
Definition dloc (cx : dcx) (s1 : drain_b_c.dstate) (p : nat) : Z := fst (fst (dlrun cx s1 p)).
Definition dlH (cx : dcx) (s1 : drain_b_c.dstate) (p : nat) : list (list Z) := snd (fst (dlrun cx s1 p)).
Definition dlka (cx : dcx) (s1 : drain_b_c.dstate) (p : nat) : Z := snd (dlrun cx s1 p).
(* p is 0 or just after a NUL of the buffer; the line [p, q). *)
Definition dbound (s1 : drain_b_c.dstate) (p : nat) : Prop :=
(p <= length (dW s1))%nat /\ (p = 0%nat \/ nth_error (dW s1) (p - 1) = Some 0).
Definition dline (s1 : drain_b_c.dstate) (p q : nat) : list Z := firstn (q - p) (skipn p (dW s1)).

(* The round's start state after the rounds that handed over D (plain drain_b.v RSTART). *)
Definition RSTART (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) : Prop :=
drain_b_c.ds_ref s1 = feed (dSTR cx) D /\
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) /\
4096 <= drain_b_c.ds_cap s1 - ulen s1 /\ dwf s1 /\ dstrict s1 /\
drain_b_c.ds_eintr s1 = false /\ drain_b_c.ds_pend s1 <> [].

(* The line loop's core: the harness side of the round is done (D ++ ddata s1 taken), the relay has sent `sent`
   and updated its held keys with `kl`; g_nout = no, g_capout = oc, s->skip = sk, and nk key updates and the
   requests `tl` of this round and the later rounds are still to come (plain drain_b.v LCORE). *)
Definition LCORE (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (sent kl : list (list Z))
(H : list (list Z)) (ka no oc nk : Z) (sk : bool)
(ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
let sv := dvirt cx s1 sk H ka no oc in
DMEM cx ly1 S1 W1 m1 md1 k1 e1 h1 sv out1 ev1 sent LB1 /\
DLINK sv e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sv (D ++ ddata s1) (D ++ ddata s1) sent kl h1 LB1 nk /\
RSTART cx s1 D /\ dbud cx S1 spent tl.

(* ---- The eight cut predicates, over concrete machine states. ---- *)

(* DI (0x831f8): the outer loop's head in the round state s1, after the rounds that handed over D.
   s6 = s, s9 / s11 / s10 = &s->cap / &s->used / &s->buf, s2 = g_s, s1 = g_s >> 3, s0 = (g_s + 4) >> 3,
   s5 = the shadow base, s7 = shadow (&s->cap), s8 = shadow (s); s3 and s4 are dead here. *)
Definition dregs_top (cx : dcx) (regs1 : bvmap 5 word) : Prop :=
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 22 = w64 (dxSA cx) /\ getr regs1 25 = w64 (dxSA cx + 32) /\
getr regs1 27 = w64 (dxSA cx + 24) /\ getr regs1 26 = w64 (dxSA cx + 16) /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
getr regs1 23 = w64 (shadow_addr (dxSA cx + 32)) /\ getr regs1 24 = w64 (shadow_addr (dxSA cx)).

Definition DI (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_top) regs1 m1 md1 /\
dregs_top cx regs1 /\
DMEM cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 /\
(* in the outer loop the buffer holds no NUL and at most 6000 bytes: the tight form of the relay entry *)
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DLINK s1 e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) /\
dlater cx s1 jb a tl /\ dbud cx S1 spent tl.

(* DEND (0x83bbc): fuzz_recv found no pending text, so this is the last round; the walk tests h->closed and
   returns through the eof store (0x83b64) or EAGAIN (0x83b44).  s7 = &g_s[j], s8 = the shadow base + 12 j. *)
Definition DEND (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 22 = w64 (dxSA cx) /\ getr regs1 18 = w64 (rg_s RG) /\ getr regs1 21 = w64 SHADOW_OFF /\
getr regs1 23 = w64 (dHA cx) /\ getr regs1 24 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) /\
dr_frame cx W1 m1 /\
DMEM cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DLINK s1 e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) /\
(* the model's last round: nothing pending, no EINTR, room in the buffer *)
drain_b_c.ds_pend s1 = [] /\ drain_b_c.ds_eintr s1 = false /\ 4096 <= drain_b_c.ds_cap s1 - ulen s1 /\
dlater cx s1 jb a tl /\ dbud cx S1 spent tl.

(* DRB (0x8347c): reference_feed's byte loop (fuzz_reply.c:221-236) after k of the n = dnum s1 bytes.
   s9 counts down (n - k); s8 and s10 both hold the source pointer p0 + k, where p0 = v[0].s + pending_off is
   the head pending text's unread bytes (s8 is the one the shadow check shifts, s10 the one the load reads);
   s7 = &g_s[j], s3 = n, s4 / s11 / s6 = the shadow bytes of h->partial, h->npartial and h->overlong.
   The n bytes are already in the relay's buffer after s->used (s->used is not yet updated, so they sit in
   the first n bytes of re_junk). *)
Definition DRB (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a v rs tl p0 r0 rs0,
c1 = cfg_at SEGS (BASE + A_dr_feed) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
getr regs1 23 = w64 (dHA cx) /\ getr regs1 19 = w64 (dnum s1) /\
getr regs1 25 = w64 (dnum s1 - Z.of_nat k) /\
getr regs1 26 = w64 (p0 + Z.of_nat k) /\ getr regs1 24 = w64 (p0 + Z.of_nat k) /\
getr regs1 20 = w64 (shadow_addr (dHA cx + 40)) /\ getr regs1 27 = w64 (shadow_addr (dHA cx + 48)) /\
getr regs1 22 = w64 (shadow_addr (dHA cx + 56)) /\
dr_frame cx W1 m1 /\
(* the frame slots the round set up: the saved s6/s9/s10/s11, &h->expected, &h->overlong, the shadow cells *)
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 56) 8 (dxSA cx) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 64) 8 (dxSA cx + 32) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 48) 8 (dxSA cx + 24) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 200) 8 (dxSA cx + 16) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 32) 8 (dHA cx + 24) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 (dHA cx + 56) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 72) 8 (dHA cx + 64) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 80) 8 (shadow_addr (dHA cx + 16)) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 40) 8 (shadow_addr (dHA cx + 24)) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (shadow_addr (dHA cx + 32)) /\
(* the bytes still to feed start at p0 + k, in the head pending text; the n bytes handed over are already
   in the relay's buffer after s->used.  k < n: the byte loop is a do-while (s9 = n is set at 0x83478, the test
   `bne s9, zero` is at the bottom 0x83550), so DRB k is the head with at least one byte still to feed. *)
hl_recs (hs_pending h1) = r0 :: rs0 /\ p0 = fst r0 + drain_b_c.ds_off s1 /\
(Z.of_nat k < dnum s1)%Z /\ 0 < dnum s1 /\
bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 /\
DMEM cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DSAME cx e1 h1 /\
(* the harness's fields after the lines of the first k bytes were pushed (plain drain_b.v DRB) *)
re_cap e1 = drain_b_c.ds_cap s1 /\ bzs (re_U e1) = drain_b_c.ds_u s1 /\
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) /\
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 /\ drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 /\
hs_eintr h1 = 0 /\
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend s1 /\
hs_off h1 = drain_b_c.ds_off s1 /\
hs_state h1 = feed (drain_b_c.ds_ref s1) (firstn k (ddata s1)) /\
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (lines (drain_b_c.ds_ref s1) (firstn k (ddata s1)))) /\
hl_cap (hs_expected h1) =
  pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (lines (drain_b_c.ds_ref s1) (firstn k (ddata s1))) /\
DHIST cx s1 D (D ++ firstn k (ddata s1)) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
RSTART cx s1 D /\
dpfut cx s1 k jb a v rs tl /\ dbud cx S1 spent tl.

(* DE (0x835ac): the byte loop left, every byte of the round fed to the reference splitter and its lines
   pushed.  s3 = n, s7 = &g_s[j]; the pending offset, list_drop, s->used and the first memchr are to come. *)
Definition DE (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_fed) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
getr regs1 23 = w64 (dHA cx) /\ getr regs1 19 = w64 (dnum s1) /\
dr_frame cx W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 56) 8 (dxSA cx) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 64) 8 (dxSA cx + 32) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 48) 8 (dxSA cx + 24) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 200) 8 (dxSA cx + 16) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 32) 8 (dHA cx + 24) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 80) 8 (shadow_addr (dHA cx + 16)) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 40) 8 (shadow_addr (dHA cx + 24)) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (shadow_addr (dHA cx + 32)) /\
0 < dnum s1 /\ bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 /\
DMEM cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DSAME cx e1 h1 /\
re_cap e1 = drain_b_c.ds_cap s1 /\ bzs (re_U e1) = drain_b_c.ds_u s1 /\
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) /\
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 /\ drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 /\
hs_eintr h1 = 0 /\
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend s1 /\
hs_off h1 = drain_b_c.ds_off s1 /\
hs_state h1 = feed (drain_b_c.ds_ref s1) (ddata s1) /\
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (dref s1)) /\
hl_cap (hs_expected h1) = pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (dref s1) /\
DHIST cx s1 D (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
RSTART cx s1 D /\
drfut cx s1 jb a tl /\ dbud cx S1 spent tl.

(* DLL (0x836bc): the line [p, q) of the relay's buffer found (relay.c:207).  s7 = s->buf + q (the NUL),
   s8 = s->buf + p, s11 = &s->used; 192(sp) = (&s->skip) >> 3.  s9 and s10 are dead here. *)
Definition dregs_line (cx : dcx) (regs1 : bvmap 5 word) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 22 = w64 (dxSA cx) /\ getr regs1 27 = w64 (dxSA cx + 24) /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
dr_frame cx W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 ((dxSA cx + 8) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 200) 8 (dxSA cx + 16) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 56) 8 (dxSA cx) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 48) 8 (dxSA cx + 24) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 64) 8 (dxSA cx + 32).

(* The line loop's state after the prefix [0, p): the lines drlp relayed, the keys dlH, g_nout dlno,
   g_capout dloc, s->skip dskp, and the lines drlq still to relay (plain drain_b.v DLC). *)
Definition DLC (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p : nat)
(ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
LCORE cx s1 D (lines (dSTR cx) D ++ drlp s1 p) (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p) (Z.of_nat (length (drlq s1 p))) (dskp s1 p)
  ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.

Definition DLL (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_line) regs1 m1 md1 /\
dregs_line cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
dbound s1 p /\ (p <= q < length (dW s1))%nat /\ nth_error (dW s1) q = Some 0 /\
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) /\
DLC cx s1 D p ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlno s1 p) (dloc cx s1 p) (dlH cx s1 p) (dlka cx s1 p)
  (drlq s1 p) jb o ha ks tl.

(* DLN (0x836f4): the line ending at buffer[p - 1] is done (relay.c:214).  s7 = s->buf + p - 1. *)
Definition DLN (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_next) regs1 m1 md1 /\
dregs_line cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat p - 1) /\
dbound s1 p /\ (0 < p)%nat /\
DLC cx s1 D p ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlno s1 p) (dloc cx s1 p) (dlH cx s1 p) (dlka cx s1 p)
  (drlq s1 p) jb o ha ks tl.

(* DLR (0x83a4c): no NUL in the buffer from p on (relay.c:216).  s8 = s->buf + p, s9 = |W| - p, s10 = s->buf. *)
Definition DLR (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_rest) regs1 m1 md1 /\
dregs_line cx regs1 W1 m1 /\
getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 25 = w64 (Z.of_nat (length (dW s1) - p)) /\
getr regs1 26 = w64 (re_buf e1) /\
dbound s1 p /\ (forall i, (p <= i)%nat -> nth_error (dW s1) i <> Some 0) /\
DLC cx s1 D p ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlno s1 p) (dloc cx s1 p) (dlH cx s1 p) (dlka cx s1 p)
  (drlq s1 p) jb o ha ks tl.

(* DGS (0x837c8): the line [p, q) was sent and is a gesture of kind k with key `firstn jj (dline s1 p q)`;
   gesture_seen's search over the held array is to come.  s8 = s->buf + p, s9 = the last space,
   s7 = s->buf + q, s3 = 0 for a begin and the begin test's nonzero strcmp result for an end. *)
Definition DGS (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_seen) regs1 m1 md1 /\
dregs_line cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 25 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) /\ getr regs1 19 = w64 bg /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
dbound s1 p /\ (p <= q < length (dW s1))%nat /\ nth_error (dW s1) q = Some 0 /\
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) /\
dskp s1 p = false /\ (q - p <= LINE_LIMIT)%nat /\
(* the line is sent; the held keys are not yet updated with it *)
LCORE cx s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dsfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (drlq s1 (S q)) jb o ha ks tl.

(* ---- The segment statements. ----
   Every segment concludes `SRr SEGS W1 c1 (dPOST cx)` and takes its continuations in the same form, so the
   compositions below are plain applications. *)

(* PRO: the prologue 0x830dc .. 0x831f4 (13 saves, the field and shadow constants into the frame, the shadow
   base from the GOT) to the outer loop's head in the initial round state. *)
Definition dr_pro_stmt : Prop :=
forall cx,
DBASE cx ->
(forall W2 c2, DI cx (ds0 cx) [] W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS (dxW cx) (cfg_at SEGS A_drainP (dxregs cx) (dxmem cx) (dxmd cx)) (dPOST cx).

(* TOP: DI 0x831f8 -> the round's growth (realloc #1, 0x83248), source_of's scan (0x83294-0x832e8), the EINTR
   round (0x83314-0x83360, errno = EINTR, back to DI), the empty-pending test (0x83364 -> DEND), the data
   round's n and memcpy (0x83380-0x833f4) and the setup of the byte loop (-> DRB 0).  The EINTR re-entry is
   offered only for a round state whose EINTR flag is set (TOP takes that arm only when h->eintr = 1, and DLINK
   ties h->eintr to ds_eintr s1): without the guard OUTER's induction has no decreasing measure at that arm
   (dclr (dgrow s1) = s1 when no growth and no EINTR is due). *)
Definition dr_top_stmt : Prop :=
forall cx s1 D W1 c1,
DBASE cx -> DI cx s1 D W1 c1 ->
(drain_b_c.ds_eintr s1 = true -> forall W2 c2, DI cx (dclr (dgrow s1)) D W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
(forall W2 c2, DEND cx (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
(forall W2 c2, DRB cx (dgrow s1) D 0 W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).

(* FEED: one byte of reference_feed's loop 0x8347c-0x83550: the NUL case (list_push of h->partial onto
   h->expected, npartial = 0, overlong = 0), the overlong case and the ordinary case
   (partial[npartial++] = b). *)
Definition dr_feed_stmt : Prop :=
forall cx s1 D k W1 c1,
DBASE cx -> DRB cx s1 D k W1 c1 ->
(forall W2 c2, DRB cx s1 D (S k) W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
(forall W2 c2, DE cx s1 D W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).

(* DROP: DE 0x835ac -> pending_off += n (0x835c0), list_drop of a used-up head text (free 0x83618 and
   __asan_memmove 0x83648, pending.n -= 1, pending_off = 0), s->used += n (0x83684) and the first
   memchr (0x836a4) -> the first line, or no line at all. *)
Definition dr_drop_stmt : Prop :=
forall cx s1 D W1 c1,
DBASE cx -> DE cx s1 D W1 c1 ->
(forall q W2 c2, DLL cx s1 D 0 q W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
(forall W2 c2, DLR cx s1 D 0 W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).

(* LINEA: DLL 0x836bc -> the skip / overlong test (0x836bc-0x836f0), send_line (0x83744) and gesture_seen's
   tests: strrchr (0x83750), strncmp "param_gesture" (0x83768), line[13] == ' ', last != NULL,
   last != line + 13, strcmp "begin" (0x837a8) and strcmp "end" (0x837c0). *)
Definition dr_linea_stmt : Prop :=
forall cx s1 D p q W1 c1,
DBASE cx -> DLL cx s1 D p q W1 c1 ->
(forall W2 c2, DLN cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
(forall W2 c2, DGS cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).

(* GS: DGS 0x837c8 -> the held search loop 0x83838-0x83874 (strlen 0x83850, strncmp 0x83864), then
   a begin not held (realloc #2 0x838c0, strndup 0x838e0, held[nheld++] = key) or an end held
   (free #2 0x8394c, nheld -= 1, held[n] = held[nheld]) -> on to the next line. *)
Definition dr_gs_stmt : Prop :=
forall cx s1 D p q W1 c1,
DBASE cx -> DGS cx s1 D p q W1 c1 ->
(forall W2 c2, DLN cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).

(* NEXT: DLN 0x836f4 -> start = nul + 1, memchr (0x8372c) -> the next line, or the loop's exit. *)
Definition dr_next_stmt : Prop :=
forall cx s1 D p W1 c1,
DBASE cx -> DLN cx s1 D p W1 c1 ->
(forall q W2 c2, DLL cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
(forall W2 c2, DLR cx s1 D p W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).

(* REST: DLR 0x83a4c -> s->used = |W| - p (0x83a58), __asan_memmove of the rest to the buffer's start
   (0x83a68), and the 6001 test (s->used = 0 and s->skip = 1 when the rest is too long) -> DI of the next
   round, with the bytes handed over added to D. *)
Definition dr_rest_stmt : Prop :=
forall cx s1 D p W1 c1,
DBASE cx -> DLR cx s1 D p W1 c1 ->
(forall W2 c2, DI cx (dnext (dlive cx) (dxmx cx) s1) (D ++ ddata s1) W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).

(* EPI: the epilogue 0x83b80 (ld ra / s0 .. s11, addi sp, sp, 336, ret).  It writes nothing: the caller's
   continuation gets the same restricted memory and the same journal (the form of W_send_line_cx.v sl_epi). *)
Definition dr_epi_stmt : Prop :=
forall cx ly1 S1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m1 md1 k1 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
YK0s.ret_ok (getr (dxregs cx) 1) ->
dr_saved W1 m1 (dsp0 cx - DRAIN_FRAME) (dxregs cx) ->
(forall regs' m' md', aregs_preserved (dxregs cx) regs' ->
   (forall x, arm W1 m' x = arm W1 m1 x) ->
   @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
     (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m' md' k1 ->
   Q W1 (mkCfg (mkst regs' (getr (dxregs cx) 1) m' (seg_rom SEGS)) md')) ->
SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_epi) regs1 m1 md1) Q.

(* END: DEND 0x83bbc -> h->closed ? (s->eof = 1 at 0x83b64) : (errno = EAGAIN at 0x83b44), then the
   epilogue; this is where the drain returns.  dr_end_concl is what END gives once the epilogue is supplied. *)
Definition dr_end_concl : Prop :=
forall cx s1 D W1 c1,
DBASE cx -> DEND cx s1 D W1 c1 ->
SRr SEGS W1 c1 (dPOST cx).
Definition dr_end_stmt : Prop := dr_epi_stmt -> dr_end_concl.

(* ---- The compositions. ----
   A composition takes the segment STATEMENTS it chains, and the CONCLUSION (the *_concl form) of every
   composition below it, so that the assembly supplies each premise from exactly one theorem:
     pb_drain := dr_all dr_pro
                   (dr_outer dr_top (dr_feeds dr_feed) dr_drop
                      (dr_lines dr_linea (dr_gs_of gs_scan gs_add gs_free) dr_next dr_rest)
                      (dr_end dr_epi)). *)

(* FEEDS: the byte loop, by induction on dnum s1 - k. *)
Definition dr_feeds_concl : Prop :=
forall cx s1 D k W1 c1,
DBASE cx -> DRB cx s1 D k W1 c1 ->
(forall W2 c2, DE cx s1 D W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).
Definition dr_feeds_stmt : Prop := dr_feed_stmt -> dr_feeds_concl.

(* LINES: the line loop, by induction on |dW s1| - p, from any of its three cut points to the next round. *)
Definition dr_lines_concl : Prop :=
forall cx s1 D W1 c1,
DBASE cx ->
((exists p q, DLL cx s1 D p q W1 c1) \/ (exists p, DLN cx s1 D p W1 c1) \/ (exists p, DLR cx s1 D p W1 c1)) ->
(forall W2 c2, DI cx (dnext (dlive cx) (dxmx cx) s1) (D ++ ddata s1) W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).
Definition dr_lines_stmt : Prop :=
dr_linea_stmt -> dr_gs_stmt -> dr_next_stmt -> dr_rest_stmt -> dr_lines_concl.

(* OUTER: the outer loop, by induction on dneed s1 (W_drain_model.v drun_grow / drun_eintr / drun_end /
   drun_data / dneed_dnext).  It takes TOP and DROP as statements and the byte loop, the line loop and END as
   their conclusions. *)
Definition dr_outer_concl : Prop :=
forall cx s1 D W1 c1,
DBASE cx -> DI cx s1 D W1 c1 ->
SRr SEGS W1 c1 (dPOST cx).
Definition dr_outer_stmt : Prop :=
dr_top_stmt -> dr_feeds_concl -> dr_drop_stmt -> dr_lines_concl -> dr_end_concl -> dr_outer_concl.

(* The walk: the prologue and the outer loop's conclusion give drain's contract. *)
Definition dr_all_stmt : Prop :=
dr_pro_stmt -> dr_outer_concl -> dr_spec B MT MMAX RG A_drainP.

End c.
End b.
End a.
