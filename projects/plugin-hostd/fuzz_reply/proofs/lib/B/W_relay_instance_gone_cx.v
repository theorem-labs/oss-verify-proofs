(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the SEGMENT INTERFACE of the IMAGE-B walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan-ubsan 0x82ca0 .. 0x83278, 374 instructions), the twin of lib/A/W_relay_instance_gone_cx.v (lib/A
   input: a working branch b38ac8437a7).  Hand-written: image B's relay_instance_gone is a different function (UBSan
   trap mode), so only the FORM carries over: the same cuts (outer head, inner head, entry done, unlock tail), the same
   invariants GOUT / GIN and budget gbud, the same segment statements.  Nothing is proved here.

   IMAGE B AGAINST IMAGE A.
   - The same frame (224 bytes, thirteen saves at 120(sp) .. 216(sp)) and the same class-1 fake frame F
     (__asan_stack_malloc_1 (128) at 0x82d0c; the real-stack fallback 0x82d20-0x82d38 is refuted as on image A: the
     detect_stack_use_after_return cell is 1 (al_const) and SMP gives a fake frame under GBASE's count_cid premise).
   - The shadow base lives in s5 (image A: s2); the frame slots differ: 8(sp), 16(sp) and 112(sp) = F, 24(sp) = g_src's
     register image, 32(sp) = 0x7fffffff (the int32 bound of i + 1), 40(sp) = F's shadow, 48(sp) = "param_gesture"
     (.str.6, A_OBJ 18), 56(sp) = "%s %d " (.str.9, A_OBJ 17), 64(sp) = g_nsrc's register image, 72(sp) = the id
     (a0 at the entry), 80(sp) = i (written by TOP), 88(sp) = F + 32 (the prefix buffer).
   - g_src is reloaded and checked at every use; 24 trap edges (TRAPS-ALL.md sha256 c90982171c9b; internal record): in TOP the entry pointer's
     overflow / null-consistency / null / alignment checks (0x82e38-0x82e48, again 0x82e7c-0x82e80 and 0x82ec4-0x82ecc
     after drain and strlen); in KEY the held array's and held[n]'s (0x82f18-0x82f38, again after gesture_end
     0x82f7c-0x82f9c), nheld's int32 decrement (0x82fd4), the move's index and wrap checks (0x82ff4-0x83038, among them
     `not a2,a1; bltu a2,s3`, the WRAP family of lib/B/W_traps.v); in STEP the int32 bound of i + 1 (0x830ec).  All
     trap edges go to `unimp` at 0x83220 and are proved not taken (lib/B/W_traps.v on a working branch).
   - The inner loop's head is 0x82f08: the end arm returns there (s6 = 8 n unchanged), the pass arm through 0x82f04
     (s6 recomputed); both arms of KEY therefore end at 0x82f08.

   CUT POINTS
     RGO i       0x82e1c  the outer loop's head at entry i (GOUT i);
     RGI i n r   0x82f08  the inner (held keys) loop's head at index n of entry i, r + 1 = nheld - n (GIN);
     RGE i       0x830c4  entry i done (GOUT (S i)), before the step;
     RGU         0x8312c  the unlock tail, every entry done (GOUT |es|).
   SEGMENTS (as image A)
     PRO    0x82ca0 -> RGO 0 | RGU         TOP    RGO i -> RGI i 0 r | RGE i      KEY    RGI i n (S r) -> RGI i (S n) r | RGI i n r
     KEYS   the inner loop by induction    STEP   RGE i -> RGO (S i) | RGU       OUTER  the outer loop by induction
     TAIL   RGU -> rig_post (unlock, the frame's release 0x83138-0x831dc, the epilogue)

   STATEMENT TEXT: GBASE is exactly the kit's rig_spec premise list (lib/B/W_contract.v at bkit 5bf9ced2993: rg_place
   and the capacity conjuncts; no canary premise since a Theorem Labs lane's HCANR ruling; B's FR_GUARD = 0x5f9a30, its GOT word
   FR_GOT_GUARD = 0x9ebd8).  C3 (the peak form, the image-A twin's 475b8a2b569) REMOVED both capacity conjuncts
   (`gxcap cx < MMAX` and `blocks_bytes + tr_alloc + 4 * max cap tr_max <= LIVE_MAX`): ge_room is stated over
   gesture_end's own trace, so rig_spec and GBASE take blocks_bytes + tr_peak tr <= LIVE_MAX (tr_max tr < MMAX and
   the meter unchanged), and gbud's room over the remaining trace tl is blocks_bytes S1 + tr_peak tl <= LIVE_MAX
   (was + tr_alloc tl).
   CONSUMER NOTE (the B top's call of relay_instance_gone): rig_spec's room premise at the call is `blocks_bytes S +
   tr_peak tr <= LIVE_MAX` (was `+ tr_alloc tr`), with tr = rig_tr c mx |O| cap ID es hs; the two premises `cap <
   MMAX` and `blocks_bytes S + tr_alloc tr + 4 * Z.max cap (tr_max tr) <= LIVE_MAX` are gone.

   ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record); the image-A twin is the RIG_x round, commit
   f4cd818e98d): converted IN PLACE to any allocator relation ARx with its laws and the room record RP (W_journal_x.v
   Record roomp); the AR statement is dropped (a Theorem Labs lane's ruling 10:34Z: no consumer).  Section c takes PST / ARx /
   hl / LAWS (AR_laws_x), HP0 (a Theorem Labs lane's ruling: no hidden head in any ARx state), the frame twins' hypotheses of
   W_frame_x.v in place of ML / SMP (IMGC, BLKN, OWNLOW, WFx, WFL, SFREE, SMALLOC) with ASMP / ASF / FFL in their _x
   forms, the runtime entries and callees in their _x room forms (W_sites_x.v, W_contract_x.v, W_journal_x.v Section
   hc), ALLOC_TAIL and HGOTG over ARx, the literals' shadow by W_contract_x.ashp_x (glit_at_x), and two facts on the
   program statics PST that the journal's image clause exempts (PSTR, PSTG; both hold at PST = []), as image A's
   W_relay_instance_gone_cx.v does.  The entry record gcx gains the entry's head set gxHp and room budget gxkr; GBASE is
   rig_spec_x's premises exactly (W_contract_x.v rig_spec_x, at the kit's RIG_STK_x = RIG_STK + 128: the drain it calls
   takes DRAIN_STK_x), gPOST rig_post_x; GLIVE's journal is ajournal_gx_x at RIG_STK_x from gxHp to the cut's head set
   Hp1 (existential, beside fpos); gbud takes the cut's layout and carries, beside the meter, the room the requests still
   owed need on top of gxkr (rp_RM RP S1 (Z.to_nat (tr_cost MT_rk tl) + gxkr cx)) and the live counts plus rig_pk's
   shape over those requests (cnt_ok_pk RP (fun P => Z.to_nat (tr_peakP P tl) + 3) (ablocks B ly1 S1)); at the entry
   (tl = gtr cx) both are GBASE's, by conversion.  rig_all_stmt concludes rig_spec_x. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c relay_instance_gone_b_c drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x W_frame_x.
(* the count names (tr_peakP): lib/B/ReplyCnt.v, the one definition; Required, not Imported, and named qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
(* route R: a Theorem Labs lane's B rig_post_xR / rig_spec_xR, the B dr_spec_xR / ge_spec_xR, SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_relayB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
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

(* ---- The walk's program counters (B text base 0x82344; AF_fr_relay_instance_gone = 0x95c). ---- *)
Definition A_rig_entry : Z := AF_fr_relay_instance_gone.            (* 0x82ca0, the entry *)
Definition A_rig_entryP : Z := BASE + A_rig_entry.
Definition A_rig_outer : Z := AF_fr_relay_instance_gone + 0x17c.    (* 0x82e1c, the outer loop's head *)
Definition A_rig_inner : Z := AF_fr_relay_instance_gone + 0x268.    (* 0x82f08, the inner loop's head *)
Definition A_rig_step : Z := AF_fr_relay_instance_gone + 0x424.     (* 0x830c4, entry i done *)
Definition A_rig_unlock : Z := AF_fr_relay_instance_gone + 0x48c.   (* 0x8312c, the unlock tail *)

(* The callee-saved registers in their frame slots 120(sp) (s11) .. 216(sp) (ra), sp = the entry sp - 224. *)
Definition RIG_SAVED : list (bv 5) :=
[27%bv; 26%bv; 25%bv; 24%bv; 23%bv; 22%bv; 21%bv; 20%bv; 19%bv; 18%bv; 9%bv; 8%bv; 1%bv].

(* The register images of g_nsrc and g_src: the auipc at 0x82dcc (kept at 64(sp); g_nsrc = it - 172, listing A_HI
   41) and s7, the auipc at 0x82dec (kept at 24(sp); g_src = s7 - 172, listing A_HI 42). *)
Definition RIG_HI_NSRC : Z := 172.
Definition RIG_HI_SRC : Z := 172.

Section c.
Variable B : asyms.
(* the program statics of the generic journal (YCbqG.ajournal_x's image clause exempts them) *)
Variable PST : list (Z * Z).
(* the allocator relation, its third argument the head set Hp *)
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (K0_SITES' CTX_AFREE) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts').  Each is either the AR
   walk's (AR-free, verbatim) or its _x twin (image A's W_relay_instance_gone_cx.v, the same list). ---- *)
(* the instance's laws, over ARx *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* no hidden head in any ARx state (a Theorem Labs lane's HP0 ruling; W_journal_x.v range_addressable_of_block_hp0_x) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MLAW : ameter_laws MT.
(* the frame twins' hypotheses (W_frame_x.v), in place of ML / SMP: the image cover IMGC (frm_off_imgP_x; image B's
   bound 0x5fc000, W_kit_x.v's IMGC); a live block's size is non-negative (W_kit_x.v's BLKN); the owned-low law OWNLOW,
   the model invariant WFx with its law WFL, and the two facts the twins read off model_laws / stack_malloc_progressP
   (SFREE, SMALLOC) *)
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
(* the fake frame's laws over ARx: __asan_stack_malloc_1 (class 1), the release's flag store and frame free *)
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 1.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
(* the meter does not see a change of the fake-frame state alone (KF-COUNT, the image-A twin's MO_FR): sound, since
   the seat's post state is a set_fs (Reusable/YG01.v stack_malloc_post) and the release is stack_free_state, a set_fs *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
Hypothesis HGRIG : gx_ok SEGS B (G_RIG B RG).
(* the register images of g_nsrc / g_src (PB_fr on AsanUbsan discharges both by vm_compute, as the image-A twin's
   HH44 / HH45) *)
Hypothesis HH41 : VAL (A_HI 41) = rg_nsrc RG + RIG_HI_NSRC.
Hypothesis HH42 : VAL (A_HI 42) = rg_src RG + RIG_HI_SRC.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are image bytes (so apart from the frames, the fake frame's shadow and the stack).  The pinned
   placement decides both by vm_compute at fr_globals, as W7's W_drain_cx.v HRGD / HGSB. *)
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
(* no read-only image byte is owned by the runtime (W_gesture_end.v's HROMO form): rom_view survives the stack
   allocator's calls (W_journal_x.v ajournal_gx_rom_view_x) *)
Hypothesis HROMO : rom_out SEGS B (G_RIG B RG).
(* the allocator instance's granule-tail fact (W7's ALLOC_TAIL over ARx, as W_drain_cx_x.v states it): a held key is
   represented over its |text| + 1 bytes (ruling (A)); a word read of a key to the end of its last granule is
   visible *)
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the runtime entries relay_instance_gone calls, at their SIGMA pcs, over ARx (W_sites_x.v / W_contract_x.v /
   W_journal_x.v Section hc; the free rule at the room record RP).  snprintf: a Theorem Labs lane's statement at fuzz_reply's
   addresses (W_sites.v asnprintf_realizes, its twin W_sites_x.v asnprintf_realizes_x), which the snprintf chain
   (RT_pf_vf.v snprintf_chain_ok, through a Theorem Labs lane's evt -> SRr bridge) discharges. *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis ASNPRINTF : asnprintf_realizes_x B ARx (SIGMA WS_snprintf) FR_GOT_GUARD FR_GUARD.
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
(* the program functions relay_instance_gone calls (W7's drain, W4's gesture_end), by their published _x room specs *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GE : ge_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gesture_end).
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* snprintf's stack-protector cells (see the header): the GOT word, a fact of every ARx state (at ARi0: the AR fact,
   am_const); the canary, image bytes *)
Hypothesis HGOTG : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  rdword (aview SEGS (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
(* the canary's bytes are image bytes (seg_rom SEGS at FR_GUARD .. + 8 is Some 0), so aview reads them in EVERY state
   through mbyte's seg_rom fallback: aguard_ok's second half needs nothing carried (a Theorem Labs lane's ruling; a Theorem Labs lane's
   pin measurement).  PB_fr decides it by vm_compute. *)
Hypothesis HCANR : forall a, FR_GUARD <= a < FR_GUARD + 8 -> seg_rom SEGS (Z_to_bv 64 a) <> None.
(* the two literals of the snprintf call, in W7's dlit_at form (W_drain_cx.v:175): the bytes in .rodata, read-only,
   their shadow as W3's ashp over ARx (never zero shadow: a literal's last granule is partial), the granule's tail
   bytes *)
Definition RIG_FMT : list Z := [37; 115; 32; 37; 100; 32].   (* "%s %d " *)
(* ashp_x is W_contract_x.v's twin of the kit's lib/B/W_shadow_pin.v ashp over ARx: range_addressable over exactly
   [a, a + n) and the shadow hull, in every ARx state *)
Definition glit_at_x (i : nat) (l : list Z) : Prop :=
(forall k, (k < length l)%nat ->
   seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ i) + Z.of_nat k)) = option_map (Z_to_bv 8) (nth_error l k)) /\
(forall x, VAL (A_OBJ i) <= x < VAL (A_OBJ i) + Z.of_nat (length l) -> YG0d.in_rom SEGS x) /\
ashp_x ARx (VAL (A_OBJ i)) (Z.of_nat (length l)) /\
(* the bytes after the literal's NUL to the end of its 8-byte granule are image bytes (snprintf's atail_vis and its
   "%s" argument read to the granule's end; found by BRigTop at 0x82eb8; PB_fr decides it by vm_compute) *)
(forall x, VAL (A_OBJ i) + Z.of_nat (length l) <= x <
   VAL (A_OBJ i) + Z.of_nat (length l) - 1 - (VAL (A_OBJ i) + Z.of_nat (length l) - 1) mod 8 + 8 ->
   seg_rom SEGS (Z_to_bv 64 x) <> None).
Hypothesis HLIT17 : glit_at_x 17 (RIG_FMT ++ [0]).
Hypothesis HLIT18 : glit_at_x 18 (RelayModel.K_GESTURE ++ [0]).
(* " end\0" (.str.4, A_lit_end5 = A_OBJ 28) in the same form, for gesture_end's / gestures_end's garr8 premise and its
   ashp (instance: W_shadow_pin_fr.v ashp_end5_5_fr): bytes, in_rom, ashp, the granule's tail; HEND5L above gives the
   bytes alone *)
Hypothesis HLIT28 : glit_at_x 28 ([32; 101; 110; 100] ++ [0]).
(* The program statics PST hold no byte this walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x, the literals and " end\0"), and no byte of the
   relay's and the output's global cells (G_RIG, and the cells of HRGP that G_RIG does not name: g_src, g_nsrc,
   g_capsrc, g_send_max, g_client, g_send_dead).  At PST := [] both hold trivially (image A's PSTR / PSTG). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a,
(inG (G_RIG B RG) a \/ rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
 rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
~ Exists (in_zr a) PST.

(* ---- The callees' journals, lifted to relay_instance_gone's globals: drain's at G_DR and gesture_end's at G_SL are
   journals at G_RIG (W_journal_x.v ajournal_gx_G_mono_x), for every call-making segment. ---- *)
Lemma rig_G_DR_RIG : forall a, inG (G_DR B RG) a -> inG (G_RIG B RG) a.
Proof. intros a Ha. unfold G_RIG, inG in *. apply Exists_cons_tl. exact Ha. Qed.
Lemma rig_G_SL_RIG : forall a, inG (G_SL B RG) a -> inG (G_RIG B RG) a.
Proof. intros a Ha. apply rig_G_DR_RIG. unfold G_DR, inG in *. apply Exists_cons_tl. exact Ha. Qed.
Lemma rig_lift_DR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_x; [exact rig_G_DR_RIG | eassumption]. Qed.
Lemma rig_lift_SL : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_SL B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_x; [exact rig_G_SL_RIG | eassumption]. Qed.

(* ---- The entry context: rig_spec_x's binders, with the entry's head set gxHp and its room budget gxkr. ---- *)
Record gcx : Type := mkGcx {
  gxregs : bvmap 5 word;
  gxly : alayout; gxS : astate; gxHp : list Z; gxW : world SEGS; gxmem : word -> option byte; gxmd : Model;
  gxch : list (Z * Z * Z);
  gxG0 : Z; gxID : Z; gxes : list rentry; gxhs : list (hsrc * nat);
  gxc : ctl; gxO : list byte; gxmx : Z; gxcap : Z; gxout : Z;
  gxrest : list (Z * Z); gxkr : nat }.

Definition gsp0 (cx : gcx) : Z := spZ (gxregs cx).
Definition gsp1 (cx : gcx) : Z := gsp0 cx - RIG_FRAME.
Definition gpre (cx : gcx) : list Z := relay_instance_gone_b_c.instance_prefix (gxID cx).
Definition gps (cx : gcx) : list (rentry * (hsrc * nat)) := combine (gxes cx) (gxhs cx).
Definition gnth (cx : gcx) (i : nat) : rentry := nth i (gxes cx) relay_remove_b_c.no_entry.
Definition ghj (cx : gcx) (i : nat) : hsrc * nat := nth i (gxhs cx) relay_instance_gone_b_c.no_hj.
Definition gslot (cx : gcx) (i : nat) : Z := rg_s RG + ASRC * Z.of_nat (snd (ghj cx i)).
Definition gSA (cx : gcx) (i : nat) : Z := gxG0 cx + AENT * Z.of_nat i.
Definition gFP (cx : gcx) : list (Z * Z) := rig_fp (gxG0 cx) (gxes cx) (gxhs cx) (gxcap cx) (gxout cx).
Definition gtr (cx : gcx) :=
rig_tr (gxc cx) (gxmx cx) (Z.of_nat (length (gxO cx))) (gxcap cx) (gxID cx) (gxes cx) (gxhs cx).
Definition ga0 : RelayRunT.addr YO0i.sptr := drain_b_c.da_out drain_b_c.dadr0.
(* the requests of the entries i .. from g_nout = no, g_capout = cap (rig_tr's run over the suffix) *)
Definition grest (cx : gcx) (i : nat) (no cap : Z) :=
relay_instance_gone_b_c.relay_instance_gone_tr (sl_live (gxc cx) 1) (gxmx cx) no cap (gpre cx)
  (skipn i (gxes cx)) (skipn i (gxhs cx)) (fun _ => ga0) 0 ga0.
(* the requests of ending the keys Er (gesture_end, free each), from g_nout = no, g_capout = cap *)
Definition gkrest (cx : gcx) (no cap : Z) (Er : list (Z * list byte * list byte)) :=
fst (keys_end_run (sl_live (gxc cx) 1) (gxmx cx) no cap
       (map (fun k => (Z.of_nat (length (key_text k)), ga0)) Er) 0 ga0).
Definition gPOST (cx : gcx) : world SEGS -> config -> Prop :=
rig_post_x B PST ARx MT RP RG (gxregs cx) (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx)
  (gxG0 cx) (gxID cx) (gxes cx) (gxhs cx) (gxc cx) (gxO cx) (gxmx cx) (gxcap cx) (gxout cx) (gxkr cx).

(* GBASE: exactly the kit's rig_spec_x premises at the entry (lib/B/W_contract_x.v rig_spec_x), with the
   Permutation's `rest` taken from the context, the room record's two premises at the entry's budget gxkr last. *)
Definition GBASE (cx : gcx) : Prop :=
afn_pre_x SEGS B ARx RIG_STK_x (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxregs cx) (gxmem cx) (gxmd cx) (gxch cx) /\
gsp0 cx mod 32 = 0 /\ count_cid 1 (frames (gxS cx)) < fs_frames 1 /\ rg_place B RG /\
getr (gxregs cx) 10 = w64 (gxID cx) /\ - 2 ^ 31 <= gxID cx < 2 ^ 31 /\
alock_at RG (gxW cx) (gxmem cx) false /\
arelay_at B RG (gxly cx) (gxS cx) (gxW cx) (gxmem cx) (gxG0 cx) (gxes cx) /\
aout_at B RG (gxly cx) (gxS cx) (gxW cx) (gxmem cx) (gxc cx) (gxO cx) (gxmx cx) (Z.of_nat (length (gxO cx)))
  (gxcap cx) (gxout cx) /\
rom_view SEGS (gxW cx) (gxmem cx) /\
length (gxhs cx) = length (gxes cx) /\
Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG (gxly cx) (gxS cx) (gxW cx) (gxmem cx) (fst p) (fst (snd p)) (snd (snd p)))
  (gps cx) /\
NoDup (rig_slots (gps cx)) /\
Permutation (ablocks B (gxly cx) (gxS cx))
  ((gxG0 cx, ATABLE) :: concat (map aentry_blks (gxes cx)) ++ rig_srcs (gps cx) ++ aout_blks (gxcap cx) (gxout cx) ++
   gxrest cx) /\
tr_max (gtr cx) < MMAX /\ blocks_bytes (gxS cx) + tr_peak (gtr cx) <= LIVE_MAX /\
mo_ok MT (gxS cx) (tr_cost MT (gtr cx)) /\
rp_RM RP (gxS cx) (Z.to_nat (tr_cost MT_rk (gtr cx)) + gxkr cx) /\
cnt_ok_pk RP (rig_pk (gtr cx)) (ablocks B (gxly cx) (gxS cx)).

(* GCTX: rig_spec's caller-context premise at the entry (the kit's B rig_spec, from W4Gesture-2 / BTrapKit's b_facts:
   pc + 792), read by KEY's free at 0x82fb4 (ra 0x82fb8 = entry + 0x318): 0x82fb8, then this entry's return and chain
   (image B's relay_instance_gone keeps a frame pointer: s0 = the entry sp, prologue `addi s0,sp,224`) *)
Definition GCTX (cx : gcx) : Prop :=
spZ (gxregs cx) + 16 < ly_top (gxly cx) /\ In (A_rig_entryP + 792 :: raZ (gxregs cx) :: spine (gxch cx)) CTX_AFREE.

(* ---- The frame. ----
   After the prologue: sp = the entry sp - 224 (the entry sp is 32-aligned), the thirteen callee-saved registers in
   their slots, the class-1 fake frame F at position fpos of the allocator's frame stack (the walk's OWN frame: GLIVE's
   journal carries own = [(1, fpos)]) with its flag cell FL in F's last word (F + 120: read by the release at
   0x83194), and the frame slots 8(sp), 16(sp), 112(sp) = F (the release reads 8 and 16) and 72(sp) = a0 at the entry
   (the id, as the register holds it). *)
Definition g_saved (cx : gcx) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
forall i, (i < 13)%nat ->
val_mem SEGS (arm W1 m1) (gsp1 cx + 120 + 8 * Z.of_nat i) 8 (bv_unsigned (getr (gxregs cx) (nth i RIG_SAVED 0%bv))).
Definition g_frame (cx : gcx) (fpos F FL : Z) (ly1 : alayout) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
frame_addr ly1 1 fpos = F /\ flag_addr ly1 1 fpos = FL /\
val_mem SEGS (arm W1 m1) (F + 120) 8 FL /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 8) 8 F /\ val_mem SEGS (arm W1 m1) (gsp1 cx + 16) 8 F /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 112) 8 F /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 72) 8 (bv_unsigned (getr (gxregs cx) 10)) /\
g_saved cx W1 m1.
(* the loop's frame slots (0x82dd0, 0x82de0-0x82e18): 24(sp) = g_src's register image, 32(sp) = 0x7fffffff,
   40(sp) = F's shadow, 48(sp) = "param_gesture" (.str.6, A_OBJ 18), 56(sp) = the format (.str.9, A_OBJ 17),
   64(sp) = g_nsrc's register image, 88(sp) = F + 32 (the prefix buffer) *)
Definition g_lslots (cx : gcx) (F : Z) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
val_mem SEGS (arm W1 m1) (gsp1 cx + 24) 8 (rg_src RG + RIG_HI_SRC) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 32) 8 0x7fffffff /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 40) 8 (shadow_addr F) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 48) 8 (VAL (A_OBJ 18)) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 56) 8 (VAL (A_OBJ 17)) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 64) 8 (rg_nsrc RG + RIG_HI_NSRC) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 88) 8 (F + 32).

(* The registers every cut after the prologue holds: sp, gp, tp, s0 = the entry sp, s1 = sp, s5 = the shadow
   offset (ld from the GOT at 0x82cfc). *)
Definition gregs_base (cx : gcx) (regs1 : bvmap 5 word) : Prop :=
spZ regs1 = gsp1 cx /\
getr regs1 3 = getr (gxregs cx) 3 /\ getr regs1 4 = getr (gxregs cx) 4 /\
getr regs1 8 = w64 (gsp0 cx) /\ getr regs1 9 = w64 (gsp1 cx) /\
getr regs1 21 = w64 SHADOW_OFF.

(* ---- What holds while the lock is held: the journal from the entry (at G_RIG, RIG_STK_x, rig_fp; from the entry's
   head set gxHp to the cut's Hp1) owning the fake frame (1, fpos), the .rodata view, the presence of image bytes, the
   frame and g_lock held. ---- *)
Definition GLIVE (cx : gcx) (F FL : Z) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte)
(md1 : Model) (k1 : Z) : Prop :=
exists fpos Hp1,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 /\
rom_view SEGS W1 m1 /\ apres_kept B (gxW cx) (gxmem cx) W1 m1 /\
g_frame cx fpos F FL ly1 W1 m1 /\
alock_at RG W1 m1 true.

(* The meter: `spent` charged so far, tl still to come (W_drain_cx.v dbud); and the room round's two facts over tl
   (W_drain_cx_x.v dbud_x's form): the room at the cut's allocator state for MT_rk's count of the requests still owed
   on top of the entry's budget gxkr, and the live counts at the cut plus rig_pk's shape over those requests (their
   own peak count tr_peakP plus 3, the largest premise constant of an inner callee: gesture_end's ge_pk; drain's
   dr_pk is its trace's peak plus 2, W_contract_x.v dr_pk). *)
Definition gbud (cx : gcx) (ly1 : alayout) (S1 : astate) (spent : Z) (tl : list (RelayRunT.rev YO0i.sptr)) : Prop :=
mo_le MT (gxS cx) S1 spent /\ 0 <= spent /\
spent + tr_cost MT tl <= tr_cost MT (gtr cx) /\
blocks_bytes S1 + tr_peak tl <= LIVE_MAX /\
tr_max tl < MMAX /\
rp_RM RP S1 (Z.to_nat (tr_cost MT_rk tl) + gxkr cx) /\
cnt_ok_pk RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P tl) + 3)%nat) (ablocks B ly1 S1).

(* The harness sources of the entries done, as rig_post states them. *)
Definition gdone_srcs (ps : list (rentry * (hsrc * nat))) (qd : list (rentry * hsrc)) : list (Z * Z) :=
concat (map (fun p => if re_eof (fst (fst p)) =? 0 then asrc_blks (snd (snd p)) else []) (combine ps qd)).

(* GOUT i: entries 0 .. i-1 done (qd: each with its harness source after), the stream at (c2, O2, cap2, out2);
   entries i .. as at the entry, with drain's source facts at the current state. *)
Definition GOUT (cx : gcx) (i : nat) (qd : list (rentry * hsrc)) (c2 : ctl) (O2 : list byte) (cap2 out2 : Z)
(spent : Z) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
(i <= length (gxes cx))%nat /\ length qd = i /\
rig_rel (gpre cx) (gxmx cx) (gxc cx) (gxO cx) (gxcap cx) (firstn i (gps cx)) qd c2 O2 cap2 /\
arelay_at B RG ly1 S1 W1 m1 (gxG0 cx) (map fst qd ++ skipn i (gxes cx)) /\
aout_at B RG ly1 S1 W1 m1 c2 O2 (gxmx cx) (Z.of_nat (length O2)) cap2 out2 /\
(forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
   asrc_at B ly1 S1 W1 m1 (gslot cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly1 S1 W1 m1 (fst p) (fst (snd p)) (snd (snd p)))
  (skipn i (gps cx)) /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
   (forall j, In j (rig_slots (firstn i (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
   abyte_kept (gxW cx) (gxmem cx) W1 m1 a) /\
Permutation (ablocks B ly1 S1)
  ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ skipn i (gxes cx))) ++
   gdone_srcs (firstn i (gps cx)) qd ++ rig_srcs (skipn i (gps cx)) ++ aout_blks cap2 out2 ++ gxrest cx) /\
gbud cx ly1 S1 spent (grest cx i (Z.of_nat (length O2)) cap2).

(* What drain leaves of entry e (at stream (cB, OB, capB)) and its source h: e1, h1, the stream (c1, O1, cap1); the
   let-bindings of W_contract.v rig_rel, named. *)
Definition gdrained (cx : gcx) (cB : ctl) (OB : list byte) (capB : Z) (e : rentry) (h : hsrc)
(e1 : rentry) (h1 : hsrc) (ev : Z) (LB : list byte) (c1 : ctl) (O1 : list byte) (cap1 : Z) : Prop :=
let open := re_eof e =? 0 in
let no := Z.of_nat (length OB) in
let live := open && dr_live cB h in
c1 = (if open then dr_ctl cB h ev else cB) /\
O1 = (if live then OB ++ LB else OB) /\
cap1 = (if live then drain_b_c.ds_ocap (dr_fin cB (gxmx cx) no capB e h) else capB) /\
(if open then dr_rel cB (gxmx cx) no capB e h e1 h1 LB else e1 = e /\ h1 = h).

(* GIN: inside entry i (i < |es|).  Entries 0 .. i-1 done (qd, stream (cB, OB, capB): GOUT i's rig_rel); entry i
   drained (gdrained: e1, h1, the stream (c1, O1, cap1)); of its held keys, Ed ended so far, ks held now (the table's
   entry i is entry_keys e1 ks), the stream after Ed at (c2, O2, cap2, out2); geik's run from index n over ks (fuel f)
   ends what is left.  |ks| = n + S r: every KEY step lowers r by one (a pass raises n, an end shortens ks), which is
   the inner loop's measure.  The prefix and its zero shadow are in the fake frame. *)
Definition GIN (cx : gcx) (i n r : nat) (F : Z) (qd : list (rentry * hsrc)) (cB : ctl) (OB : list byte) (capB : Z)
(e1 : rentry) (h1 : hsrc) (ev : Z) (LB : list byte) (c1 : ctl) (O1 : list byte) (cap1 : Z)
(ks Ed : list (Z * list byte * list byte)) (f : nat) (c2 : ctl) (O2 : list byte) (cap2 out2 : Z)
(spent : Z) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
let e := gnth cx i in
let h := fst (ghj cx i) in
let open := re_eof e =? 0 in
let Er := fst (geik_loop f (gpre cx) n ks) in
(i < length (gxes cx))%nat /\ length qd = i /\
rig_rel (gpre cx) (gxmx cx) (gxc cx) (gxO cx) (gxcap cx) (firstn i (gps cx)) qd cB OB capB /\
gdrained cx cB OB capB e h e1 h1 ev LB c1 O1 cap1 /\
sl_sends (gxmx cx) c1 O1 cap1 (ge_bytes Ed) = (c2, O2, cap2) /\
length ks = (n + S r)%nat /\ (length ks - n <= f)%nat /\
geik (gpre cx) (re_keys e1) = (Ed ++ Er, snd (geik_loop f (gpre cx) n ks)) /\
arelay_at B RG ly1 S1 W1 m1 (gxG0 cx) (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx)) /\
aout_at B RG ly1 S1 W1 m1 c2 O2 (gxmx cx) (Z.of_nat (length O2)) cap2 out2 /\
(forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
   asrc_at B ly1 S1 W1 m1 (gslot cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
(open = true -> asrc_at B ly1 S1 W1 m1 (gslot cx i) h1) /\
Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly1 S1 W1 m1 (fst p) (fst (snd p)) (snd (snd p)))
  (skipn (S i) (gps cx)) /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
   (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
   abyte_kept (gxW cx) (gxmem cx) W1 m1 a) /\
Permutation (ablocks B ly1 S1)
  ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx))) ++
   gdone_srcs (firstn i (gps cx)) qd ++ (if open then asrc_blks h1 else []) ++ rig_srcs (skipn (S i) (gps cx)) ++
   aout_blks cap2 out2 ++ gxrest cx) /\
garr8 SEGS (arm W1 m1) (F + 32) (gpre cx ++ [0]) /\
garr8 SEGS (arm W1 m1) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0] /\
(let '(_, O3, cap3) := sl_sends (gxmx cx) c2 O2 cap2 (ge_bytes Er) in
 gbud cx ly1 S1 spent (gkrest cx (Z.of_nat (length O2)) cap2 Er ++ grest cx (S i) (Z.of_nat (length O3)) cap3)).

(* ---- The cut predicates. ---- *)

(* RGO i (0x82e1c): the outer loop's head at entry i < |es|.  s4 = F's shadow, s6 = i, s7 = g_src's register
   image. *)
Definition RGO (cx : gcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_outer) regs1 m1 md1 /\
gregs_base cx regs1 /\
getr regs1 20 = w64 (shadow_addr F) /\ getr regs1 22 = w64 (Z.of_nat i) /\
getr regs1 23 = w64 (rg_src RG + RIG_HI_SRC) /\
(i < length (gxes cx))%nat /\
GLIVE cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots cx F W1 m1 /\
GOUT cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.

(* RGI i n r (0x82f08): the inner loop's head at index n of entry i (SA = g_src + 56 i), nheld = n + S r.
   s3 = s6 = 8 n, s4 = n, s7 = &s->nheld (SA + 48) and s11 its shadow address, s8 = |prefix| (strlen's result),
   s9 = &s->held (SA + 40) and s2 its shadow address; 80(sp) = i (0x82e84). *)
Definition RGI (cx : gcx) (i n r : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd cB OB capB e1 h1 ev LB c2' O1 cap1 ks Ed f c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_inner) regs1 m1 md1 /\
gregs_base cx regs1 /\
getr regs1 19 = w64 (8 * Z.of_nat n) /\ getr regs1 22 = w64 (8 * Z.of_nat n) /\ getr regs1 20 = w64 (Z.of_nat n) /\
getr regs1 23 = w64 (gSA cx i + 48) /\ getr regs1 27 = w64 (SHADOW_OFF + (gSA cx i + 48) / 8) /\
getr regs1 24 = w64 (Z.of_nat (length (gpre cx))) /\
getr regs1 25 = w64 (gSA cx i + 40) /\ getr regs1 18 = w64 (SHADOW_OFF + (gSA cx i + 40) / 8) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 80) 8 (Z.of_nat i) /\
GLIVE cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots cx F W1 m1 /\
GIN cx i n r F qd cB OB capB e1 h1 ev LB c2' O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1.

(* RGE i (0x830c4): entry i done (GOUT (S i)); 80(sp) = i. *)
Definition RGE (cx : gcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_step) regs1 m1 md1 /\
gregs_base cx regs1 /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 80) 8 (Z.of_nat i) /\
(i < length (gxes cx))%nat /\
GLIVE cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots cx F W1 m1 /\
GOUT cx (S i) qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.

(* RGU (0x8312c): every entry done (GOUT |es|; the empty table included).  s4 = F's shadow. *)
Definition RGU (cx : gcx) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_unlock) regs1 m1 md1 /\
gregs_base cx regs1 /\ getr regs1 20 = w64 (shadow_addr F) /\
GLIVE cx F FL ly1 S1 W1 m1 md1 k1 /\
GOUT cx (length (gxes cx)) qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.

(* ---- The segment statements. ---- *)

(* PRO: the prologue 0x82ca0 .. 0x82dbc (thirteen saves, the id at 72(sp), the uar test, __asan_stack_malloc_1 (128)
   0x82d0c, the frame header and its shadow poison), pthread_mutex_lock (g_lock) 0x82dc8, g_nsrc <= 0 0x82dd8
   (-> RGU) and the loop's setup 0x82ddc-0x82e18 (-> RGO 0). *)
Definition rig_pro_stmt : Prop :=
forall cx,
GBASE cx ->
(forall W2 c2, RGO cx 0 W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
(forall W2 c2, RGU cx W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
SRr SEGS (gxW cx) (cfg_at SEGS A_rig_entryP (gxregs cx) (gxmem cx) (gxmd cx)) (gPOST cx).

(* TOP: RGO i 0x82e1c -> g_src + 56 i and its traps (0x82e38-0x82e48), the shadow check of s->eof (0x82e4c-0x82e5c;
   0x83108-0x83110, report 0x83270 NOT taken), drain (s) when s->eof = 0 (0x82e68), g_src reloaded and checked
   (0x82e6c-0x82e80), 80(sp) = i, F's shadow bytes 4 .. 9 = 0 (0x82e88-0x82e9c), snprintf (F + 32, 48, "%s %d ",
   "param_gesture", id) (0x82eb8), strlen (F + 32) (0x82ec0), the traps 0x82ec4-0x82ecc, the shadow check of s->nheld
   (0x82ed8-0x82ee4; 0x83118-0x83120, report 0x83128 NOT taken) and the nheld test 0x82eec: nheld > 0 -> the inner
   loop's setup 0x82ef0-0x82f04 -> RGI i 0 r (nheld = S r); nheld <= 0 -> RGE i. *)
Definition rig_top_stmt : Prop :=
forall cx i W1 c1,
GBASE cx -> RGO cx i W1 c1 ->
(forall r W2 c2, RGI cx i 0 r W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
(forall W2 c2, RGE cx i W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
SRr SEGS W1 c1 (gPOST cx).

(* KEY: RGI i n r 0x82f08 -> the shadow check of s->held (0x82f08-0x82f0c), held + 8 n and its traps
   (0x82f14-0x82f38), the shadow check of held[n] (0x82f3c-0x82f48), key = held[n], strncmp (key, prefix, |prefix|)
   (0x82f5c):
   - nonzero (0x83098-0x830ac): nheld reread (its shadow check, slow path 0x830b4-0x830bc NOT reporting), n += 1,
     n < nheld (r = S r') -> through 0x82f04 (s6 = 8 n) -> RGI i (S n) r', else (r = 0) -> RGE i;
   - zero: gesture_end (key) (0x82f68), the checks again (0x82f6c-0x82fac), free (key) (0x82fb4), nheld -= 1 with its
     int32 trap (0x82fcc-0x82fd4), held[n] = held[nheld] (0x83050; its checks 0x82fd8-0x83048, the WRAP check
     `not a2,a1; bltu a2,s3` 0x83028-0x8302c among them): n < nheld (r = S r') -> RGI i n r' (the last key moved into
     slot n), else (r = 0) -> RGE i. *)
Definition rig_key_stmt : Prop :=
forall cx i n r W1 c1,
GBASE cx -> GCTX cx -> RGI cx i n r W1 c1 ->
(forall r' W2 c2, r = S r' -> RGI cx i (S n) r' W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
(forall r' W2 c2, r = S r' -> RGI cx i n r' W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
(forall W2 c2, RGE cx i W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
SRr SEGS W1 c1 (gPOST cx).

(* KEYS: the inner loop, by induction on r. *)
Definition rig_keys_stmt : Prop :=
rig_key_stmt ->
forall cx i n r W1 c1,
GBASE cx -> GCTX cx -> RGI cx i n r W1 c1 ->
(forall W2 c2, RGE cx i W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
SRr SEGS W1 c1 (gPOST cx).

(* STEP: RGE i 0x830c4 -> F's shadow bytes 4 .. 9 = 0xf8 again (0x830c8-0x830e0), i's int32 bound (0x830ec, the trap
   NOT taken: i < |es| <= 16), g_nsrc reread, i + 1 < g_nsrc -> RGO (S i), else -> RGU.  No call. *)
Definition rig_step_stmt : Prop :=
forall cx i W1 c1,
GBASE cx -> RGE cx i W1 c1 ->
(forall W2 c2, RGO cx (S i) W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
(forall W2 c2, RGU cx W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
SRr SEGS W1 c1 (gPOST cx).

(* OUTER: the outer loop, by induction on |es| - i (KEY is passed to KEYS). *)
Definition rig_outer_stmt : Prop :=
rig_top_stmt -> rig_key_stmt -> rig_keys_stmt -> rig_step_stmt ->
forall cx i W1 c1,
GBASE cx -> GCTX cx -> RGO cx i W1 c1 ->
(forall W2 c2, RGU cx W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
SRr SEGS W1 c1 (gPOST cx).

(* TAIL: RGU 0x8312c -> pthread_mutex_unlock (g_lock) (0x83134), the frame's release 0x83138-0x8319c (retired
   magic, shadow 0xf5, *flag = 0) and the epilogue 0x831e0 -> rig_post. *)
Definition rig_tail_stmt : Prop :=
forall cx W1 c1,
GBASE cx -> RGU cx W1 c1 ->
SRr SEGS W1 c1 (gPOST cx).

(* The walk: the segments give relay_instance_gone's generic contract.  The kit's B rig_spec_x takes
   `spZ regs + 16 < ly_top ly -> In (pc + 792 :: raZ regs :: spine ch) CTX_AFREE` LAST; W_rig_all.v takes the two
   premises into GCTX (as image A's W_rig_all.v does). *)
Definition rig_all_stmt : Prop :=
rig_pro_stmt -> rig_top_stmt -> rig_key_stmt -> rig_step_stmt -> rig_keys_stmt -> rig_outer_stmt -> rig_tail_stmt ->
rig_spec_x B PST ARx MT RP MMAX RG CTX_AFREE A_rig_entryP.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): this Section's texts at a world relation R.  Each <name>_xR below is <name>
   with the journal ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, rig_post_x / rig_spec_x -> a Theorem Labs lane's
   rig_post_xR / rig_spec_xR (W_contract_xR_relayB.v, R right after ARx), and every carrier or statement it names -> its
   R twin; every other token is the strict text's.  At R := wle each is its strict twin by conversion.  The Section's
   hypotheses add, for the segment walks that copy them: the R laws, the free rule at R (afree_cf_rule_c_xR, with its
   call-boundary fact RO read off ARx) and the two callees' R specs (W_contract_xR.v dr_spec_xR / ge_spec_xR).
   GBASE, GCTX, GOUT, GIN, gbud, g_frame, g_lslots, gregs_base name no journal and no step relation and are shared.
   Image A's twin: lib/A/W_relay_instance_gone_cx.v Section wR. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Hypothesis DRAIN_R : dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GE_R : ge_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gesture_end).
(* W_relay_instance_gone_cx.v:262 rig_lift_DR at R *)
Lemma rig_lift_DR_xR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_xR; [exact rig_G_DR_RIG | eassumption]. Qed.
(* W_relay_instance_gone_cx.v:266 rig_lift_SL at R *)
Lemma rig_lift_SL_xR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_SL B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_xR; [exact rig_G_SL_RIG | eassumption]. Qed.
(* W_relay_instance_gone_cx.v:300 gPOST at R *)
Definition gPOST_xR (cx : gcx) : world SEGS -> config -> Prop :=
rig_post_xR B PST ARx R MT RP RG (gxregs cx) (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx)
  (gxG0 cx) (gxID cx) (gxes cx) (gxhs cx) (gxc cx) (gxO cx) (gxmx cx) (gxcap cx) (gxout cx) (gxkr cx).
(* W_relay_instance_gone_cx.v:372 GLIVE at R *)
Definition GLIVE_xR (cx : gcx) (F FL : Z) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte)
(md1 : Model) (k1 : Z) : Prop :=
exists fpos Hp1,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 /\
rom_view SEGS W1 m1 /\ apres_kept B (gxW cx) (gxmem cx) W1 m1 /\
g_frame cx fpos F FL ly1 W1 m1 /\
alock_at RG W1 m1 true.
(* W_relay_instance_gone_cx.v:472 RGO at R *)
Definition RGO_xR (cx : gcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_outer) regs1 m1 md1 /\
gregs_base cx regs1 /\
getr regs1 20 = w64 (shadow_addr F) /\ getr regs1 22 = w64 (Z.of_nat i) /\
getr regs1 23 = w64 (rg_src RG + RIG_HI_SRC) /\
(i < length (gxes cx))%nat /\
GLIVE_xR cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots cx F W1 m1 /\
GOUT cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.
(* W_relay_instance_gone_cx.v:485 RGI at R *)
Definition RGI_xR (cx : gcx) (i n r : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd cB OB capB e1 h1 ev LB c2' O1 cap1 ks Ed f c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_inner) regs1 m1 md1 /\
gregs_base cx regs1 /\
getr regs1 19 = w64 (8 * Z.of_nat n) /\ getr regs1 22 = w64 (8 * Z.of_nat n) /\ getr regs1 20 = w64 (Z.of_nat n) /\
getr regs1 23 = w64 (gSA cx i + 48) /\ getr regs1 27 = w64 (SHADOW_OFF + (gSA cx i + 48) / 8) /\
getr regs1 24 = w64 (Z.of_nat (length (gpre cx))) /\
getr regs1 25 = w64 (gSA cx i + 40) /\ getr regs1 18 = w64 (SHADOW_OFF + (gSA cx i + 40) / 8) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 80) 8 (Z.of_nat i) /\
GLIVE_xR cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots cx F W1 m1 /\
GIN cx i n r F qd cB OB capB e1 h1 ev LB c2' O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1.
(* W_relay_instance_gone_cx.v:498 RGE at R *)
Definition RGE_xR (cx : gcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_step) regs1 m1 md1 /\
gregs_base cx regs1 /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 80) 8 (Z.of_nat i) /\
(i < length (gxes cx))%nat /\
GLIVE_xR cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots cx F W1 m1 /\
GOUT cx (S i) qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.
(* W_relay_instance_gone_cx.v:508 RGU at R *)
Definition RGU_xR (cx : gcx) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_unlock) regs1 m1 md1 /\
gregs_base cx regs1 /\ getr regs1 20 = w64 (shadow_addr F) /\
GLIVE_xR cx F FL ly1 S1 W1 m1 md1 k1 /\
GOUT cx (length (gxes cx)) qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.
(* W_relay_instance_gone_cx.v:520 rig_pro_stmt at R *)
Definition rig_pro_stmt_xR : Prop :=
forall cx,
GBASE cx ->
(forall W2 c2, RGO_xR cx 0 W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
(forall W2 c2, RGU_xR cx W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
SRrG SEGS R (gxW cx) (cfg_at SEGS A_rig_entryP (gxregs cx) (gxmem cx) (gxmd cx)) (gPOST_xR cx).
(* W_relay_instance_gone_cx.v:533 rig_top_stmt at R *)
Definition rig_top_stmt_xR : Prop :=
forall cx i W1 c1,
GBASE cx -> RGO_xR cx i W1 c1 ->
(forall r W2 c2, RGI_xR cx i 0 r W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
(forall W2 c2, RGE_xR cx i W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
SRrG SEGS R W1 c1 (gPOST_xR cx).
(* W_relay_instance_gone_cx.v:549 rig_key_stmt at R *)
Definition rig_key_stmt_xR : Prop :=
forall cx i n r W1 c1,
GBASE cx -> GCTX cx -> RGI_xR cx i n r W1 c1 ->
(forall r' W2 c2, r = S r' -> RGI_xR cx i (S n) r' W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
(forall r' W2 c2, r = S r' -> RGI_xR cx i n r' W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
(forall W2 c2, RGE_xR cx i W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
SRrG SEGS R W1 c1 (gPOST_xR cx).
(* W_relay_instance_gone_cx.v:558 rig_keys_stmt at R *)
Definition rig_keys_stmt_xR : Prop :=
rig_key_stmt_xR ->
forall cx i n r W1 c1,
GBASE cx -> GCTX cx -> RGI_xR cx i n r W1 c1 ->
(forall W2 c2, RGE_xR cx i W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
SRrG SEGS R W1 c1 (gPOST_xR cx).
(* W_relay_instance_gone_cx.v:567 rig_step_stmt at R *)
Definition rig_step_stmt_xR : Prop :=
forall cx i W1 c1,
GBASE cx -> RGE_xR cx i W1 c1 ->
(forall W2 c2, RGO_xR cx (S i) W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
(forall W2 c2, RGU_xR cx W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
SRrG SEGS R W1 c1 (gPOST_xR cx).
(* W_relay_instance_gone_cx.v:575 rig_outer_stmt at R *)
Definition rig_outer_stmt_xR : Prop :=
rig_top_stmt_xR -> rig_key_stmt_xR -> rig_keys_stmt_xR -> rig_step_stmt_xR ->
forall cx i W1 c1,
GBASE cx -> GCTX cx -> RGO_xR cx i W1 c1 ->
(forall W2 c2, RGU_xR cx W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
SRrG SEGS R W1 c1 (gPOST_xR cx).
(* W_relay_instance_gone_cx.v:584 rig_tail_stmt at R *)
Definition rig_tail_stmt_xR : Prop :=
forall cx W1 c1,
GBASE cx -> RGU_xR cx W1 c1 ->
SRrG SEGS R W1 c1 (gPOST_xR cx).
(* W_relay_instance_gone_cx.v:592 rig_all_stmt at R *)
Definition rig_all_stmt_xR : Prop :=
rig_pro_stmt_xR -> rig_top_stmt_xR -> rig_key_stmt_xR -> rig_step_stmt_xR -> rig_keys_stmt_xR -> rig_outer_stmt_xR -> rig_tail_stmt_xR ->
rig_spec_xR B PST ARx R MT RP MMAX RG CTX_AFREE A_rig_entryP.
End wR.
(* at R := wle the R texts are the strict ones (conversion) *)
Lemma gPOST_wle : gPOST = gPOST_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma GLIVE_wle : GLIVE = GLIVE_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RGO_wle : RGO = RGO_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RGI_wle : RGI = RGI_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RGE_wle : RGE = RGE_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RGU_wle : RGU = RGU_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_pro_stmt_wle : rig_pro_stmt = rig_pro_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_top_stmt_wle : rig_top_stmt = rig_top_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_key_stmt_wle : rig_key_stmt = rig_key_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_keys_stmt_wle : rig_keys_stmt = rig_keys_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_step_stmt_wle : rig_step_stmt = rig_step_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_outer_stmt_wle : rig_outer_stmt = rig_outer_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_tail_stmt_wle : rig_tail_stmt = rig_tail_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_all_stmt_wle : rig_all_stmt = rig_all_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
End c.
End b.
End a.
