(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE-B segment KEY of fuzz_reply's relay_instance_gone: the symbolic seat of the
   inner loop's body (fuzz_reply.asan-ubsan 0x82f08 and gesture_end's return 0x82f6c; B's register map, lib/B/W_traps.v
   seat recipe R1-R5).  Proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record); the image-A twin is
   a Theorem Labs lane's RIG_x round, commit f4cd818e98d, lib/A/W_rig_key.v's rk_shok / rk_st_gen): the seats over any allocator
   relation ARx, against the cx file's generic Section (copied below).  Each seat reads its allocator state at the
   empty head set (HP0: ARh below, the image-A twin's technique, with Local helpers): the block facts by alx_blocks and
   BLKN (rk_alb), the shadow ranges by W_journal_x.v range_addressable_of_block_hp0_x (rk_rab). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_instance_gone_b_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_instance_gone_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_traps.
(* route R: a Theorem Labs lane's dr_spec_xR / ge_spec_xR, SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).


(* ---- The seat at the inner loop's head (RGI, 0x82f08) and at gesture_end's return (0x82f6c): B's registers
   s1 = sp (atom 9), s5 = SHADOW_OFF (atom 21), s3 = 8 n (atom 19; s6 = r22 pinned to the same atom), s4 = n (atom 20),
   s7 = SA + 48 (atom 23) and s11 its shadow address, s9 = SA + 40 (atom 25) and s2 its shadow address (formulas over
   atom 21); held = hp (atom 32), held + 8 n (atom 33, both sum orders aliased: `add a1,s3,a0` 0x82f14 and
   `add a0,a0,s6` 0x82f30), held[n] = the key (atom 34), nheld (atom 35), 88(sp) = F + 32 (atom 36).  The WRAP check
   0x82f18 `bltu held + 8 n, held` (lib/B/W_traps.v R5) is seated as the condition held + 8 n >=u held, so the runner
   decides it and its copy 0x82f7c. ---- *)
Definition rk_sh (b : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff b 0) (SLit 3)) (SOff 21 0).
Definition rk_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 18%bv (rk_sh 25)) 27%bv (rk_sh 23)) 22%bv (SOff 19 0).
Definition rk_regions : smem :=
[ YP09.mkRegion (Some 25%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 23%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))];
  YP09.mkRegion (Some 33%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))];
  YP09.mkRegion (Some 9%nat) 88 96 88 88 [YP09.mkChunk 88 (CVal 8 (SOff 36 0))] ].
Definition PTRK (al : Z) : afact := mkAF 4096 140737479966720 al.
Definition rk_atoms : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF (2^46) (2^47) 4); (21%nat, mkAF SB SB 0);
  (19%nat, mkAF 0 (2^29) 3); (20%nat, mkAF 0 (2^26) 0);
  (23%nat, PTRK 3); (25%nat, PTRK 3); (32%nat, PTRK 3); (33%nat, PTRK 3); (34%nat, PTRK 0);
  (35%nat, mkAF 1 (2^26) 0); (36%nat, PTRK 0) ].
Definition rk_conds : list acond := [mkAC BC_GEU (SOff 33 0) (SOff 32 0)].
Definition rk_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 32 0) (SOff 19 0), SOff 33 0); (SAlu ALU_ADD (SOff 19 0) (SOff 32 0), SOff 33 0) ].
Definition rk_facts : facts := mkFacts rk_atoms rk_conds rk_alias.
Definition ss_k (pc : Z) : sstate := mkSS pc rk_regs rk_regions None rk_facts.
Definition rk_SH : list shent := [ mkSHE 25 0 8; mkSHE 23 0 8; mkSHE 33 0 8 ].
Definition rk_Bx : sv := SOff 21 0.
Definition rk_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rk_extra (hp hpn key nh f32 : Z) : list word := map (Z_to_bv 64) [hp; hpn; key; nh; f32].
Definition A_rig_ge_ret : Z := A_rig_inner + 0x64.    (* 0x82f6c: gesture_end's return address *)
Definition A_rig_fr_ret : Z := A_rig_inner + 0xb0.    (* 0x82fb8: free's return address *)



(* ---- The seat at free's return (0x82fb8): the move held[n] = held[nheld - 1] and nheld - 1 are stored by the run
   (write windows on nheld and on held[n]).  held + 8 (nheld - 1), the engine's `(held - 8) + (nheld << 3)` (0x82fe4),
   is atom 36 (read-only held[nheld - 1] = klast, atom 37) when n < nheld - 1 (rk3a), and atom 33 itself when
   n = nheld - 1 (rk3b: the last key moves onto itself). ---- *)
Definition rk3_hpl_sv : sv := SAlu ALU_ADD (SOff 32 (-8)) (SAlu ALU_SLL (SOff 35 0) (SLit 3)).
Definition rk3a_regions : smem :=
[ YP09.mkRegion (Some 25%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 23%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))];
  YP09.mkRegion (Some 33%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))];
  YP09.mkRegion (Some 36%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 37 0))] ].
Definition rk3b_regions : smem :=
[ YP09.mkRegion (Some 25%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 23%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))];
  YP09.mkRegion (Some 33%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))] ].
Definition rk3_atoms (nlo : Z) : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF (2^46) (2^47) 4); (21%nat, mkAF SB SB 0);
  (19%nat, mkAF 0 (2^29) 3); (20%nat, mkAF 0 (2^26) 0);
  (23%nat, PTRK 3); (25%nat, PTRK 3); (32%nat, PTRK 3); (33%nat, PTRK 3); (34%nat, PTRK 0);
  (35%nat, mkAF nlo (2^26) 0); (36%nat, PTRK 3); (37%nat, PTRK 0) ].
Definition rk3a_facts : facts := mkFacts (rk3_atoms 2) rk_conds (rk_alias ++ [(rk3_hpl_sv, SOff 36 0)]).
Definition rk3b_facts : facts := mkFacts (rk3_atoms 1) rk_conds (rk_alias ++ [(rk3_hpl_sv, SOff 33 0)]).
Definition ss_k3a (pc : Z) : sstate := mkSS pc rk_regs rk3a_regions None rk3a_facts.
Definition ss_k3b (pc : Z) : sstate := mkSS pc rk_regs rk3b_regions None rk3b_facts.
Definition rk3_SH : list shent := [ mkSHE 25 0 8; mkSHE 23 0 8; mkSHE 33 0 8; mkSHE 36 0 8 ].
Definition rk_extra3 (hp hpn key nh hpl klast : Z) : list word := map (Z_to_bv 64) [hp; hpn; key; nh; hpl; klast].

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
(* ---- The Section hypotheses of lib/B/W_relay_instance_gone_cx.v, copied (the names are the contracts'). ---- *)
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
(* RIG_FMT and glit_at_x (ashp over ARx, W_contract_x.v ashp_x) are the cx file's definitions *)
Hypothesis HLIT17 : glit_at_x ARx 17 (RIG_FMT ++ [0]).
Hypothesis HLIT18 : glit_at_x ARx 18 (RelayModel.K_GESTURE ++ [0]).
(* " end\0" (.str.4, A_lit_end5 = A_OBJ 28) in the same form, for gesture_end's / gestures_end's garr8 premise and its
   ashp (instance: W_shadow_pin_fr.v ashp_end5_5_fr): bytes, in_rom, ashp, the granule's tail; HEND5L above gives the
   bytes alone *)
Hypothesis HLIT28 : glit_at_x ARx 28 ([32; 101; 110; 100] ++ [0]).
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

#[local] Set Default Proof Using "All".

(* ==== the generic relation at the empty head set (the image-A twin's lib/A/W_rig_key.v:236-280; Local here, as every
   key file that needs them defines its own) ==== *)
(* HP0: every ARx state a seat reads has the head set [], so the seats state it at ARh (= ARx at []).  rk_alb is
   AR_blocks_law's seven conjuncts (alx_blocks' six and BLKN), in the AR walk's argument order. *)
#[local] Notation ARh ly S W mem md := (ARx ly S (@nil Z) W mem md).
Local Lemma rk_alb : forall ly S W mem md p n, ARh ly S W mem md -> In (p, n) (ablocks B ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\ 0 <= n.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (BLKN ly S [] W mem md p n HAR Hin))))))).
Qed.
Local Definition rk_rab ly S W mem md p m a n (H : ARh ly S W mem md) :=
  range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S [] W mem md p m a n H.

Lemma rk_sh_den : forall E b x, ew E b = w64 x -> ew E 21 = w64 SHADOW_OFF -> 0 <= x < 2 ^ 60 ->
sv_denot E (rk_sh b) = w64 (SHADOW_OFF + x / 8).
Proof.
intros E b x Hb E21 Hx. unfold rk_sh. cbn [sv_denot]. rewrite Hb, E21, !Z.add_0_r, !Z_to_bv_bv_unsigned.
assert (H8 : 0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (x / 8) (2 ^ 64)) by lia. rewrite Z.add_comm. apply Z.mod_small. unfold SHADOW_OFF. lia.
Qed.

(* the three shadow entries, at any memory where the table and the held array are live blocks *)
Lemma rk_shok : forall E W ly S m md SA G0 hp kh n nh,
ARh ly S W m md ->
ew E 21 = w64 SHADOW_OFF -> ew E 23 = w64 (SA + 48) -> ew E 25 = w64 (SA + 40) -> ew E 33 = Z_to_bv 64 (hp + 8 * n) ->
In (G0, ATABLE) (ablocks B ly S) -> G0 <= SA -> SA + AENT <= G0 + ATABLE ->
In (hp, kh) (ablocks B ly S) -> 8 * nh <= kh -> 0 <= n < nh ->
sh_ok SEGS rk_Bx rk_SH E (mrestrict (w_H W) m).
Proof.
intros E W ly S m md SA G0 hp kh n nh HAR E21 E23 E25 E33 HinT HT1 HT2 Hinh Hkh Hn.
destruct (rk_alb ly S W m md G0 ATABLE HAR HinT) as (HT16 & HT4096 & HTceil & HTapp & _ & _ & _).
destruct (rk_alb ly S W m md hp kh HAR Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & _ & _ & Hkh0).
change (req_size ATABLE) with 896 in *. unfold AENT, ATABLE in *.
pose proof (req_size_pos kh ltac:(lia)) as [Hrk1 Hrk2].
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
unfold sh_ok, rk_SH. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_range SEGS (w_H W) m E rk_Bx 25 (SA + 40) 8 (SA + 40) 0 8).
  + apply (rk_rab ly S W m md G0 ATABLE); [exact HAR | exact HinT | lia | change (req_size ATABLE) with 896; lia].
  + unfold rk_Bx. apply U_atom; [exact E21 | unfold SHADOW_OFF; lia].
  + apply U_atom; [exact E25 | lia].
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- apply (shent_ok_of_range SEGS (w_H W) m E rk_Bx 23 (SA + 48) 8 (SA + 48) 0 8).
  + apply (rk_rab ly S W m md G0 ATABLE); [exact HAR | exact HinT | lia | change (req_size ATABLE) with 896; lia].
  + unfold rk_Bx. apply U_atom; [exact E21 | unfold SHADOW_OFF; lia].
  + apply U_atom; [exact E23 | lia].
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- apply (shent_ok_of_range SEGS (w_H W) m E rk_Bx 33 (hp + 8 * n) 8 (hp + 8 * n) 0 8).
  + apply (rk_rab ly S W m md hp kh); [exact HAR | exact Hinh | lia | lia].
  + unfold rk_Bx. apply U_atom; [exact E21 | unfold SHADOW_OFF; lia].
  + apply U_atom; [exact E33 | lia].
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* the seat: any pc of the loop body whose registers and memory are as at the loop head *)
Lemma rk_seat : forall W ly S regs m md sp SA G0 hp kh n nh key f32 pc,
ARh ly S W m md ->
spZ regs = sp -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> alloc_ceiling <= sp ->
getr regs 9 = w64 sp -> getr regs 21 = w64 SHADOW_OFF ->
getr regs 19 = w64 (8 * n) -> getr regs 22 = w64 (8 * n) -> getr regs 20 = w64 n ->
getr regs 23 = w64 (SA + 48) -> getr regs 27 = w64 (SHADOW_OFF + (SA + 48) / 8) ->
getr regs 25 = w64 (SA + 40) -> getr regs 18 = w64 (SHADOW_OFF + (SA + 40) / 8) ->
In (G0, ATABLE) (ablocks B ly S) -> G0 <= SA -> SA + AENT <= G0 + ATABLE -> SA mod 8 = 0 ->
In (hp, kh) (ablocks B ly S) -> 8 * nh <= kh -> 0 <= n < nh -> nh < 2 ^ 26 ->
4096 <= key <= 140737479966720 -> 4096 <= f32 <= 140737479966720 ->
(hp + 8 * n + 8 <= SA + 40 \/ SA + 52 <= hp + 8 * n) ->
val_mem SEGS (arm W m) (SA + 40) 8 hp -> val_mem SEGS (arm W m) (SA + 48) 4 nh ->
val_mem SEGS (arm W m) (hp + 8 * n) 8 key -> val_mem SEGS (arm W m) (sp + 88) 8 f32 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rk_extra hp (hp + 8 * n) key nh f32))) (ss_k pc)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))) /\
sh_ok SEGS rk_Bx rk_SH (Eimg (Ereg regs (rk_extra hp (hp + 8 * n) key nh f32))) (mrestrict (w_H W) m).
Proof.
intros W ly S regs m md sp SA G0 hp kh n nh key f32 pc HAR Hsp Hsp1 Hsp16 Hspc R9 R21 R19 R22 R20 R23 R27 R25 R18
  HinT HT1 HT2 HSA8 Hinh Hkh Hn Hnh Hkey Hf32 Hdis Mhp Mnh Mkey Mf32.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_alb ly S W m md G0 ATABLE HAR HinT) as (HT16 & HT4096 & HTceil & HTapp & HTpres & _ & _).
destruct (rk_alb ly S W m md hp kh HAR Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & Hhpres & _ & Hkh0).
change (req_size ATABLE) with 896 in *. unfold AENT, ATABLE in *.
pose proof (req_size_pos kh ltac:(lia)) as [Hrk1 Hrk2].
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rk_extra hp (hp + 8 * n) key nh f32))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 hp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hp + 8 * n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 key) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 nh) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 f32) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 sp) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E19 : ew E 19 = Z_to_bv 64 (8 * n)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 n) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E23 : ew E 23 = Z_to_bv 64 (SA + 48)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E25 : ew E 25 = Z_to_bv 64 (SA + 40)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (V18 : getr regs 18 = sv_denot E (rk_sh 25))
  by (rewrite (rk_sh_den E 25 (SA + 40) E25 E21) by lia; exact R18).
assert (V27 : getr regs 27 = sv_denot E (rk_sh 23))
  by (rewrite (rk_sh_den E 23 (SA + 48) E23 E21) by lia; exact R27).
assert (V22 : getr regs 22 = sv_denot E (SOff 19 0))
  by (cbn [sv_denot]; rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned; exact R22).
split.
- unfold ss_k. apply pa_entry_st_ok_full.
  + unfold rk_regs.
    apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X | exact V18]
      | intros X; discriminate X | exact V27] | intros X; discriminate X | exact V22].
  + vm_compute. reflexivity.
  + unfold rk_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 25%nat (SA + 40) E25) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SA + 40) 0 8 (SOff 32 0) hp);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mhp].
    * rewrite (VB 23%nat (SA + 48) E23) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SA + 48) 0 4 (SOff 35 0) nh);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mnh].
    * rewrite (VB 33%nat (hp + 8 * n) E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (hp + 8 * n) 0 8 (SOff 34 0) key);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mkey].
    * rewrite (VB 9%nat sp E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ sp 88 8 (SOff 36 0) f32);
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mf32].
  + apply pairwise_disjoint_of_extents. unfold rk_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 25%nat (SA + 40) E25) by lia. rewrite (VB 23%nat (SA + 48) E23) by lia.
    rewrite (VB 33%nat (hp + 8 * n) E33) by lia. rewrite (VB 9%nat sp E9) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hdis HT1 HT2 HTceil Hhceil Hkh Hn Hrk2 Hspc HT4096 Hh4096. clear. intros. repeat split; lia.
  + split; [|split].
    * cbn [rk_facts rk_atoms f_atoms atoms_ok]. unfold afact_ok, PTRK. cbn [af_lo af_hi af_al2].
      rewrite Usp, E9, E21, E19, E20, E23, E25, E32, E33, E34, E35, E36.
      rewrite !unsigned_lit_small by (unfold SB, SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      assert (M1 : (8 * n) mod 8 = 0) by (replace (8 * n) with (n * 8) by lia; apply Z_mod_mult).
      assert (M2 : (SA + 48) mod 8 = 0)
        by (replace (SA + 48) with ((SA / 8 + 6) * 8) by (pose proof (Z.div_mod SA 8 ltac:(lia)); lia); apply Z_mod_mult).
      assert (M3 : (SA + 40) mod 8 = 0)
        by (replace (SA + 40) with ((SA / 8 + 5) * 8) by (pose proof (Z.div_mod SA 8 ltac:(lia)); lia); apply Z_mod_mult).
      assert (M4 : hp mod 8 = 0)
        by (replace hp with ((2 * (hp / 16)) * 8) by (pose proof (Z.div_mod hp 16 ltac:(lia)); lia); apply Z_mod_mult).
      assert (M5 : (hp + 8 * n) mod 8 = 0)
        by (replace (hp + 8 * n) with ((2 * (hp / 16) + n) * 8) by (pose proof (Z.div_mod hp 16 ltac:(lia)); lia); apply Z_mod_mult).
      unfold SB, SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
    * cbn [rk_facts rk_conds f_conds conds_ok]. split; [|exact I].
      unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U.
      rewrite (U_atom E 33 (hp + 8 * n) E33), (U_atom E 32 hp E32) by lia. apply negb_true_iff. apply Z.ltb_ge. lia.
    * cbn [rk_facts rk_alias f_alias alias_ok]. split; [|split; [|exact I]].
      -- apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
         rewrite (U_atom E 32 hp E32), (U_atom E 19 (8 * n) E19), (U_atom E 33 (hp + 8 * n) E33) by lia.
         apply zcanon_id. unfold M64. lia.
      -- apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
         rewrite (U_atom E 32 hp E32), (U_atom E 19 (8 * n) E19), (U_atom E 33 (hp + 8 * n) E33) by lia.
         replace (hp + 8 * n) with (8 * n + hp) by lia. apply zcanon_id. unfold M64. lia.
- apply (rk_shok E W ly S m md SA G0 hp kh n nh HAR E21 E23 E25 E33 HinT ltac:(lia) ltac:(unfold AENT, ATABLE; lia) Hinh Hkh Hn).
Qed.


Lemma rk3_shok : forall E W ly S m md SA G0 hp kh n nh hpl,
ARh ly S W m md ->
ew E 21 = w64 SHADOW_OFF -> ew E 23 = w64 (SA + 48) -> ew E 25 = w64 (SA + 40) -> ew E 33 = Z_to_bv 64 (hp + 8 * n) ->
ew E 36 = Z_to_bv 64 hpl ->
In (G0, ATABLE) (ablocks B ly S) -> G0 <= SA -> SA + AENT <= G0 + ATABLE ->
In (hp, kh) (ablocks B ly S) -> 8 * nh <= kh -> 0 <= n < nh -> hp <= hpl -> hpl + 8 <= hp + 8 * nh ->
sh_ok SEGS rk_Bx rk3_SH E (mrestrict (w_H W) m).
Proof.
intros E W ly S m md SA G0 hp kh n nh hpl HAR E21 E23 E25 E33 E36 HinT HT1 HT2 Hinh Hkh Hn Hl1 Hl2.
destruct (rk_alb ly S W m md G0 ATABLE HAR HinT) as (HT16 & HT4096 & HTceil & HTapp & _ & _ & _).
destruct (rk_alb ly S W m md hp kh HAR Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & _ & _ & Hkh0).
change (req_size ATABLE) with 896 in *. unfold AENT, ATABLE in *.
pose proof (req_size_pos kh ltac:(lia)) as [Hrk1 Hrk2].
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (rk_shok E W ly S m md SA G0 hp kh n nh HAR E21 E23 E25 E33 HinT HT1 HT2 Hinh Hkh Hn) as H3.
unfold sh_ok, rk_SH in H3. inversion H3 as [|? ? Ha Hr]; subst. inversion Hr as [|? ? Hb Hr2]; subst.
inversion Hr2 as [|? ? Hc _]; subst.
unfold sh_ok, rk3_SH. constructor; [exact Ha|]. constructor; [exact Hb|]. constructor; [exact Hc|]. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) m E rk_Bx 36 hpl 8 hpl 0 8).
- apply (rk_rab ly S W m md hp kh); [exact HAR | exact Hinh | lia | lia].
- unfold rk_Bx. apply U_atom; [exact E21 | unfold SHADOW_OFF; lia].
- apply U_atom; [exact E36 | lia].
- lia.
- lia.
- intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

Lemma rk_seat3 : forall (last : bool) W ly S regs m md sp SA G0 hp kh n nh key klast pc,
ARh ly S W m md ->
spZ regs = sp -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> alloc_ceiling <= sp ->
getr regs 9 = w64 sp -> getr regs 21 = w64 SHADOW_OFF ->
getr regs 19 = w64 (8 * n) -> getr regs 22 = w64 (8 * n) -> getr regs 20 = w64 n ->
getr regs 23 = w64 (SA + 48) -> getr regs 27 = w64 (SHADOW_OFF + (SA + 48) / 8) ->
getr regs 25 = w64 (SA + 40) -> getr regs 18 = w64 (SHADOW_OFF + (SA + 40) / 8) ->
In (G0, ATABLE) (ablocks B ly S) -> G0 <= SA -> SA + AENT <= G0 + ATABLE -> SA mod 8 = 0 ->
In (hp, kh) (ablocks B ly S) -> 8 * nh <= kh -> nh < 2 ^ 26 ->
(if last then nh = n + 1 else n + 2 <= nh) -> 0 <= n ->
4096 <= key <= 140737479966720 -> 4096 <= klast <= 140737479966720 ->
(hp + kh <= SA + 40 \/ SA + 52 <= hp) ->
val_mem SEGS (arm W m) (SA + 40) 8 hp -> val_mem SEGS (arm W m) (SA + 48) 4 nh ->
val_mem SEGS (arm W m) (hp + 8 * n) 8 key -> (last = false -> val_mem SEGS (arm W m) (hp + 8 * (nh - 1)) 8 klast) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rk_extra3 hp (hp + 8 * n) key nh (hp + 8 * (nh - 1)) klast)))
  ((if last then ss_k3b else ss_k3a) pc)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))) /\
sh_ok SEGS rk_Bx rk3_SH (Eimg (Ereg regs (rk_extra3 hp (hp + 8 * n) key nh (hp + 8 * (nh - 1)) klast))) (mrestrict (w_H W) m).
Proof.
intros last W ly S regs m md sp SA G0 hp kh n nh key klast pc HAR Hsp Hsp1 Hsp16 Hspc R9 R21 R19 R22 R20 R23 R27 R25 R18
  HinT HT1 HT2 HSA8 Hinh Hkh Hnh Hlast Hn0 Hkey Hkl Hblk Mhp Mnh Mkey Mkl.
assert (Hn : 0 <= n < nh) by (destruct last; lia).
assert (Hdis : hp + 8 * n + 8 <= SA + 40 \/ SA + 52 <= hp + 8 * n) by lia.
assert (Hdis2 : hp + 8 * (nh - 1) + 8 <= SA + 40 \/ SA + 52 <= hp + 8 * (nh - 1)) by lia.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_alb ly S W m md G0 ATABLE HAR HinT) as (HT16 & HT4096 & HTceil & HTapp & HTpres & _ & _).
destruct (rk_alb ly S W m md hp kh HAR Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & Hhpres & _ & Hkh0).
change (req_size ATABLE) with 896 in *. unfold AENT, ATABLE in *.
pose proof (req_size_pos kh ltac:(lia)) as [Hrk1 Hrk2].
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rk_extra3 hp (hp + 8 * n) key nh (hp + 8 * (nh - 1)) klast))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 hp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hp + 8 * n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 key) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 nh) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (hp + 8 * (nh - 1))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 klast) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 sp) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E19 : ew E 19 = Z_to_bv 64 (8 * n)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 n) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E23 : ew E 23 = Z_to_bv 64 (SA + 48)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E25 : ew E 25 = Z_to_bv 64 (SA + 40)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (V18 : getr regs 18 = sv_denot E (rk_sh 25))
  by (rewrite (rk_sh_den E 25 (SA + 40) E25 E21) by lia; exact R18).
assert (V27 : getr regs 27 = sv_denot E (rk_sh 23))
  by (rewrite (rk_sh_den E 23 (SA + 48) E23 E21) by lia; exact R27).
assert (V22 : getr regs 22 = sv_denot E (SOff 19 0))
  by (cbn [sv_denot]; rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned; exact R22).
assert (HRG : regs_ok E rk_regs regs).
{ unfold rk_regs.
  apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X | exact V18]
    | intros X; discriminate X | exact V27] | intros X; discriminate X | exact V22]. }
assert (HPL : sv_denot E rk3_hpl_sv = Z_to_bv 64 (hp + 8 * (nh - 1))).
{ unfold rk3_hpl_sv. cbn [sv_denot]. rewrite E32, E35, !unsigned_lit_small by lia.
  apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
  rewrite !unsigned_lit_small by lia. change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small ((nh + 0) * 8)) by lia. rewrite Z.mod_small by lia. lia. }
assert (M1 : (8 * n) mod 8 = 0) by (replace (8 * n) with (n * 8) by lia; apply Z_mod_mult).
assert (M2 : (SA + 48) mod 8 = 0)
  by (replace (SA + 48) with ((SA / 8 + 6) * 8) by (pose proof (Z.div_mod SA 8 ltac:(lia)); lia); apply Z_mod_mult).
assert (M3 : (SA + 40) mod 8 = 0)
  by (replace (SA + 40) with ((SA / 8 + 5) * 8) by (pose proof (Z.div_mod SA 8 ltac:(lia)); lia); apply Z_mod_mult).
assert (M4 : hp mod 8 = 0)
  by (replace hp with ((2 * (hp / 16)) * 8) by (pose proof (Z.div_mod hp 16 ltac:(lia)); lia); apply Z_mod_mult).
assert (M5 : (hp + 8 * n) mod 8 = 0)
  by (replace (hp + 8 * n) with ((2 * (hp / 16) + n) * 8) by (pose proof (Z.div_mod hp 16 ltac:(lia)); lia); apply Z_mod_mult).
assert (M6 : (hp + 8 * (nh - 1)) mod 8 = 0)
  by (replace (hp + 8 * (nh - 1)) with ((2 * (hp / 16) + (nh - 1)) * 8) by (pose proof (Z.div_mod hp 16 ltac:(lia)); lia); apply Z_mod_mult).
assert (M7 : sp mod 16 = 0) by exact Hsp16.
assert (HATOMS : forall nlo, nlo <= nh -> atoms_ok E (rk3_atoms nlo)).
{ intros nlo Hnlo. cbn [rk3_atoms atoms_ok]. unfold afact_ok, PTRK. cbn [af_lo af_hi af_al2].
  rewrite Usp, E9, E21, E19, E20, E23, E25, E32, E33, E34, E35, E36, E37.
  rewrite !unsigned_lit_small by (unfold SB, SHADOW_OFF; destruct last; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
assert (HCOND : conds_ok E rk_conds).
{ cbn [rk_conds conds_ok]. split; [|exact I].
  unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U.
  rewrite (U_atom E 33 (hp + 8 * n) E33), (U_atom E 32 hp E32) by lia. apply negb_true_iff. apply Z.ltb_ge. lia. }
assert (AL1 : sv_denot E (SAlu ALU_ADD (SOff 32 0) (SOff 19 0)) = sv_denot E (SOff 33 0)).
{ apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 32 hp E32), (U_atom E 19 (8 * n) E19), (U_atom E 33 (hp + 8 * n) E33) by lia.
  apply zcanon_id. unfold M64. lia. }
assert (AL2 : sv_denot E (SAlu ALU_ADD (SOff 19 0) (SOff 32 0)) = sv_denot E (SOff 33 0)).
{ apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 32 hp E32), (U_atom E 19 (8 * n) E19), (U_atom E 33 (hp + 8 * n) E33) by lia.
  replace (hp + 8 * n) with (8 * n + hp) by lia. apply zcanon_id. unfold M64. lia. }
assert (RG0 : region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 25%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 25%nat (SA + 40) E25) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (SA + 40) 0 8 (SOff 32 0) hp);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mhp]. }
assert (RG1 : region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 23%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 23%nat (SA + 48) E23) by lia. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply (HTpres (SA + 48 + o)); lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (SA + 48) 0 4 (SOff 35 0) nh);
  [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mnh]. }
assert (RG2 : region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 33%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 33%nat (hp + 8 * n) E33) by lia. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply (Hhpres (hp + 8 * n + o)); lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (hp + 8 * n) 0 8 (SOff 34 0) key);
  [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mkey]. }
split.
- destruct last.
  + unfold ss_k3b. apply pa_entry_st_ok_full.
    * exact HRG.
    * vm_compute. reflexivity.
    * unfold rk3b_regions. repeat apply Forall_cons; try apply Forall_nil; assumption.
    * apply pairwise_disjoint_of_extents. unfold rk3b_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 25%nat (SA + 40) E25) by lia. rewrite (VB 23%nat (SA + 48) E23) by lia.
      rewrite (VB 33%nat (hp + 8 * n) E33) by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hdis. clear. intros. repeat split; lia.
    * split; [apply HATOMS; lia|]. split; [exact HCOND|].
      cbn [rk3b_facts f_alias rk_alias app alias_ok]. refine (conj AL1 (conj AL2 (conj _ I))).
      rewrite HPL. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. f_equal. lia.
  + unfold ss_k3a. apply pa_entry_st_ok_full.
    * exact HRG.
    * vm_compute. reflexivity.
    * unfold rk3a_regions. repeat apply Forall_cons; try apply Forall_nil; try assumption.
      unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 36%nat (hp + 8 * (nh - 1)) E36) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (hp + 8 * (nh - 1)) 0 8 (SOff 37 0) klast);
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact (Mkl eq_refl)].
    * apply pairwise_disjoint_of_extents. unfold rk3a_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 25%nat (SA + 40) E25) by lia. rewrite (VB 23%nat (SA + 48) E23) by lia.
      rewrite (VB 33%nat (hp + 8 * n) E33) by lia. rewrite (VB 36%nat (hp + 8 * (nh - 1)) E36) by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hdis Hdis2 Hlast. clear. intros. repeat split; lia.
    * split; [apply HATOMS; lia|]. split; [exact HCOND|].
      cbn [rk3a_facts f_alias rk_alias app alias_ok]. refine (conj AL1 (conj AL2 (conj _ I))).
      rewrite HPL. cbn [sv_denot]. rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- apply (rk3_shok E W ly S m md SA G0 hp kh n nh (hp + 8 * (nh - 1)) HAR E21 E23 E25 E33 E36 HinT ltac:(lia)
    ltac:(unfold AENT, ATABLE; lia) Hinh Hkh Hn ltac:(lia) ltac:(lia)).
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): KEY's seat lemmas at a world relation R.  The strict lemmas above take every Section
   hypothesis (Default Proof Using "All"), the strict AFREE / DRAIN / GE / ALLOC_TAIL included, so this Section copies
   each of them as X_xR (same statement and proof) under a Default Proof Using that leaves those out.  The lemmas that
   read a journal are lifted: ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the journal lemmas ->
   their _xR twins (W_journal_x.v), nothing else (no lemma here reads a journal).  The hypothesis list is the cx file's Section wR, verbatim. ---- *)
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
(* every lemma below takes the Section's hypotheses except the strict AFREE / DRAIN / GE / ALLOC_TAIL and R_refl /
   DRAIN_R (KEY needs none of them), so no route-R statement here carries a strict allocator rule *)
#[local] Set Default Proof Using "-(AFREE DRAIN GE ALLOC_TAIL R_refl DRAIN_R)".
(* ==== the generic relation at the empty head set (the image-A twin's lib/A/W_rig_key.v:236-280; Local here, as every
   key file that needs them defines its own) ==== *)
(* HP0: every ARx state a seat reads has the head set [], so the seats state it at ARh (= ARx at []).  rk_alb_xR is
   AR_blocks_law's seven conjuncts (alx_blocks' six and BLKN), in the AR walk's argument order. *)
Local Lemma rk_alb_xR : forall ly S W mem md p n, ARh ly S W mem md -> In (p, n) (ablocks B ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\ 0 <= n.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (BLKN ly S [] W mem md p n HAR Hin))))))).
Qed.

Lemma rk_sh_den_xR : forall E b x, ew E b = w64 x -> ew E 21 = w64 SHADOW_OFF -> 0 <= x < 2 ^ 60 ->
sv_denot E (rk_sh b) = w64 (SHADOW_OFF + x / 8).
Proof.
intros E b x Hb E21 Hx. unfold rk_sh. cbn [sv_denot]. rewrite Hb, E21, !Z.add_0_r, !Z_to_bv_bv_unsigned.
assert (H8 : 0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (x / 8) (2 ^ 64)) by lia. rewrite Z.add_comm. apply Z.mod_small. unfold SHADOW_OFF. lia.
Qed.

(* the three shadow entries, at any memory where the table and the held array are live blocks *)
Lemma rk_shok_xR : forall E W ly S m md SA G0 hp kh n nh,
ARh ly S W m md ->
ew E 21 = w64 SHADOW_OFF -> ew E 23 = w64 (SA + 48) -> ew E 25 = w64 (SA + 40) -> ew E 33 = Z_to_bv 64 (hp + 8 * n) ->
In (G0, ATABLE) (ablocks B ly S) -> G0 <= SA -> SA + AENT <= G0 + ATABLE ->
In (hp, kh) (ablocks B ly S) -> 8 * nh <= kh -> 0 <= n < nh ->
sh_ok SEGS rk_Bx rk_SH E (mrestrict (w_H W) m).
Proof.
intros E W ly S m md SA G0 hp kh n nh HAR E21 E23 E25 E33 HinT HT1 HT2 Hinh Hkh Hn.
destruct (rk_alb_xR ly S W m md G0 ATABLE HAR HinT) as (HT16 & HT4096 & HTceil & HTapp & _ & _ & _).
destruct (rk_alb_xR ly S W m md hp kh HAR Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & _ & _ & Hkh0).
change (req_size ATABLE) with 896 in *. unfold AENT, ATABLE in *.
pose proof (req_size_pos kh ltac:(lia)) as [Hrk1 Hrk2].
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
unfold sh_ok, rk_SH. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_range SEGS (w_H W) m E rk_Bx 25 (SA + 40) 8 (SA + 40) 0 8).
  + apply (rk_rab ly S W m md G0 ATABLE); [exact HAR | exact HinT | lia | change (req_size ATABLE) with 896; lia].
  + unfold rk_Bx. apply U_atom; [exact E21 | unfold SHADOW_OFF; lia].
  + apply U_atom; [exact E25 | lia].
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- apply (shent_ok_of_range SEGS (w_H W) m E rk_Bx 23 (SA + 48) 8 (SA + 48) 0 8).
  + apply (rk_rab ly S W m md G0 ATABLE); [exact HAR | exact HinT | lia | change (req_size ATABLE) with 896; lia].
  + unfold rk_Bx. apply U_atom; [exact E21 | unfold SHADOW_OFF; lia].
  + apply U_atom; [exact E23 | lia].
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- apply (shent_ok_of_range SEGS (w_H W) m E rk_Bx 33 (hp + 8 * n) 8 (hp + 8 * n) 0 8).
  + apply (rk_rab ly S W m md hp kh); [exact HAR | exact Hinh | lia | lia].
  + unfold rk_Bx. apply U_atom; [exact E21 | unfold SHADOW_OFF; lia].
  + apply U_atom; [exact E33 | lia].
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* the seat: any pc of the loop body whose registers and memory are as at the loop head *)
Lemma rk_seat_xR : forall W ly S regs m md sp SA G0 hp kh n nh key f32 pc,
ARh ly S W m md ->
spZ regs = sp -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> alloc_ceiling <= sp ->
getr regs 9 = w64 sp -> getr regs 21 = w64 SHADOW_OFF ->
getr regs 19 = w64 (8 * n) -> getr regs 22 = w64 (8 * n) -> getr regs 20 = w64 n ->
getr regs 23 = w64 (SA + 48) -> getr regs 27 = w64 (SHADOW_OFF + (SA + 48) / 8) ->
getr regs 25 = w64 (SA + 40) -> getr regs 18 = w64 (SHADOW_OFF + (SA + 40) / 8) ->
In (G0, ATABLE) (ablocks B ly S) -> G0 <= SA -> SA + AENT <= G0 + ATABLE -> SA mod 8 = 0 ->
In (hp, kh) (ablocks B ly S) -> 8 * nh <= kh -> 0 <= n < nh -> nh < 2 ^ 26 ->
4096 <= key <= 140737479966720 -> 4096 <= f32 <= 140737479966720 ->
(hp + 8 * n + 8 <= SA + 40 \/ SA + 52 <= hp + 8 * n) ->
val_mem SEGS (arm W m) (SA + 40) 8 hp -> val_mem SEGS (arm W m) (SA + 48) 4 nh ->
val_mem SEGS (arm W m) (hp + 8 * n) 8 key -> val_mem SEGS (arm W m) (sp + 88) 8 f32 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rk_extra hp (hp + 8 * n) key nh f32))) (ss_k pc)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))) /\
sh_ok SEGS rk_Bx rk_SH (Eimg (Ereg regs (rk_extra hp (hp + 8 * n) key nh f32))) (mrestrict (w_H W) m).
Proof.
intros W ly S regs m md sp SA G0 hp kh n nh key f32 pc HAR Hsp Hsp1 Hsp16 Hspc R9 R21 R19 R22 R20 R23 R27 R25 R18
  HinT HT1 HT2 HSA8 Hinh Hkh Hn Hnh Hkey Hf32 Hdis Mhp Mnh Mkey Mf32.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_alb_xR ly S W m md G0 ATABLE HAR HinT) as (HT16 & HT4096 & HTceil & HTapp & HTpres & _ & _).
destruct (rk_alb_xR ly S W m md hp kh HAR Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & Hhpres & _ & Hkh0).
change (req_size ATABLE) with 896 in *. unfold AENT, ATABLE in *.
pose proof (req_size_pos kh ltac:(lia)) as [Hrk1 Hrk2].
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rk_extra hp (hp + 8 * n) key nh f32))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 hp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hp + 8 * n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 key) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 nh) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 f32) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 sp) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E19 : ew E 19 = Z_to_bv 64 (8 * n)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 n) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E23 : ew E 23 = Z_to_bv 64 (SA + 48)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E25 : ew E 25 = Z_to_bv 64 (SA + 40)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (V18 : getr regs 18 = sv_denot E (rk_sh 25))
  by (rewrite (rk_sh_den_xR E 25 (SA + 40) E25 E21) by lia; exact R18).
assert (V27 : getr regs 27 = sv_denot E (rk_sh 23))
  by (rewrite (rk_sh_den_xR E 23 (SA + 48) E23 E21) by lia; exact R27).
assert (V22 : getr regs 22 = sv_denot E (SOff 19 0))
  by (cbn [sv_denot]; rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned; exact R22).
split.
- unfold ss_k. apply pa_entry_st_ok_full.
  + unfold rk_regs.
    apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X | exact V18]
      | intros X; discriminate X | exact V27] | intros X; discriminate X | exact V22].
  + vm_compute. reflexivity.
  + unfold rk_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 25%nat (SA + 40) E25) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SA + 40) 0 8 (SOff 32 0) hp);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mhp].
    * rewrite (VB 23%nat (SA + 48) E23) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SA + 48) 0 4 (SOff 35 0) nh);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mnh].
    * rewrite (VB 33%nat (hp + 8 * n) E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (hp + 8 * n) 0 8 (SOff 34 0) key);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mkey].
    * rewrite (VB 9%nat sp E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ sp 88 8 (SOff 36 0) f32);
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mf32].
  + apply pairwise_disjoint_of_extents. unfold rk_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 25%nat (SA + 40) E25) by lia. rewrite (VB 23%nat (SA + 48) E23) by lia.
    rewrite (VB 33%nat (hp + 8 * n) E33) by lia. rewrite (VB 9%nat sp E9) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hdis HT1 HT2 HTceil Hhceil Hkh Hn Hrk2 Hspc HT4096 Hh4096. clear. intros. repeat split; lia.
  + split; [|split].
    * cbn [rk_facts rk_atoms f_atoms atoms_ok]. unfold afact_ok, PTRK. cbn [af_lo af_hi af_al2].
      rewrite Usp, E9, E21, E19, E20, E23, E25, E32, E33, E34, E35, E36.
      rewrite !unsigned_lit_small by (unfold SB, SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      assert (M1 : (8 * n) mod 8 = 0) by (replace (8 * n) with (n * 8) by lia; apply Z_mod_mult).
      assert (M2 : (SA + 48) mod 8 = 0)
        by (replace (SA + 48) with ((SA / 8 + 6) * 8) by (pose proof (Z.div_mod SA 8 ltac:(lia)); lia); apply Z_mod_mult).
      assert (M3 : (SA + 40) mod 8 = 0)
        by (replace (SA + 40) with ((SA / 8 + 5) * 8) by (pose proof (Z.div_mod SA 8 ltac:(lia)); lia); apply Z_mod_mult).
      assert (M4 : hp mod 8 = 0)
        by (replace hp with ((2 * (hp / 16)) * 8) by (pose proof (Z.div_mod hp 16 ltac:(lia)); lia); apply Z_mod_mult).
      assert (M5 : (hp + 8 * n) mod 8 = 0)
        by (replace (hp + 8 * n) with ((2 * (hp / 16) + n) * 8) by (pose proof (Z.div_mod hp 16 ltac:(lia)); lia); apply Z_mod_mult).
      unfold SB, SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
    * cbn [rk_facts rk_conds f_conds conds_ok]. split; [|exact I].
      unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U.
      rewrite (U_atom E 33 (hp + 8 * n) E33), (U_atom E 32 hp E32) by lia. apply negb_true_iff. apply Z.ltb_ge. lia.
    * cbn [rk_facts rk_alias f_alias alias_ok]. split; [|split; [|exact I]].
      -- apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
         rewrite (U_atom E 32 hp E32), (U_atom E 19 (8 * n) E19), (U_atom E 33 (hp + 8 * n) E33) by lia.
         apply zcanon_id. unfold M64. lia.
      -- apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
         rewrite (U_atom E 32 hp E32), (U_atom E 19 (8 * n) E19), (U_atom E 33 (hp + 8 * n) E33) by lia.
         replace (hp + 8 * n) with (8 * n + hp) by lia. apply zcanon_id. unfold M64. lia.
- apply (rk_shok_xR E W ly S m md SA G0 hp kh n nh HAR E21 E23 E25 E33 HinT ltac:(lia) ltac:(unfold AENT, ATABLE; lia) Hinh Hkh Hn).
Qed.


Lemma rk3_shok_xR : forall E W ly S m md SA G0 hp kh n nh hpl,
ARh ly S W m md ->
ew E 21 = w64 SHADOW_OFF -> ew E 23 = w64 (SA + 48) -> ew E 25 = w64 (SA + 40) -> ew E 33 = Z_to_bv 64 (hp + 8 * n) ->
ew E 36 = Z_to_bv 64 hpl ->
In (G0, ATABLE) (ablocks B ly S) -> G0 <= SA -> SA + AENT <= G0 + ATABLE ->
In (hp, kh) (ablocks B ly S) -> 8 * nh <= kh -> 0 <= n < nh -> hp <= hpl -> hpl + 8 <= hp + 8 * nh ->
sh_ok SEGS rk_Bx rk3_SH E (mrestrict (w_H W) m).
Proof.
intros E W ly S m md SA G0 hp kh n nh hpl HAR E21 E23 E25 E33 E36 HinT HT1 HT2 Hinh Hkh Hn Hl1 Hl2.
destruct (rk_alb_xR ly S W m md G0 ATABLE HAR HinT) as (HT16 & HT4096 & HTceil & HTapp & _ & _ & _).
destruct (rk_alb_xR ly S W m md hp kh HAR Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & _ & _ & Hkh0).
change (req_size ATABLE) with 896 in *. unfold AENT, ATABLE in *.
pose proof (req_size_pos kh ltac:(lia)) as [Hrk1 Hrk2].
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (rk_shok_xR E W ly S m md SA G0 hp kh n nh HAR E21 E23 E25 E33 HinT HT1 HT2 Hinh Hkh Hn) as H3.
unfold sh_ok, rk_SH in H3. inversion H3 as [|? ? Ha Hr]; subst. inversion Hr as [|? ? Hb Hr2]; subst.
inversion Hr2 as [|? ? Hc _]; subst.
unfold sh_ok, rk3_SH. constructor; [exact Ha|]. constructor; [exact Hb|]. constructor; [exact Hc|]. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) m E rk_Bx 36 hpl 8 hpl 0 8).
- apply (rk_rab ly S W m md hp kh); [exact HAR | exact Hinh | lia | lia].
- unfold rk_Bx. apply U_atom; [exact E21 | unfold SHADOW_OFF; lia].
- apply U_atom; [exact E36 | lia].
- lia.
- lia.
- intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

Lemma rk_seat3_xR : forall (last : bool) W ly S regs m md sp SA G0 hp kh n nh key klast pc,
ARh ly S W m md ->
spZ regs = sp -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> alloc_ceiling <= sp ->
getr regs 9 = w64 sp -> getr regs 21 = w64 SHADOW_OFF ->
getr regs 19 = w64 (8 * n) -> getr regs 22 = w64 (8 * n) -> getr regs 20 = w64 n ->
getr regs 23 = w64 (SA + 48) -> getr regs 27 = w64 (SHADOW_OFF + (SA + 48) / 8) ->
getr regs 25 = w64 (SA + 40) -> getr regs 18 = w64 (SHADOW_OFF + (SA + 40) / 8) ->
In (G0, ATABLE) (ablocks B ly S) -> G0 <= SA -> SA + AENT <= G0 + ATABLE -> SA mod 8 = 0 ->
In (hp, kh) (ablocks B ly S) -> 8 * nh <= kh -> nh < 2 ^ 26 ->
(if last then nh = n + 1 else n + 2 <= nh) -> 0 <= n ->
4096 <= key <= 140737479966720 -> 4096 <= klast <= 140737479966720 ->
(hp + kh <= SA + 40 \/ SA + 52 <= hp) ->
val_mem SEGS (arm W m) (SA + 40) 8 hp -> val_mem SEGS (arm W m) (SA + 48) 4 nh ->
val_mem SEGS (arm W m) (hp + 8 * n) 8 key -> (last = false -> val_mem SEGS (arm W m) (hp + 8 * (nh - 1)) 8 klast) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rk_extra3 hp (hp + 8 * n) key nh (hp + 8 * (nh - 1)) klast)))
  ((if last then ss_k3b else ss_k3a) pc)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))) /\
sh_ok SEGS rk_Bx rk3_SH (Eimg (Ereg regs (rk_extra3 hp (hp + 8 * n) key nh (hp + 8 * (nh - 1)) klast))) (mrestrict (w_H W) m).
Proof.
intros last W ly S regs m md sp SA G0 hp kh n nh key klast pc HAR Hsp Hsp1 Hsp16 Hspc R9 R21 R19 R22 R20 R23 R27 R25 R18
  HinT HT1 HT2 HSA8 Hinh Hkh Hnh Hlast Hn0 Hkey Hkl Hblk Mhp Mnh Mkey Mkl.
assert (Hn : 0 <= n < nh) by (destruct last; lia).
assert (Hdis : hp + 8 * n + 8 <= SA + 40 \/ SA + 52 <= hp + 8 * n) by lia.
assert (Hdis2 : hp + 8 * (nh - 1) + 8 <= SA + 40 \/ SA + 52 <= hp + 8 * (nh - 1)) by lia.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_alb_xR ly S W m md G0 ATABLE HAR HinT) as (HT16 & HT4096 & HTceil & HTapp & HTpres & _ & _).
destruct (rk_alb_xR ly S W m md hp kh HAR Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & Hhpres & _ & Hkh0).
change (req_size ATABLE) with 896 in *. unfold AENT, ATABLE in *.
pose proof (req_size_pos kh ltac:(lia)) as [Hrk1 Hrk2].
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rk_extra3 hp (hp + 8 * n) key nh (hp + 8 * (nh - 1)) klast))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 hp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hp + 8 * n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 key) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 nh) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (hp + 8 * (nh - 1))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 klast) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 sp) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E19 : ew E 19 = Z_to_bv 64 (8 * n)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 n) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E23 : ew E 23 = Z_to_bv 64 (SA + 48)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E25 : ew E 25 = Z_to_bv 64 (SA + 40)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (V18 : getr regs 18 = sv_denot E (rk_sh 25))
  by (rewrite (rk_sh_den_xR E 25 (SA + 40) E25 E21) by lia; exact R18).
assert (V27 : getr regs 27 = sv_denot E (rk_sh 23))
  by (rewrite (rk_sh_den_xR E 23 (SA + 48) E23 E21) by lia; exact R27).
assert (V22 : getr regs 22 = sv_denot E (SOff 19 0))
  by (cbn [sv_denot]; rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned; exact R22).
assert (HRG : regs_ok E rk_regs regs).
{ unfold rk_regs.
  apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X | exact V18]
    | intros X; discriminate X | exact V27] | intros X; discriminate X | exact V22]. }
assert (HPL : sv_denot E rk3_hpl_sv = Z_to_bv 64 (hp + 8 * (nh - 1))).
{ unfold rk3_hpl_sv. cbn [sv_denot]. rewrite E32, E35, !unsigned_lit_small by lia.
  apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
  rewrite !unsigned_lit_small by lia. change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small ((nh + 0) * 8)) by lia. rewrite Z.mod_small by lia. lia. }
assert (M1 : (8 * n) mod 8 = 0) by (replace (8 * n) with (n * 8) by lia; apply Z_mod_mult).
assert (M2 : (SA + 48) mod 8 = 0)
  by (replace (SA + 48) with ((SA / 8 + 6) * 8) by (pose proof (Z.div_mod SA 8 ltac:(lia)); lia); apply Z_mod_mult).
assert (M3 : (SA + 40) mod 8 = 0)
  by (replace (SA + 40) with ((SA / 8 + 5) * 8) by (pose proof (Z.div_mod SA 8 ltac:(lia)); lia); apply Z_mod_mult).
assert (M4 : hp mod 8 = 0)
  by (replace hp with ((2 * (hp / 16)) * 8) by (pose proof (Z.div_mod hp 16 ltac:(lia)); lia); apply Z_mod_mult).
assert (M5 : (hp + 8 * n) mod 8 = 0)
  by (replace (hp + 8 * n) with ((2 * (hp / 16) + n) * 8) by (pose proof (Z.div_mod hp 16 ltac:(lia)); lia); apply Z_mod_mult).
assert (M6 : (hp + 8 * (nh - 1)) mod 8 = 0)
  by (replace (hp + 8 * (nh - 1)) with ((2 * (hp / 16) + (nh - 1)) * 8) by (pose proof (Z.div_mod hp 16 ltac:(lia)); lia); apply Z_mod_mult).
assert (M7 : sp mod 16 = 0) by exact Hsp16.
assert (HATOMS : forall nlo, nlo <= nh -> atoms_ok E (rk3_atoms nlo)).
{ intros nlo Hnlo. cbn [rk3_atoms atoms_ok]. unfold afact_ok, PTRK. cbn [af_lo af_hi af_al2].
  rewrite Usp, E9, E21, E19, E20, E23, E25, E32, E33, E34, E35, E36, E37.
  rewrite !unsigned_lit_small by (unfold SB, SHADOW_OFF; destruct last; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
assert (HCOND : conds_ok E rk_conds).
{ cbn [rk_conds conds_ok]. split; [|exact I].
  unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U.
  rewrite (U_atom E 33 (hp + 8 * n) E33), (U_atom E 32 hp E32) by lia. apply negb_true_iff. apply Z.ltb_ge. lia. }
assert (AL1 : sv_denot E (SAlu ALU_ADD (SOff 32 0) (SOff 19 0)) = sv_denot E (SOff 33 0)).
{ apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 32 hp E32), (U_atom E 19 (8 * n) E19), (U_atom E 33 (hp + 8 * n) E33) by lia.
  apply zcanon_id. unfold M64. lia. }
assert (AL2 : sv_denot E (SAlu ALU_ADD (SOff 19 0) (SOff 32 0)) = sv_denot E (SOff 33 0)).
{ apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 32 hp E32), (U_atom E 19 (8 * n) E19), (U_atom E 33 (hp + 8 * n) E33) by lia.
  replace (hp + 8 * n) with (8 * n + hp) by lia. apply zcanon_id. unfold M64. lia. }
assert (RG0 : region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 25%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 25%nat (SA + 40) E25) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (SA + 40) 0 8 (SOff 32 0) hp);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mhp]. }
assert (RG1 : region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 23%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 23%nat (SA + 48) E23) by lia. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply (HTpres (SA + 48 + o)); lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (SA + 48) 0 4 (SOff 35 0) nh);
  [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mnh]. }
assert (RG2 : region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 33%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 33%nat (hp + 8 * n) E33) by lia. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply (Hhpres (hp + 8 * n + o)); lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (hp + 8 * n) 0 8 (SOff 34 0) key);
  [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mkey]. }
split.
- destruct last.
  + unfold ss_k3b. apply pa_entry_st_ok_full.
    * exact HRG.
    * vm_compute. reflexivity.
    * unfold rk3b_regions. repeat apply Forall_cons; try apply Forall_nil; assumption.
    * apply pairwise_disjoint_of_extents. unfold rk3b_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 25%nat (SA + 40) E25) by lia. rewrite (VB 23%nat (SA + 48) E23) by lia.
      rewrite (VB 33%nat (hp + 8 * n) E33) by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hdis. clear. intros. repeat split; lia.
    * split; [apply HATOMS; lia|]. split; [exact HCOND|].
      cbn [rk3b_facts f_alias rk_alias app alias_ok]. refine (conj AL1 (conj AL2 (conj _ I))).
      rewrite HPL. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. f_equal. lia.
  + unfold ss_k3a. apply pa_entry_st_ok_full.
    * exact HRG.
    * vm_compute. reflexivity.
    * unfold rk3a_regions. repeat apply Forall_cons; try apply Forall_nil; try assumption.
      unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 36%nat (hp + 8 * (nh - 1)) E36) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (hp + 8 * (nh - 1)) 0 8 (SOff 37 0) klast);
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact (Mkl eq_refl)].
    * apply pairwise_disjoint_of_extents. unfold rk3a_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 25%nat (SA + 40) E25) by lia. rewrite (VB 23%nat (SA + 48) E23) by lia.
      rewrite (VB 33%nat (hp + 8 * n) E33) by lia. rewrite (VB 36%nat (hp + 8 * (nh - 1)) E36) by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hdis Hdis2 Hlast. clear. intros. repeat split; lia.
    * split; [apply HATOMS; lia|]. split; [exact HCOND|].
      cbn [rk3a_facts f_alias rk_alias app alias_ok]. refine (conj AL1 (conj AL2 (conj _ I))).
      rewrite HPL. cbn [sv_denot]. rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- apply (rk3_shok_xR E W ly S m md SA G0 hp kh n nh (hp + 8 * (nh - 1)) HAR E21 E23 E25 E33 E36 HinT ltac:(lia)
    ltac:(unfold AENT, ATABLE; lia) Hinh Hkh Hn ltac:(lia) ltac:(lia)).
Qed.
End wR.

End c.
End b.
End a.
