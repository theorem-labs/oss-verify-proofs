(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment PRO of the IMAGE-B walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan-ubsan 0x82ca0 .. 0x82e18), lib/B/W_relay_instance_gone_cx.v rig_pro_stmt: the prologue (thirteen
   saves, the id at 72(sp)), __asan_stack_malloc_1 (128) at 0x82d0c (the uar cell is 1, alx_const; the real-stack
   fallback 0x82d20-0x82d38 is not reached: SMALLOC gives a fake frame under GBASE's count_cid), 8(sp) / 16(sp) /
   112(sp) = F, the fake frame's header and the shadow poison through s4 = F's shadow, pthread_mutex_lock (g_lock) at
   0x82dc8, 64(sp) = g_nsrc's register image, the g_nsrc test 0x82dd8 (g_nsrc <= 0 -> the unlock tail RGU at 0x8312c)
   and the outer loop's setup 0x82ddc-0x82e18 (s6 = 0, 88(sp) = F + 32, s7 = g_src's register image, 56(sp) / 48(sp) =
   the two literals, 32(sp) = 0x7fffffff, 40(sp) = s4, 24(sp) = s7; -> the outer head RGO 0 at 0x82e1c).  The proof's
   shape is the image-A twin's (lib/A/W_rig_pro.v on a working branch); the instruction run is B's (objdump of
   fuzz_reply.asan-ubsan from 0x82ca0, listing lib/B/W_listing.v).  The fake frame lies above image B's top by
   rgp_frm_off_imgB_x below (the kit's lib/B/W_frame_b.v frm_off_imgB over ARx). *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record); the image-A twin's
   RIG_x round, a Theorem Labs lane f4cd818e98d): converted IN PLACE to the generic Section of
   lib/B/W_relay_instance_gone_cx.v (commit 258ee8f57ad), any allocator relation ARx with its laws and the room record
   RP.  The prologue runs on the donor journal ajournal_x (YC80x.v SRr_run_pi_tok_AJx); __asan_stack_malloc_1 is ASMP
   (astack_malloc_pres_x, class 1) through W_frame_x.v aj_stack_malloc_pres_at_raw_x with OWNLOW / WFx / WFL /
   SMALLOC (ASMP's frame clause kept, for errno); the lock is alock_realizes_x.  The journal's stack is the kit's
   RIG_STK_x = RIG_STK + 128 (W_contract_x.v rig_spec_x).  At RGO 0 / RGU, GLIVE's journal ends at the entry's head
   set (the seat and the lock keep it), and gbud's room and count are GBASE's: the seat's state is a set_fs of the
   entry's (RPF_of keeps the room) with the same blocks, the lock keeps the state, and the requests still owed at
   entry 0 are gtr by conversion. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a YP07.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin W_frame_b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_instance_gone_cx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
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
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* the plain token runner on the donor journal ajournal_x (W_kit.v paj_run's text over Reusable/YC80x.v), as
   lib/B/W_relay_finish.v's RUN0 *)
Let RUN0 := SRr_run_pi_tok_AJx (SK := SK) wsym SEGS B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) VAL SIGMA
fr_prog_listing (@pl_tpi fr_prog_listing PL_fr) (@pl_tw fr_prog_listing PL_fr) pa_fetch_ok pa_cert pa_B_ok A_LIM
A_LIM_text (@pl_lim fr_prog_listing PL_fr) (@pl_len fr_prog_listing PL_fr) (@pl_tpi_eq fr_prog_listing PL_fr)
(@pl_tw_eq fr_prog_listing PL_fr).
Let RUN := paj_run_x_x B PST ARx LAWS (G_RIG B RG) HGRIG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_RIG B RG) HGRIG 0 [].
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ_x (PL := PL_fr) B PST ARx LAWS. Let RUNTOP := SRr_run_to_pi_AJ_x (PL := PL_fr) B PST ARx LAWS.
Let RUNC := SRr_run_pi_AJ_call_x (PL := PL_fr) B PST ARx LAWS.
Definition rgp_Bx : sv := SOff 33 0.
Definition rgp_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rgp_regions0 : smem :=
[ stack_region RIG_FRAME; got_regionP; bcell_regionP 33; uar_got_regionP 32; uar_cell_regionP 32 ].
Definition rgp_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF 0x10000 0x5fc000 2); (33%nat, mkAF SB SB 0) ].
Definition ss_rgp0 : sstate := mkSS A_rig_entry sr_atoms rgp_regions0 None (mkFacts rgp_atoms0 [] []).
Definition rgp_extra : list word := map (Z_to_bv 64) [as_uar_cell B; SB].
Lemma rgp_entry : forall W ly S Hp regs mem md ch,
afn_pre_x SEGS B ARx RIG_STK_x ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs rgp_extra)) ss_rgp0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_rig_entryP) mem (seg_rom SEGS)))
/\ sh_ok SEGS rgp_Bx [] (Eimg (Ereg regs rgp_extra)) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch HPRE H32.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : RIG_STK_x = 17232) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs rgp_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E247 : ew E (A_OBJ 6) = Z_to_bv 64 (VAL (A_OBJ 6))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E271 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 6 ltac:(lia)) as Hob6. pose proof (pa_obj_img 30 ltac:(lia)) as Hob30.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_rgp0, A_rig_entryP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rgp_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, RIG_FRAME.
    repeat apply Forall_cons; try apply Forall_nil.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
      [cbn [sv_denot]; rewrite E271, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E271) by (pose proof (pa_val_range (A_OBJ 30)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 (SOff 33 0) SB);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB (A_OBJ 6) (VAL (A_OBJ 6)) E247) by (pose proof (pa_val_range (A_OBJ 6)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 6)) 0 8 (SOff 32 0) (as_uar_cell B));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 32%nat (as_uar_cell B) E32) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
  + apply pairwise_disjoint_of_extents.
    unfold rgp_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region, RIG_FRAME.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 32%nat (as_uar_cell B) E32) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E271) by (pose proof (pa_val_range (A_OBJ 30)); lia).
    rewrite (VB (A_OBJ 6) (VAL (A_OBJ 6)) E247) by (pose proof (pa_val_range (A_OBJ 6)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hob0 Hob6 Hob30 Huar Hsep. clear.
    unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
    repeat split; first [ assumption | (apply or_comm; assumption)
    | (repeat match goal with H : pa_val (A_OBJ _) + 8 <= _ \/ _ |- _ => clear H | H : as_uar_cell _ + 4 <= _ \/ _ |- _ => clear H end; lia) ].
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok rgp_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 5) with 32. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hal16 H32 Huar Huar4. clear.
    unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok. constructor.
Qed.
(* The footprint of relay_instance_gone's journal names heap blocks only, so it is closed to the sink. *)
Lemma rgp_fp_closed : forall ly S Hp W mem md bl rest,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (bl ++ rest) -> ~ YI16.sink_open_fp (ablocks_fp bl).
Proof.
intros ly S Hp W mem md bl rest HAR HP. apply sink_closed_ablocks_fp. apply Forall_forall. intros [p n] Hin.
assert (Hb : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hin).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hb) as (_ & H4096 & _). cbn [fst]. lia.
Qed.
(* ---- Facts about the footprints the cut predicates read: every byte is a global cell or in a live block. ---- *)
Definition rgp_blk (ly : alayout) (S : astate) (a : Z) : Prop :=
exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n.
Lemma rgp_blk_of : forall ly S p n a, In (p, n) (ablocks B ly S) -> 0 <= n -> p <= a -> a < p + n -> rgp_blk ly S a.
Proof.
intros ly S p n a Hb Hn H1 H2. exists p, n. split; [exact Hb|].
pose proof (req_size_pos n Hn) as [_ Hr]. lia.
Qed.
Lemma rgp_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.
Lemma rgp_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.
Lemma rgp_aentry_fp : forall ly S (W : world SEGS) mem e, aentry_ok B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> rgp_blk ly S a.
Proof.
intros ly S W mem e HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (rgp_blk_of ly S (re_buf e) (re_cap e) a Hin); lia.
- destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, rgp_key_ptrs_len in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. cbn [length] in Ha. lia.
    * unfold re_nheld in Hk1. apply (rgp_blk_of ly S (re_hp e) (re_kh e) a Hin); lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
    apply (rgp_blk_of ly S (key_addr k) (Z.of_nat (length (key_text k)) + 1) a Hin); lia.
Qed.
Lemma rgp_alist_fp : forall ly S (W : world SEGS) mem LA l lines, alist_at B ly S W mem LA l lines ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> (LA <= a < LA + 16) \/ rgp_blk ly S a.
Proof.
intros ly S W mem LA l lines HL r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- left. cbn [fst snd] in Ha. exact Ha.
- right. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, rgp_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    unfold hl_n in Hn, Hj. unfold AREC in *.
    apply (rgp_blk_of ly S (hl_v l) (16 * hl_cap l) a Hin); lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
    apply (rgp_blk_of ly S (fst q) (Z.of_nat (length (snd q)) + 1) a Hin); lia.
Qed.
Lemma rgp_asrc_fp : forall ly S (W : world SEGS) mem HA h, asrc_at B ly S W mem HA h ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> (HA <= a < HA + ASRC) \/ rgp_blk ly S a.
Proof.
intros ly S W mem HA h HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpe & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ & Hex & Hhe & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- left. cbn [fst snd] in Ha. exact Ha.
- right. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  apply (rgp_blk_of ly S (hs_partial h) APARTIAL a Hpb); unfold APARTIAL in *; lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr]; [|apply in_app_or in Hr; destruct Hr as [Hr | Hr]].
  + destruct (rgp_alist_fp ly S W mem _ _ _ Hpe r Hr a Ha) as [Hx | Hx]; [left; unfold ASRC; lia | right; exact Hx].
  + destruct (rgp_alist_fp ly S W mem _ _ _ Hex r Hr a Ha) as [Hx | Hx]; [left; unfold ASRC; lia | right; exact Hx].
  + destruct (rgp_alist_fp ly S W mem _ _ _ Hhe r Hr a Ha) as [Hx | Hx]; [left; unfold ASRC; lia | right; exact Hx].
Qed.
(* Two cells of a pairwise-apart list are apart. *)
Lemma rgp_zall : forall x l j d, zall_disjoint x l -> (j < length l)%nat -> zdisj x (nth j l d).
Proof.
intros x l. induction l as [|y l IH]; intros j d H Hj; [cbn in Hj; lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | cbn in Hj; lia].
Qed.
Lemma rgp_zpd : forall l i j d, zpairwise_disjoint l -> (i < j < length l)%nat -> zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|x l IH]; intros i j d H Hij; [cbn in Hij; lia|].
destruct H as [H1 H2]. destruct i as [|i]; destruct j as [|j]; try lia.
- cbn [nth]. apply rgp_zall; [exact H1 | cbn in Hij; lia].
- cbn [nth]. apply IH; [exact H2 | cbn in Hij; lia].
Qed.
(* YCbq.v region_kept_stack_aj over YCbqG.v's journal ajournal_x (no kit twin; the image-A twin's
   rgp_region_kept_stack_aj_x, the same proof: it reads only the journal's stack presence and stack geometry and the
   call's acall_kept frame clause) *)
Lemma rgp_region_kept_stack_aj_x : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs sp0 sp
STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
ajournal_x (SK := SK) SEGS B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k
(K1 & _) HJ Hn Hshi Hlo Hhi Hw1 Hw2.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply K1; lia.
- intros _. apply (apresent_writable SEGS). apply Hpres. lia.
Qed.
(* W_frame_b.v frm_off_imgB over ARx: a live fake frame lies off image B's [0x10000, 0x5fc000) - at or above the
   image's top (the image law alx_img), which IMGC puts at or above 0x5fc000 (W_frame_x.v frm_off_imgP_x's proof;
   its off_img is image A's top 0x5fb000, too weak for B's objects) *)
Lemma rgp_frm_off_imgB_x : forall ly S Hp (W : world SEGS) mem md cid pos,
ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos + fs_frame_bytes cid <= 0x10000 \/ 0x5fc000 <= frame_addr ly cid pos.
Proof.
intros ly S Hp W mem md cid pos HAR Hin.
destruct (IMGC ly S Hp W mem md HAR) as [_ C2].
pose proof (proj2 (alx_img _ _ _ LAWS ly S Hp W mem md HAR) cid pos Hin) as Hf.
right. lia.
Qed.
Ltac rgp_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* a cell of HRGP (index i) is apart from cell j: Ha places the byte in one of them *)
Ltac rgp_off i j Ha :=
let D := fresh "D" in
lazymatch goal with HP : zpairwise_disjoint _ |- _ =>
pose proof (rgp_zpd _ i j (0, 0) HP ltac:(cbn [length]; lia)) as D end;
cbn [nth] in D; unfold zdisj in D; cbn [fst snd] in D; clear - D Ha; lia.
Ltac rgp_tls n := lazymatch n with O => idtac | S ?m => apply Exists_cons_tl; rgp_tls m end.
Ltac rgp_ing k Ha := unfold G_RIG, G_DR, G_SL, inG; rgp_tls k; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; clear - Ha; lia.
Ltac rgp_nowr2 U2 U245 :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2, ?U245 in Hr; lia | ]);
destruct Hin.
Ltac rgp_regeq Q U := rewrite Q; apply bv_eq; unfold w64; rewrite U; rewrite ?unsigned_lit_small by (unfold SB in *; lia); unfold SB in *; lia.
Theorem rig_pro : rig_pro_stmt B PST ARx MT RP MMAX RG.
Proof.
intros cx HB KO KU.
destruct cx as [regs ly S Hpe W mem md ch G0 ID es hs c O mx cap out rest kr].
unfold GBASE, gsp0, gps, gtr in HB.
cbn [gxregs gxly gxS gxHp gxW gxmem gxmd gxch gxG0 gxID gxes gxhs gxc gxO gxmx gxcap gxout gxrest gxkr] in HB |- *.
destruct HB as (HPRE & H32 & HCNT & RGP & H10 & RID & Hlock & HREL & HOUT & HROM & HLEN & HDRS & HNODUP & HPERM & HTRM & HLIVE & HMOK
  & HRMe & HCNTe).
set (cx := mkGcx regs ly S Hpe W mem md ch G0 ID es hs c O mx cap out rest kr) in *.
destruct RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
assert (RGIM : forall a, (rg_lock RG <= a < rg_lock RG + 12 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
  rg_src RG <= a < rg_src RG + 8) -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4)) by (intros a Ha; apply RGIMG; unfold rg_rng; tauto).
assert (RGAL : rg_lock RG mod 8 = 0 /\ rg_nsrc RG mod 4 = 0 /\ rg_src RG mod 8 = 0)
  by (split; [exact RGAL8 | split; [exact RGAL4 | exact RGSAL]]).
assert (GSEP : forall a, (rg_lock RG <= a < rg_lock RG + 12 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
  rg_src RG <= a < rg_src RG + 8) -> ~ (VAL (A_OBJ 0) <= a < VAL (A_OBJ 0) + 8) /\
  ~ (VAL (A_OBJ 6) <= a < VAL (A_OBJ 6) + 8) /\ ~ (VAL (A_OBJ 30) <= a < VAL (A_OBJ 30) + 8) /\
  ~ (as_uar_cell B <= a < as_uar_cell B + 4)) by (intros a Ha; apply RGSEP; unfold rg_rng; tauto).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (rgp_entry W ly S Hpe regs mem md ch HPRE H32) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx RIG_STK_x (rig_fp G0 es hs cap out) ly S Hpe W regs mem md ch HPRE) as HJ.
assert (HFPcl : ~ YI16.sink_open_fp (rig_fp G0 es hs cap out)).
{ unfold rig_fp.
  apply (rgp_fp_closed ly S Hpe W mem md _ rest (proj1 HPRE)). cbn [app]. rewrite <- !app_assoc. exact HPERM. }
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs rgp_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs rgp_extra) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17232) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (SPR : 2 ^ 46 <= spZ regs <= 2 ^ 47).
{ revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 H32. clear.
  unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
unfold cfg_at. change (w64 A_rig_entryP) with (Z_to_bv 64 A_rig_entryP). unfold A_rig_entryP, A_rig_entry.
paj_run_tok_x RUN0 HS HJ SHOK rgp_Bspan. { awr_ok_tac. exact Usp. }
(* the call to __asan_stack_malloc_1 (128): the fake frame (ASMP through W_frame_x.v aj_stack_malloc_pres_at_raw_x:
   ASMP's frame clause kept in the post, so errno's view crosses the call) *)
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite (palf_sm1 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply (aj_stack_malloc_pres_at_raw_x SEGS B PST ARx LAWS Hsegs (pal_env B TL) OWNLOW WFx WFL SMALLOC 1 ASMP ltac:(lia)
    W rg mm RIG_STK_x (spZ regs) (rig_fp G0 es hs cap out) ly S Hpe W mem md [] ly S Hpe _ 0 (-224) _ HJ) end.
  - unfold spZ at 1. rewrite R2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). lia.
  - reflexivity. - lia. - rewrite WS, Hes. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp. - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HCNT. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HKgrow & HFRM & HFS).
(* the room round: the seat's state is a set_fs of S, so RPF_of carries GBASE's room to it (the lock keeps it) *)
assert (HRM2 : rp_RM RP S2 (Z.to_nat (tr_cost MT_rk (rig_tr c mx (Z.of_nat (length O)) cap ID es hs)) + kr))
by (destruct HFS as (f & ->); exact (RPF_of RP _ _ _ HRMe)).
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
pose proof (proj1 HJ) as HARa. pose proof (proj1 HJ2) as HARb. clear HJ.
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARa) as (Kc1 & Ku1 & Kg1 & Kgu1).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARb) as (Kc2 & Ku2 & Kg2 & Kgu2).
rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2. rewrite (palf_got_uar B TLF) in Kgu1, Kgu2.
pose proof (palf_uar_img B TLF) as HuR.
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | apply Forall_nil].
  - eapply rgp_region_kept_stack_aj_x; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 30)));
    [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 30) (VAL (A_OBJ 30)) 8 SHADOW_OFF);
    [exact (HEI (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 6) (VAL (A_OBJ 6)) 8 (as_uar_cell B));
    [exact (HEI (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu2) | lia].
  - apply (region_kept_val_at E _ _ 32 (as_uar_cell B) 4 1);
    [rewrite E32; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku1) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku2) | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 34)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs rgp_extra) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
prreg HS (10%bv : bv 5) RF.
(* seat the fake frame: F at atom 38 (a0), its flag FL at 512, the frame's shadow SB + F / 8 at 513 *)
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 fpos HARb Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 1 fpos HARb Hfin2) as (HFal & HFapp & HFpres & HFSpres).
pose proof (rgp_frm_off_imgB_x _ _ _ _ _ _ 1 fpos HARb Hfin2) as HFimg.
destruct (FFL _ _ _ _ _ _ 1 fpos HARb Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
fold F FL in HFal, HFapp, HFpres, HFSpres, HFimg, HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc, HF4096, HFceil, HFhigh.
assert (RF' : ew Ea 38 = Z_to_bv 64 F) by (rewrite <- RF, Ha0; reflexivity).
assert (E33a : ew Ea 33 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E33).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 6 ltac:(lia)) as HguR.
pose proof (palf_sep B TLF) as HSEP. cbn [zseps zseps_from fst snd] in HSEP.
pose proof (pa_val_range (A_OBJ 0)). pose proof (pa_val_range (A_OBJ 6)). pose proof (pa_val_range (A_OBJ 30)).
pose proof (st_ok_pi_havoc_hi 512 Ea _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc Ea 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 512)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (E512 : ew Eb 512 = Z_to_bv 64 FL) by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E513 : ew Eb 513 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAEb : env_agree 32 (Ereg regs rgp_extra) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (E38 : ew Eb 38 = Z_to_bv 64 F) by (rewrite OLDb by lia; exact RF').
assert (E33b : ew Eb 33 = Z_to_bv 64 SB) by (rewrite OLDb by lia; exact E33a).
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
pose proof (st_ok_pi_add_fact Eb _ _ 38 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E38, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_fact Eb _ _ 512 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E512, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_fact Eb _ _ 513 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E513, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_alias Eb _ _ _ _ HS (shadow_decl_ok Eb 38 33 513 F SB E38 ltac:(lia) E33b E513)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
assert (U2b : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb, OLDa by lia; exact Usp).
assert (U241 : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)) by exact (HEIb (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U247 : bv_unsigned (ew Eb 247) = VAL (A_OBJ 6)) by exact (HEIb (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U271 : bv_unsigned (ew Eb 271) = VAL (A_OBJ 30)) by exact (HEIb (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U32 : bv_unsigned (ew Eb 32) = as_uar_cell B) by (rewrite OLDb, OLDa, E32 by lia; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew Eb 38) = F) by (rewrite E38; apply unsigned_lit_small; lia).
assert (U512 : bv_unsigned (ew Eb 512) = FL) by (rewrite E512; apply unsigned_lit_small; lia).
assert (U513 : bv_unsigned (ew Eb 513) = SB + F / 8) by (rewrite E513; apply unsigned_lit_small; unfold SB; lia).
pose proof (st_ok_pi_add_region Eb _ _ (fframe_region 38 512 1 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1) with 128; rewrite U38; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Eb _ F (128 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E512, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (128 - 8)) with (F + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1) with 128; rewrite U38, U2b, U241, U247, U271, U32;
unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Eb _ _ (fshadow_region 513 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1 / 8) with 16; rewrite U513; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres; apply (proj1 (HFSpres o ltac:(lia)))
| unfold zero_shadow, shadow_of_addr in Hz; rewrite <- SB_SHADOW_OFF in Hz;
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
[ apply (chunk_ok_val SEGS Eb _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside |];
  rewrite Z.add_0_r; apply val_mem_zero8; intros i Hi; apply Hz; change (128 / 8) with 16; lia
| apply (chunk_ok_val SEGS Eb _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside |];
  apply val_mem_zero8; intros i Hi; replace (SB + F / 8 + 8 + i) with (SB + F / 8 + (8 + i)) by lia; apply Hz; change (128 / 8) with 16; lia ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1 / 8) with 16; change (fs_frame_bytes 1) with 128; rewrite U513, U38, U2b, U241, U247, U271, U32;
unfold SB, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
(* the frame header and the shadow poison: a plain run, stopping at pthread_mutex_lock *)
paj_run_shc_x RUNP RUNC HS HJ2.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2b, ?U38, ?U513, ?U241, ?U247, ?U271, ?U32 in Hr;
    first [ lia
    | left; unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia
    | right; right; right; exists 1, fpos; split; [left; reflexivity|];
      change (frame_addr ly 1 fpos) with F; change (fs_frame_bytes 1) with 128;
      first [ left; unfold in_zr; cbn [fst snd]; lia
      | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (128 / 8) with 16; lia ] ]
  | ]).
  destruct Hin. }
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0.
(* the call to pthread_mutex_lock (&g_lock) *)
eassert (HJX : ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (spZ regs) (rig_fp G0 es hs cap out)
  ly S Hpe W mem md _ _ _ _ _ _ _ _).
{ eapply ajournal_gx_pack_x; [rewrite WS; lia | lia | rewrite !Z.add_0_r; exact HJ2 | apply gagree_refl | intros a Ha Hn; lia]. }
(* the program statics PST hold no byte of the cells the walk carries (PSTG), so the journal's image clause, which
   exempts PST, speaks of them *)
assert (PSG : forall a, inG (G_RIG B RG) a -> ~ Exists (in_zr a) PST) by (intros a Ha; apply PSTG; left; exact Ha).
assert (PSL : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ Exists (in_zr a) PST)
by (intros a Ha; apply PSG; rgp_ing 0%nat Ha).
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Hi Ho He Hps. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H11 & _).
  exact (H11 a Hi Ho He Hps (fp_spares_closed (rig_fp G0 es hs cap out) a HFPcl)). }
pose proof Hlock as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
pose proof (pa_obj_img 3 ltac:(lia)) as HlkR. rewrite <- RGLOCK in HlkR.
assert (LKI : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a Ha; exact (RGIM a (or_introl Ha))).
assert (LKK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a)
by (intros a Ha; destruct (LKI a Ha) as (Hi & Ho & He); exact (KIMG a Hi Ho He (PSL a Ha))).
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) mem a <> None).
{ intros a Ha. unfold aview.
  destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
  - pose proof (LK0 (Z.to_nat (a - rg_lock RG)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + (a - rg_lock RG)) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK4 (Z.to_nat (a - (rg_lock RG + 4))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 4 + (a - (rg_lock RG + 4))) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK8 (Z.to_nat (a - (rg_lock RG + 8))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 8 + (a - (rg_lock RG + 8))) with a in X by lia. rewrite X. discriminate. }
assert (LKtb : aview SEGS (w_H W) (ms_mem ms0) (rg_lock RG) = Some 0).
{ rewrite (LKK (rg_lock RG) ltac:(lia)). unfold aview. pose proof (LK0 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X.
  rewrite Z.add_0_r in X. rewrite X. vm_compute. reflexivity. }
assert (LK4m : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (rg_lock RG + 4) 4 0).
{ apply (val_mem_moved SEGS (w_H W) (w_H W) mem (ms_mem ms0) (rg_lock RG + 4) (rg_lock RG + 4) 4 0); [|exact LK4].
  intros kk Hk. apply LKK. cbn in Hk. lia. }
assert (HSPc : spZ (ms_regs ms0) = spZ regs + -224).
{ unfold spZ at 1. rewrite QSP, U2b. rewrite unsigned_lit_small by (unfold spZ in *; lia). lia. }
assert (QA0' : getr (ms_regs ms0) 10 = w64 (rg_lock RG)).
{ rewrite QA0. change 244%nat with (A_OBJ 3). rewrite (img_env_atomP Eb (A_OBJ 3) HEIb ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite RGLOCK. reflexivity. }
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS (G_RIG B RG) 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (_ : bvmap 5 word) (mem' : word -> option byte) => val_mem SEGS (mrestrict (w_H W) mem') (rg_lock RG + 4) 4 16)
    W _ _ RIG_STK_x (spZ regs) (rig_fp G0 es hs cap out) ly S Hpe W mem md _ _ _ _ _ _ (-224) _ HGRIG eq_refl HJX).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite QGP, OLDb, OLDa, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite QTP, OLDb, OLDa, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - exact QRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
    destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
  - intros a Ha _. rewrite (LKK a ltac:(lia)). exact (LKV a ltac:(lia)).
  - intros a Ha HnG. exfalso. apply HnG. unfold G_RIG. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
  - intros HPRE2 HSC. apply (ALOCK _ _ _ _ _ _ _ (rg_lock RG) 0 HPRE2).
    + exact QA0'.
    + lia.
    + destruct RGAL as (RGAL0 & _ & _). pose proof (Z.div_mod (rg_lock RG) 8 ltac:(lia)).
      pose proof (Z.div_mod (rg_lock RG) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (rg_lock RG) 4 ltac:(lia)). lia.
    + lia.
    + exact LKtb.
    + reflexivity.
    + exact LK4m.
    + intros a Ha. split; [rewrite (LKK a ltac:(lia)); exact (LKV a ltac:(lia))|]. rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha. destruct (LKI a ltac:(lia)) as (Hi & Ho & He). split; [|split].
      * apply (RGWR (w_H W) (ms_mem ms0) a); [left; lia | exact (hidden_not_img SEGS W (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; exact Hi))].
      * intros Hown. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a (proj1 HJ2) Hi) Hown).
      * rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha HKw1. apply (proj2 (proj2 (HGRIG a ltac:(unfold G_RIG, inG; apply Exists_cons_hd; unfold in_zr;
        cbn [fst snd]; lia)))). exact (proj1 (proj2 HKw1)). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJX3 & HP3 & HLK3 & Hfr3 & Hpres3).
(* reseat: the lock wrote only g_lock + 4 .. + 8, which no region of the state covers *)
jafter_call_keep_hi HS 514%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  pose proof HFapp as HFA. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFA.
  pose proof HFimg as HFI.
  pose proof (palf_uar_img B TLF) as HUI.
  assert (LKlo : forall a, rg_lock RG <= a < rg_lock RG + 12 -> 0 <= a < 2 ^ 64) by (intros a Ha; lia).
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
    ~ (spZ regs + -224 - ESTACK <= a < spZ regs + -224) ->
    aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) (ms_mem ms0) a)
  by (intros a Hq1 Hq2 Hq3; apply Hfr3; [exact Hq1 | exact Hq2 | exact Hq3]).
  repeat apply Forall_cons; [| | | | | | | apply Forall_nil].
  - (* fshadow 513 *) apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 513 (SB + F / 8) 0 16);
    [exact U513 | intros a Ha; apply KEEP3; unfold SB in *; rewrite ?Hes; lia | exact Hpres3].
  - (* fframe 38 *) apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 38 F 0 128);
    [exact U38 | intros a Ha; apply KEEP3; rewrite ?Hes; lia | exact Hpres3].
  - (* stack *) apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 2 (spZ regs) (-224) 0);
    [exact U2b | intros a Ha; apply KEEP3; rewrite ?Hes; lia | exact Hpres3].
  - (* got A_OBJ 0 *) apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 241 (VAL (A_OBJ 0)) 0 8);
    [exact U241 | intros a Ha; apply KEEP3;
     [lia | intros Hw; assert (HL : rg_lock RG <= a < rg_lock RG + 12) by lia;
            destruct (GSEP a (or_introl HL)) as (N0 & _ & _ & _); apply N0; lia | rewrite ?Hes; lia] | exact Hpres3].
  - (* bcell A_OBJ 32 *) apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 271 (VAL (A_OBJ 30)) 0 8);
    [exact U271 | intros a Ha; apply KEEP3;
     [lia | intros Hw; assert (HL : rg_lock RG <= a < rg_lock RG + 12) by lia;
            destruct (GSEP a (or_introl HL)) as (_ & _ & N32 & _); apply N32; lia | rewrite ?Hes; lia] | exact Hpres3].
  - (* uar got A_OBJ 1 *) apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 247 (VAL (A_OBJ 6)) 0 8);
    [exact U247 | intros a Ha; apply KEEP3;
     [lia | intros Hw; assert (HL : rg_lock RG <= a < rg_lock RG + 12) by lia;
            destruct (GSEP a (or_introl HL)) as (_ & N1 & _ & _); apply N1; lia | rewrite ?Hes; lia] | exact Hpres3].
  - (* uar cell *) apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 32 (as_uar_cell B) 0 4);
    [exact U32 | intros a Ha; apply KEEP3;
     [lia | intros Hw; assert (HL : rg_lock RG <= a < rg_lock RG + 12) by lia;
            destruct (GSEP a (or_introl HL)) as (_ & _ & _ & Nu); apply Nu; lia | rewrite ?Hes; lia] | exact Hpres3]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
(* ---- At 0x82dcc, after the lock.  The environment, and what the state shows of the frame. ---- *)
remember (havoc Eb 514 (map (getr regs3) CLOB)) as Ec eqn:HEc in HS.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc_hi; [exact HEIb | cbv; lia]).
assert (OLDc : forall m, (m < 514)%nat -> ew Ec m = ew Eb m) by (intros m Hm; rewrite HEc; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEc : env_agree 32 (Ereg regs rgp_extra) Ec) by (rewrite HEc; apply env_agree_havoc_ge; [cbv; lia | exact HAEb]).
clear HEc.
assert (U2c : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLDc by lia; exact U2b).
assert (U38c : bv_unsigned (ew Ec 38) = F) by (rewrite OLDc by lia; exact U38).
assert (SVc : forall n v, (n < 514)%nat -> ew Eb n = Z_to_bv 64 v -> sv_denot Ec (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn Hv. cbn [sv_denot]. rewrite (OLDc n Hn), Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (UR : forall (r : bv 5), 0 <= bv_unsigned (getr regs r) < 2 ^ 64).
{ intros r. pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
assert (EBR : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 34)%nat -> ew Eb n = Z_to_bv 64 (bv_unsigned (getr regs r))).
{ intros n r Hn Hn34. rewrite OLDb, OLDa, (EE n r Hn) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  pose proof (st_ok_pi_region_nth Ec ss _ 1 _ HS eq_refl) as RFR;
  pose proof (st_ok_pi_region_nth Ec ss _ 2 _ HS eq_refl) as RST end.
cbn [ms_mem restrict mkst] in RFR, RST.
assert (FLm3 : val_mem SEGS (mrestrict (w_H W) mem3) (F + 120) 8 FL).
{ exact (field_of_region Ec _ 38 F _ 0 128 0 128 120 8%N (SOff 512 0) FL RFR U38c ltac:(rgp_in)
    (SVc 512%nat FL ltac:(lia) E512) ltac:(zside) ltac:(zside)). }
assert (S8 : val_mem SEGS (mrestrict (w_H W) mem3) (spZ regs + -216) 8 F)
by exact (slot_of_region Ec _ _ _ _ _ _ _ (-216) (SOff 38 0) F RST U2c ltac:(rgp_in) (SVc 38%nat F ltac:(lia) E38) ltac:(lia)).
assert (S16 : val_mem SEGS (mrestrict (w_H W) mem3) (spZ regs + -208) 8 F)
by exact (slot_of_region Ec _ _ _ _ _ _ _ (-208) (SOff 38 0) F RST U2c ltac:(rgp_in) (SVc 38%nat F ltac:(lia) E38) ltac:(lia)).
assert (S112 : val_mem SEGS (mrestrict (w_H W) mem3) (spZ regs + -112) 8 F)
by exact (slot_of_region Ec _ _ _ _ _ _ _ (-112) (SOff 38 0) F RST U2c ltac:(rgp_in) (SVc 38%nat F ltac:(lia) E38) ltac:(lia)).
assert (S72 : val_mem SEGS (mrestrict (w_H W) mem3) (spZ regs + -152) 8 (bv_unsigned (getr regs 10)))
by exact (slot_of_region Ec _ _ _ _ _ _ _ (-152) (SOff 10 0) _ RST U2c ltac:(rgp_in)
  (SVc 10%nat _ ltac:(lia) (EBR 10%nat 10%bv eq_refl ltac:(lia))) (UR 10%bv)).
assert (SAV : forall i, (i < 13)%nat -> val_mem SEGS (mrestrict (w_H W) mem3) (spZ regs + (-104 + 8 * Z.of_nat i)) 8
  (bv_unsigned (getr regs (nth i RIG_SAVED 0%bv)))).
{ intros i Hi.
  do 13 (destruct i as [|i]; [
    lazymatch goal with |- val_mem _ _ (spZ regs + (-104 + 8 * Z.of_nat ?k)) 8 (bv_unsigned (getr regs (nth ?k' RIG_SAVED 0%bv))) =>
      let od := eval vm_compute in (-104 + 8 * Z.of_nat k) in
      let r := eval vm_compute in (nth k RIG_SAVED 0%bv) in
      let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
      change (spZ regs + (-104 + 8 * Z.of_nat k)) with (spZ regs + od);
      change (nth k' RIG_SAVED 0%bv) with r;
      exact (slot_of_region Ec _ _ _ _ _ _ _ od (SOff n 0) _ RST U2c ltac:(rgp_in)
        (SVc n _ ltac:(lia) (EBR n r eq_refl ltac:(lia))) (UR r)) end|]).
  lia. }
clear RFR RST.
(* the image bytes the walk keeps (the journal, then the lock's frame), the blocks and errno (each step's frame) *)
assert (KG3 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Hi Ho He Hps Hl. pose proof (Hsegs a Hi) as Hlo.
  rewrite (Hfr3 a ltac:(unfold kLowMemEnd in Hlo; lia) Hl ltac:(unfold ESTACK, kLowMemEnd in *; lia)).
  exact (KIMG a Hi Ho He Hps). }
assert (NOWR1 : forall a, a < spZ regs - 224 -> ~ in_wrange E (ss_mem ss_rgp0) a).
{ intros a Ha (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
     rewrite ?Usp in Hr; lia | ]).
  destruct Hin. }
assert (Hb2 : forall p n, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly S2)) by (intros p n Hb; rewrite Eab; exact Hb).
assert (KH3 : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros p n a Hb Ha.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hb) as (_ & Hp4096 & Hpc & Hpapp & _).
  assert (HnI : ~ in_img SEGS a)
    by (exact (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hb Ha))))))).
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly S2 _ W mem2 md2 p n 1 fpos HARb (Hb2 p n Hb) Hfin2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr ly 1 fpos) with F in Hd. change (fs_frame_bytes 1) with 128 in Hd.
  rewrite (Hfr3 a ltac:(lia) ltac:(intros Hl; apply HnI; exact (proj1 (LKI a ltac:(lia))))
    ltac:(unfold ESTACK; lia)).
  rewrite (aview_kept_out Eb _ (w_H W) mem2 (ms_mem ms0) HFr0 a ltac:(lia)).
  2: { intros (r & Hin & Hr).
       lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
       cbn [In] in Hin.
       repeat (destruct Hin as [<- | Hin];
         [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U513, ?U38, ?U2b, ?U241, ?U247, ?U271, ?U32 in Hr;
          first [ lia | exfalso; refine (fshadow_not_app F 16 p (req_size n) a HF4096 _ Hpapp _ Ha); unfold SB in *; lia ] | ]).
       destruct Hin. }
  replace a with (p + (a - p)) by lia.
  rewrite (proj1 (proj2 HK) p n (a - p) Hb ltac:(lia) ltac:(intros [])).
  replace (p + (a - p)) with a by lia.
  exact (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a ltac:(lia) (NOWR1 a ltac:(lia))). }
assert (FRNI : forall x, F <= x < F + 128 -> ~ in_img SEGS x).
{ intros x Hx. exact (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ x HARb (or_intror (or_introl (ex_intro _ 1 (ex_intro _ fpos (conj Hfin2 Hx))))))). }
assert (KE3 : forall a, as_errno B <= a < as_errno B + 4 -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Ha. pose proof (pal_env B TL) as ((He0 & He1) & Heimg & _).
  assert (Hi : in_img SEGS a) by (apply Heimg; exact Ha).
  assert (HGe : inG (G_RIG B RG) a) by (rgp_ing 7%nat Ha).
  destruct (HGRIG a HGe) as (_ & Hno & _).
  rewrite (Hfr3 a ltac:(lia) ltac:(rgp_off 0%nat 14%nat Ha) ltac:(unfold ESTACK, kLowMemEnd in *; lia)).
  rewrite (aview_kept_out Eb _ (w_H W) mem2 (ms_mem ms0) HFr0 a ltac:(lia)).
  2: { intros (r & Hin & Hr).
       lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
       cbn [In] in Hin.
       repeat (destruct Hin as [<- | Hin];
         [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U513, ?U38, ?U2b, ?U241, ?U247, ?U271, ?U32 in Hr;
          first [ unfold SB, kLowMemEnd in *; lia
          | exact (FRNI a ltac:(lia) Hi) ] | ]).
       destruct Hin. }
  rewrite (HFRM a ltac:(lia) (fun Ho => Hno (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR Hi) Ho))
    (fun Ho => Hno (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARb Hi) Ho)) ltac:(unfold ESTACK, kLowMemEnd in *; lia)).
  exact (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a ltac:(lia) (NOWR1 a ltac:(unfold kLowMemEnd in *; lia))). }
assert (PRI3 : forall a, in_img SEGS a -> apresent (w_H W) mem a -> apresent (w_H W) mem3 a).
{ intros a Hi Hp. apply Hpres3. apply (apresent_grows _ _ _ a HG0). apply (HKgrow a Hi). exact (apresent_grows _ _ _ a HG Hp). }
pose proof HREL as (RL1 & RL2 & RL3 & RL4 & RL5 & RL6 & RL7 & RL8 & RL9 & RL10 & RL11).
assert (NS3 : val_mem SEGS (mrestrict (w_H W) mem3) (rg_nsrc RG) 4 (Z.of_nat (length es))).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3 (rg_nsrc RG) 4 _); [|exact RL3].
  intros kk Hk. cbn in Hk. assert (Hk' : rg_nsrc RG <= rg_nsrc RG + kk < rg_nsrc RG + 4) by lia.
  destruct (RGIMG (rg_nsrc RG + kk) ltac:(unfold rg_rng; lia)) as (Hi & Ho & He).
  exact (KG3 _ Hi Ho He (PSTG _ (or_intror (or_intror (or_introl Hk')))) ltac:(rgp_off 0%nat 3%nat Hk')). }
assert (LK3 : alock_at RG W mem3 true).
{ unfold alock_at, arm. split; [|split; [exact HLK3|split]].
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3 (rg_lock RG) 4 0); [|exact LK0].
    intros kk Hk. cbn in Hk. destruct (LKI (rg_lock RG + kk) ltac:(lia)) as (Hi & Ho & He).
    apply KG3; [exact Hi | exact Ho | exact He | apply PSL; lia | lia].
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3 (rg_lock RG + 8) 4 0); [|exact LK8].
    intros kk Hk. cbn in Hk. destruct (LKI (rg_lock RG + 8 + kk) ltac:(lia)) as (Hi & Ho & He).
    apply KG3; [exact Hi | exact Ho | exact He | apply PSL; lia | lia].
  - intros i Hi. unfold arm. destruct (LKI (rg_lock RG + i) ltac:(lia)) as (Hii & _ & _).
    apply (RGWR (w_H W) mem3 (rg_lock RG + i)); [left; lia | exact (hidden_not_img SEGS W (Z_to_bv 64 (rg_lock RG + i)) ltac:(rewrite unsigned_lit_small by (pose proof (Hsegs _ Hii); unfold kLowMemEnd in *; lia); exact Hii))]. }
(* ---- The cut predicates' common part, at any memory the walk reaches from mem3 by storing to 24(sp) .. 96(sp)
   (the id's slot 72(sp) lies inside that window, so its value at memF is a premise). ---- *)
assert (CUT : forall memF mdF kF,
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (spZ regs) (rig_fp G0 es hs cap out)
    ly S Hpe W mem md [(1, fpos)] ly S2 Hpe W memF mdF kF ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -200 <= a < spZ regs + -128) -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem3 a) ->
  val_mem SEGS (mrestrict (w_H W) memF) (spZ regs + -152) 8 (bv_unsigned (getr regs 10)) ->
  (forall a, apresent (w_H W) mem3 a -> apresent (w_H W) memF a) ->
  GLIVE B PST ARx RG cx F FL ly S2 W memF mdF kF /\ GOUT B MT RP MMAX RG cx 0 [] c O cap out 0 ly S2 W memF).
{ intros memF mdF kF HJF KEEPF S72F PRESF.
  assert (HARF : ARx ly S2 Hpe W memF mdF) by (destruct HJF as (_ & _ & (memS & HJi & _) & _); exact (proj1 HJi)).
  assert (KF : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem3 a)
    by (intros a Ha; apply KEEPF; [pose proof asan_consts as (CC1 & _); lia | rewrite WS in Hslo; lia]).
  assert (KBI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
    ~ Exists (in_zr a) PST -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> abyte_kept W mem W memF a).
  { intros a Hi Ho He Hps Hl. pose proof (Hsegs a Hi) as Hlo. split.
    - rewrite (KF a ltac:(unfold kLowMemEnd in Hlo; lia)). exact (KG3 a Hi Ho He Hps Hl).
    - unfold arm. apply writable_kept. intros Hp. apply PRESF. exact (PRI3 a Hi Hp). }
  assert (KBE : forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W mem W memF a).
  { intros a Ha. pose proof (pal_env B TL) as ((He0 & He1) & Heimg & _). split.
    - rewrite (KF a ltac:(unfold kLowMemEnd in *; lia)). exact (KE3 a Ha).
    - unfold arm. apply writable_kept. intros Hp. apply PRESF. exact (PRI3 a (Heimg a Ha) Hp). }
  assert (KBH : forall a, rgp_blk ly S a -> abyte_kept W mem W memF a).
  { intros a (p & n & Hb & Ha).
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hb) as (_ & Hp4096 & Hpc & _ & _).
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HARF (Hb2 p n Hb)) as (_ & _ & _ & _ & HpF & _).
    split.
    - rewrite (KF a ltac:(lia)). exact (KH3 p n a Hb Ha).
    - intros _. unfold arm. apply (apresent_writable SEGS). exact (proj1 (HpF a Ha)). }
  assert (KBS : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W mem W memF a).
  { intros a Ha. destruct (RGIMG a ltac:(unfold rg_rng; lia)) as (Hi & Ho & He).
    exact (KBI a Hi Ho He (PSG a ltac:(rgp_ing 1%nat Ha)) ltac:(rgp_off 0%nat 1%nat Ha)). }
  assert (KBG : forall a, inG (G_RIG B RG) a -> ~ (as_errno B <= a < as_errno B + 4) -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
    abyte_kept W mem W memF a).
  { intros a Hg He Hl. destruct (HGRIG a Hg) as (Hi & Ho & _). exact (KBI a Hi Ho He (PSG a Hg) Hl). }
  assert (KBR : forall a, (rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
    rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
    ~ (as_errno B <= a < as_errno B + 4) -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> abyte_kept W mem W memF a).
  { intros a Hr He Hl. destruct (HRGI a Hr) as (Hi & Ho). exact (KBI a Hi Ho He (PSTG a (or_intror (or_intror (or_intror Hr)))) Hl). }
  assert (HPB : forall b, In b ((G0, ATABLE) :: concat (map aentry_blks es) ++ rig_srcs (combine es hs) ++ aout_blks cap out) ->
    In b (ablocks B ly S2)).
  { intros b Hb. rewrite Eab. apply (Permutation_in _ (Permutation_sym HPERM)).
    destruct Hb as [<- | Hb]; [left; reflexivity | right].
    apply in_app_or in Hb. destruct Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|].
    apply in_or_app; right. apply in_app_or in Hb. destruct Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|].
    apply in_or_app; right. apply in_or_app; left. exact Hb. }
  split.
  - (* GLIVE *)
    unfold GLIVE. exists fpos, Hpe. split; [exact HJF|]. split.
    { eapply (ajournal_gx_rom_view_x SEGS B PST ARx).
      all: first [exact LAWS | exact Hsegs | exact HJF | exact HROMO | exact PSTR | exact HROM]. }
    split; [intros a Hi Ho He Hp; apply PRESF; exact (PRI3 a Hi Hp)|].
    split.
    { unfold g_frame, g_saved, gsp1, gsp0, cx. cbn [gxregs]. unfold RIG_FRAME.
      split; [reflexivity|]. split; [reflexivity|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF (F + 120) 8 FL); [intros kk Hk; cbn in Hk; apply KF; lia | exact FLm3]|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF _ 8 F); [intros kk Hk; cbn in Hk; apply KEEPF; lia | replace (spZ regs - 224 + 8) with (spZ regs + -216) by lia; exact S8]|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF _ 8 F); [intros kk Hk; cbn in Hk; apply KEEPF; lia | replace (spZ regs - 224 + 16) with (spZ regs + -208) by lia; exact S16]|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF _ 8 F); [intros kk Hk; cbn in Hk; apply KEEPF; lia | replace (spZ regs - 224 + 112) with (spZ regs + -112) by lia; exact S112]|].
      split; [replace (spZ regs - 224 + 72) with (spZ regs + -152) by lia; exact S72F|].
      intros i Hi. apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF _ 8 _); [intros kk Hk; cbn in Hk; apply KEEPF; lia|].
      replace (spZ regs - 224 + 120 + 8 * Z.of_nat i) with (spZ regs + (-104 + 8 * Z.of_nat i)) by lia. exact (SAV i Hi). }
    { destruct LK3 as (L0 & L4 & L8 & LW). unfold alock_at, arm in *.
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF _ 4 0); [intros kk Hk; cbn in Hk; destruct (LKI (rg_lock RG + kk) ltac:(lia)) as (Hi & _); pose proof (Hsegs _ Hi); apply KF; unfold kLowMemEnd in *; lia | exact L0]|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF _ 4 _); [intros kk Hk; cbn in Hk; destruct (LKI (rg_lock RG + 4 + kk) ltac:(lia)) as (Hi & _); pose proof (Hsegs _ Hi); apply KF; unfold kLowMemEnd in *; lia | exact L4]|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF _ 4 0); [intros kk Hk; cbn in Hk; destruct (LKI (rg_lock RG + 8 + kk) ltac:(lia)) as (Hi & _); pose proof (Hsegs _ Hi); apply KF; unfold kLowMemEnd in *; lia | exact L8]|].
      intros i Hi. unfold arm. destruct (LKI (rg_lock RG + i) ltac:(lia)) as (Hii & _ & _).
      apply (RGWR (w_H W) memF (rg_lock RG + i)); [left; lia | exact (hidden_not_img SEGS W (Z_to_bv 64 (rg_lock RG + i)) ltac:(rewrite unsigned_lit_small by (pose proof (Hsegs _ Hii); unfold kLowMemEnd in *; lia); exact Hii))]. }
  - (* GOUT 0 *)
    unfold GOUT, gbud, gps, gtr, cx.
    cbn [gxes gxhs gxc gxO gxmx gxcap gxout gxrest gxW gxmem gxS gxHp gxly gxG0 gxID gxkr firstn skipn map app].
    split; [lia|]. split; [reflexivity|]. split; [cbn [rig_rel]; repeat split|].
    split.
    { apply (arelay_at_kept B RG ly S W mem ly S2 W memF G0 es HREL).
      - intros r Hr a Ha. unfold arelay_fp in Hr. cbn [In] in Hr.
        destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
        + destruct (RGIMG a ltac:(unfold rg_rng; lia)) as (Hi & Ho & He).
          exact (KBI a Hi Ho He (PSTG a (or_intror (or_introl Ha))) ltac:(rgp_off 0%nat 2%nat Ha)).
        + destruct (RGIMG a ltac:(unfold rg_rng; lia)) as (Hi & Ho & He).
          exact (KBI a Hi Ho He (PSTG a (or_intror (or_intror (or_introl Ha)))) ltac:(rgp_off 0%nat 3%nat Ha)).
        + exact (KBR a (or_introl Ha) ltac:(rgp_off 4%nat 14%nat Ha) ltac:(rgp_off 0%nat 4%nat Ha)).
        + apply KBH. apply (rgp_blk_of ly S G0 ATABLE a RL8); unfold ATABLE in *; lia.
        + apply in_concat in Hr as (fp & Hfp & Hr). apply in_map_iff in Hfp as (e & <- & He).
          rewrite Forall_forall in RL10. exact (KBH a (rgp_aentry_fp ly S W mem e (RL10 e He) r Hr a Ha)).
      - intros b Hb. apply HPB. destruct Hb as [<- | Hb]; [left; reflexivity | right; apply in_or_app; left; exact Hb]. }
    split.
    { apply (aout_at_kept B RG ly S W mem ly S2 W memF c O mx (Z.of_nat (length O)) cap out HOUT).
      - intros r Hr a Ha. unfold aout_fp in Hr. cbn [In] in Hr.
        destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
        + exact (KBR a (or_intror (or_introl Ha)) ltac:(rgp_off 5%nat 14%nat Ha) ltac:(rgp_off 0%nat 5%nat Ha)).
        + exact (KBG a ltac:(rgp_ing 4%nat Ha) ltac:(rgp_off 6%nat 14%nat Ha) ltac:(rgp_off 0%nat 6%nat Ha)).
        + exact (KBG a ltac:(rgp_ing 5%nat Ha) ltac:(rgp_off 7%nat 14%nat Ha) ltac:(rgp_off 0%nat 7%nat Ha)).
        + exact (KBG a ltac:(rgp_ing 6%nat Ha) ltac:(rgp_off 8%nat 14%nat Ha) ltac:(rgp_off 0%nat 8%nat Ha)).
        + exact (KBR a (or_intror (or_intror (or_introl Ha))) ltac:(rgp_off 9%nat 14%nat Ha) ltac:(rgp_off 0%nat 9%nat Ha)).
        + exact (KBG a ltac:(rgp_ing 2%nat Ha) ltac:(rgp_off 10%nat 14%nat Ha) ltac:(rgp_off 0%nat 10%nat Ha)).
        + exact (KBR a (or_intror (or_intror (or_intror Ha))) ltac:(rgp_off 11%nat 14%nat Ha) ltac:(rgp_off 0%nat 11%nat Ha)).
        + exact (KBG a ltac:(rgp_ing 3%nat Ha) ltac:(rgp_off 12%nat 14%nat Ha) ltac:(rgp_off 0%nat 12%nat Ha)).
        + exact (KBE a Ha).
        + destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []].
          cbn [fst snd] in Ha. pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HO26).
          destruct HO26 as [(Hc & _) | (Hc & _ & Hin & _)]; [lia|].
          apply KBH. apply (rgp_blk_of ly S out cap a Hin); lia.
      - intros b Hb. apply HPB. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
    split; [intros i' Hi'; lia|].
    split.
    { rewrite Forall_forall in HDRS |- *. intros p Hp He.
      destruct (HDRS p Hp He) as (Hj & Hsa & Hot & Hrest).
      split; [exact Hj|]. split.
      - apply (asrc_at_kept B ly S W mem ly S2 W memF _ _ Hsa).
        + intros r Hr a Ha. destruct (rgp_asrc_fp ly S W mem _ _ Hsa r Hr a Ha) as [Hx | Hx].
          * apply KBS. unfold ASRC in *. lia.
          * exact (KBH a Hx).
        + intros b Hb. apply HPB. right. apply in_or_app. right. apply in_or_app. left.
          unfold rig_srcs. apply in_concat. exists (asrc_blks (fst (snd p))). split; [|exact Hb].
          apply in_map_iff. exists p. split; [cbv beta; rewrite (proj2 (Z.eqb_eq _ _) He); reflexivity | exact Hp].
      - split; [|exact Hrest].
        intros i Hi Hne. destruct (Hot i Hi Hne) as (f & o & Vf & Vo & Hfo). exists f, o.
        split; [apply (akept_vm W mem W memF); [intros x Hx; apply KBS; cbn in Hx; unfold ASRC in *; lia | exact Vf]|].
        split; [apply (akept_vm W mem W memF); [intros x Hx; apply KBS; cbn in Hx; unfold ASRC in *; lia | exact Vo] | exact Hfo]. }
    split; [intros a Ha _; exact (KBS a Ha)|].
    split.
    { rewrite Eab. unfold gdone_srcs. cbn [combine map concat app]. exact HPERM. }
    split; [destruct HFS as (f & Ef); rewrite Ef; exact (MO_FR S f)|]. split; [lia|].
    lazymatch goal with |- context [grest ?cxx 0 ?no ?cp] => change (grest cxx 0 no cp) with (rig_tr c mx no cp ID es hs) end.
    rewrite Hbb2. split; [lia|]. split; [exact HLIVE|]. split; [exact HTRM|].
    (* the room round: the seat kept GBASE's room (HRM2) and the blocks (Eab), and entry 0 owes gtr's requests *)
    split; [exact HRM2 | rewrite Eab; exact HCNTe]. }
(* ---- The state for 0x82dcc .. 0x82e1c: the frame (16(sp) = F, 72(sp) = the id; writable at 24(sp) .. 96(sp)) and
   g_nsrc. ---- *)
clear SHOK.
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  pose proof (st_ok_pi_submem Ec ss _ [] HS ltac:(submem_tac) eq_refl) as HS2 end.
clear HS. rename HS2 into HS. norm_ss HS.
pose proof (st_ok_pi_havoc_hi 530 Ec _ _ [Z_to_bv 64 (Z.of_nat (length es))] HS ltac:(vm_compute; reflexivity)) as HS2.
clear HS. rename HS2 into HS.
remember (havoc Ec 530 [Z_to_bv 64 (Z.of_nat (length es))]) as Ed eqn:HEd in HS.
assert (HEId : img_env VAL A_LIM Ed) by (rewrite HEd; apply img_env_havoc_hi; [exact HEIc | cbv; lia]).
assert (OLDd : forall m, (m < 530)%nat -> ew Ed m = ew Ec m) by (intros m Hm; rewrite HEd; apply YN3v.ew_havoc_old; exact Hm).
assert (E530 : ew Ed 530 = Z_to_bv 64 (Z.of_nat (length es)))
  by (rewrite HEd; exact (ew_havoc_new _ 530 [Z_to_bv 64 (Z.of_nat (length es))] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAEd : env_agree 32 (Ereg regs rgp_extra) Ed) by (rewrite HEd; apply env_agree_havoc_ge; [cbv; lia | exact HAEc]).
clear HEd.
assert (U2d : bv_unsigned (ew Ed 2) = spZ regs) by (rewrite OLDd by lia; exact U2c).
assert (U38d : bv_unsigned (ew Ed 38) = F) by (rewrite OLDd by lia; exact U38c).
assert (U513d : bv_unsigned (ew Ed 513) = SB + F / 8) by (rewrite OLDd, OLDc by lia; exact U513).
assert (U33d : bv_unsigned (ew Ed 33) = SB) by (rewrite OLDd, OLDc, E33b by lia; apply unsigned_lit_small; unfold SB; lia).
assert (LEN16 : (length es <= 16)%nat) by exact RL7.
pose proof (st_ok_pi_add_fact Ed _ _ 530 (mkAF 0 16 0) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E530, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2.
clear HS; rename HS2 into HS.
assert (PST3 : forall a, spZ regs - RIG_STK_x <= a < spZ regs -> apresent (w_H W) mem3 a).
{ destruct HJX3 as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
  intros a Ha. apply Hp. lia. }
assert (SVe : forall n v, (n < 514)%nat -> ew Eb n = Z_to_bv 64 v -> sv_denot Ed (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn Hv. cbn [sv_denot]. rewrite (OLDd n ltac:(lia)). exact (SVc n v Hn Hv). }
pose proof (st_ok_pi_add_region Ed _ _ (YP09.mkRegion (Some 2%nat) (-224) 0 (-200) (-128)
  [YP09.mkChunk (-208) (CVal 8 (SOff 38 0)); YP09.mkChunk (-152) (CVal 8 (SOff 10 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U2d; split; [lia|]; split; [lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); apply PST3; rewrite WS; lia
    | apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      [ apply (chunk_ok_val SEGS Ed _ (spZ regs) (-208) 8 (SOff 38 0) F);
        [ exact (SVe 38%nat F ltac:(lia) E38) | zside | zside | exact S16 ]
      | apply (chunk_ok_val SEGS Ed _ (spZ regs) (-152) 8 (SOff 10 0) (bv_unsigned (getr regs 10)));
        [ exact (SVe 10%nat _ ltac:(lia) (EBR 10%nat 10%bv eq_refl ltac:(lia))) | pose proof (UR 10%bv); zside | zside | exact S72 ] ] ])
  ltac:(cbn [all_disjoint]; exact I)) as HS2.
clear HS; rename HS2 into HS.
pose proof (pa_obj_img 4 ltac:(lia)) as Hob4.
assert (U245 : bv_unsigned (ew Ed 245) = rg_nsrc RG)
  by (rewrite (HEId 245%nat ltac:(unfold A_TEXT, A_LIM; lia)); exact (eq_sym RGNSRC)).
pose proof (st_ok_pi_add_region Ed _ _ (YP09.mkRegion (Some 245%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 530 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U245; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val SEGS Ed _ (rg_nsrc RG) 0 4 (SOff 530 0) (Z.of_nat (length es)));
    [ cbn [sv_denot]; rewrite E530, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity | zside | zside | rewrite Z.add_0_r; exact NS3 ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U245, U2d; split; [lia | exact I])) as HS2.
clear HS; rename HS2 into HS. norm_ss HS.
assert (SHOK : sh_ok SEGS rgp_Bx [] Ed (mrestrict (w_H W) mem3)) by constructor.
(* 0x82dcc .. 0x82dd4: a0 = g_nsrc's register image, 64(sp) = a0, a0 = g_nsrc; stop at the blez *)
paj_run_tok_x RUN HS HJX3 SHOK rgp_Bspan.
{ apply awr_ok_x_of0. awr_ok_tac. exact U2d. }
lazymatch goal with H : frame_of _ _ (mrestrict _ mem3) _ |- _ => rename H into FRa end.
lazymatch goal with H : mem_grows (mrestrict _ mem3) _ |- _ => rename H into GRa end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msa end.
assert (V530 : sv_denot Ed (SOff 530 0) = Z_to_bv 64 (Z.of_nat (length es)))
  by (cbn [sv_denot]; rewrite E530, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
psrr_branch_tok RUN BR HS SHOK rgp_Bspan.
- (* g_nsrc <= 0: the unlock tail RGU at 0x8312c *)
  assert (Hes0 : es = []).
  { cbn [branch_taken] in Hc.
    rewrite V530, bv_lts_signed in Hc. change (bv_signed (sv_denot Ed (SLit 0))) with 0 in Hc.
    rewrite bv_signed_small, unsigned_lit_small in Hc by (rewrite ?unsigned_lit_small by lia; lia).
    apply Bool.negb_true_iff, Z.ltb_ge in Hc. apply length_zero_iff_nil. lia. }
  paj_run_to_tok_x RUNTO HS HJX3 SHOK rgp_Bspan A_rig_unlock.
  { apply awr_ok_x_of0. awr_ok_tac. exact U2d. }
  lazymatch goal with H : frame_of _ _ (mrestrict _ (ms_mem msa)) _ |- _ => rename H into FRb end.
  lazymatch goal with H : mem_grows (mrestrict _ (ms_mem msa)) _ |- _ => rename H into GRb end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msb end.
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -200 <= a < spZ regs + -128) ->
    aview SEGS (w_H W) (ms_mem msb) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha Hw.
    rewrite (aview_kept_out Ed _ (w_H W) _ _ FRb a Ha ltac:(rgp_nowr2 U2d U245)).
    exact (aview_kept_out Ed _ (w_H W) _ _ FRa a Ha ltac:(rgp_nowr2 U2d U245)). }
  assert (PRESF : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem msb) a)
    by (intros a Hp; apply (apresent_grows _ _ _ a GRb); exact (apresent_grows _ _ _ a GRa Hp)).
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => pose proof (st_ok_pi_region_nth Ed ss _ 1 _ HS eq_refl) as RSF end.
  cbn [ms_mem restrict] in RSF.
  assert (L72 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -152) 8 (bv_unsigned (getr regs 10)))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-152) (SOff 10 0) _ RSF U2d ltac:(rgp_in)
      (SVe 10%nat _ ltac:(lia) (EBR 10%nat 10%bv eq_refl ltac:(lia))) (UR 10%bv)).
  clear RSF.
  destruct (CUT (ms_mem msb) _ _ HJX3 KEEPF L72 PRESF) as [GL GO].
  prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [3%bv; 4%bv] HS HAEd ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  assert (SPb : spZ (ms_regs msb) = spZ regs - 224) by (unfold spZ at 1; rewrite Q2, U2d, unsigned_lit_small by lia; lia).
  pmkst HS.
  apply KU. unfold RGU.
  lazymatch type of HJX3 with ajournal_gx_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx ?kx =>
    exists (ms_regs msb), ly, S2, (ms_mem msb), mdx, kx, F, FL, (@nil (rentry * hsrc)), c, O, cap, out, 0 end.
  split; [unfold cfg_at, A_rig_unlock; reflexivity|].
  split.
  { unfold gregs_base, gsp1, gsp0, cx. cbn [gxregs]. unfold RIG_FRAME.
    split; [exact SPb|]. split; [exact (HKR 3%bv ltac:(rgp_in))|]. split; [exact (HKR 4%bv ltac:(rgp_in))|].
    split; [rgp_regeq Q8 U2d|]. split; [rgp_regeq Q9 U2d|].
    rewrite <- SB_SHADOW_OFF. rgp_regeq Q21 U33d. }
  split; [unfold shadow_addr; rewrite <- SB_SHADOW_OFF; rgp_regeq Q20 U513d|].
  split; [exact GL|].
  replace (length (gxes cx)) with 0%nat by (unfold cx; cbn [gxes]; rewrite Hes0; reflexivity).
  exact GO.
- (* g_nsrc > 0: the loop's setup, to the outer head RGO 0 at 0x82e1c *)
  assert (Hpos : (0 < length es)%nat).
  { cbn [branch_taken] in Hc.
    rewrite V530, bv_lts_signed in Hc. change (bv_signed (sv_denot Ed (SLit 0))) with 0 in Hc.
    rewrite bv_signed_small, unsigned_lit_small in Hc by (rewrite ?unsigned_lit_small by lia; lia).
    apply Bool.negb_false_iff, Z.ltb_lt in Hc. lia. }
  paj_run_to_tok_x RUNTO HS HJX3 SHOK rgp_Bspan A_rig_outer.
  { apply awr_ok_x_of0. awr_ok_tac. exact U2d. }
  lazymatch goal with H : frame_of _ _ (mrestrict _ (ms_mem msa)) _ |- _ => rename H into FRb end.
  lazymatch goal with H : mem_grows (mrestrict _ (ms_mem msa)) _ |- _ => rename H into GRb end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msb end.
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -200 <= a < spZ regs + -128) ->
    aview SEGS (w_H W) (ms_mem msb) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha Hw.
    rewrite (aview_kept_out Ed _ (w_H W) _ _ FRb a Ha ltac:(rgp_nowr2 U2d U245)).
    exact (aview_kept_out Ed _ (w_H W) _ _ FRa a Ha ltac:(rgp_nowr2 U2d U245)). }
  assert (PRESF : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem msb) a)
    by (intros a Hp; apply (apresent_grows _ _ _ a GRb); exact (apresent_grows _ _ _ a GRa Hp)).
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => pose proof (st_ok_pi_region_nth Ed ss _ 1 _ HS eq_refl) as RSF end.
  cbn [ms_mem restrict] in RSF.
  assert (L72 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -152) 8 (bv_unsigned (getr regs 10)))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-152) (SOff 10 0) _ RSF U2d ltac:(rgp_in)
      (SVe 10%nat _ ltac:(lia) (EBR 10%nat 10%bv eq_refl ltac:(lia))) (UR 10%bv)).
  destruct (CUT (ms_mem msb) _ _ HJX3 KEEPF L72 PRESF) as [GL GO].
  assert (SVd : forall n, (A_TEXT <= n < A_LIM)%nat -> sv_denot Ed (SOff n 0) = Z_to_bv 64 (VAL n)).
  { intros n Hn. cbn [sv_denot]. rewrite (HEId n Hn), Z.add_0_r. reflexivity. }
  pose proof (pa_val_range (A_HI 42)). pose proof (pa_val_range (A_HI 41)). pose proof (pa_val_range 322%nat).
  pose proof (pa_val_range (A_OBJ 17)). pose proof (pa_val_range (A_OBJ 18)).
  assert (L24 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -200) 8 (VAL (A_HI 42)))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-200) (SOff (A_HI 42) 0) _ RSF U2d ltac:(rgp_in)
      (SVd (A_HI 42) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) ltac:(lia)).
  assert (L32 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -192) 8 0x7fffffff)
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-192) (SLit 0x7fffffff) _ RSF U2d ltac:(rgp_in) eq_refl ltac:(lia)).
  assert (L40 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -184) 8 (SB + F / 8))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-184) (SOff 513 0) _ RSF U2d ltac:(rgp_in)
      ltac:(cbn [sv_denot]; rewrite U513d, Z.add_0_r; reflexivity) ltac:(unfold SB; lia)).
  assert (L48 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -176) 8 (VAL (A_OBJ 18)))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-176) (SOff (A_OBJ 18) 0) _ RSF U2d ltac:(rgp_in)
      (SVd (A_OBJ 18) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) ltac:(lia)).
  assert (L56 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -168) 8 (VAL (A_OBJ 17)))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-168) (SOff (A_OBJ 17) 0) _ RSF U2d ltac:(rgp_in)
      (SVd (A_OBJ 17) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) ltac:(lia)).
  assert (L64 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -160) 8 (VAL (A_HI 41)))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-160) (SOff (A_HI 41) 0) _ RSF U2d ltac:(rgp_in)
      (SVd (A_HI 41) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) ltac:(lia)).
  assert (L88 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -136) 8 (F + 32))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-136) (SOff 38 32) _ RSF U2d ltac:(rgp_in)
      ltac:(cbn [sv_denot]; rewrite U38d; reflexivity) ltac:(lia)).
  clear RSF.
  prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [3%bv; 4%bv] HS HAEd ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  assert (SPb : spZ (ms_regs msb) = spZ regs - 224) by (unfold spZ at 1; rewrite Q2, U2d, unsigned_lit_small by lia; lia).
  pmkst HS.
  apply KO. unfold RGO.
  lazymatch type of HJX3 with ajournal_gx_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx ?kx =>
    exists (ms_regs msb), ly, S2, (ms_mem msb), mdx, kx, F, FL, (@nil (rentry * hsrc)), c, O, cap, out, 0 end.
  split; [unfold cfg_at, A_rig_outer; reflexivity|].
  split.
  { unfold gregs_base, gsp1, gsp0, cx. cbn [gxregs]. unfold RIG_FRAME.
    split; [exact SPb|]. split; [exact (HKR 3%bv ltac:(rgp_in))|]. split; [exact (HKR 4%bv ltac:(rgp_in))|].
    split; [rgp_regeq Q8 U2d|]. split; [rgp_regeq Q9 U2d|].
    rewrite <- SB_SHADOW_OFF. rgp_regeq Q21 U33d. }
  split; [unfold shadow_addr; rewrite <- SB_SHADOW_OFF; rgp_regeq Q20 U513d|].
  split; [rewrite Q22; reflexivity|].
  split; [rewrite <- HH42; change (A_HI 42) with 322%nat; rgp_regeq Q23 (HEId 322%nat ltac:(unfold A_TEXT, A_LIM; lia))|].
  split; [unfold cx; cbn [gxes]; exact Hpos|].
  split; [exact GL|].
  split; [|exact GO].
  unfold g_lslots, gsp1, gsp0, cx. cbn [gxregs]. unfold RIG_FRAME, arm.
  split; [replace (spZ regs - 224 + 24) with (spZ regs + -200) by lia; rewrite <- HH42; exact L24|].
  split; [replace (spZ regs - 224 + 32) with (spZ regs + -192) by lia; exact L32|].
  split; [replace (spZ regs - 224 + 40) with (spZ regs + -184) by lia; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; exact L40|].
  split; [replace (spZ regs - 224 + 48) with (spZ regs + -176) by lia; exact L48|].
  split; [replace (spZ regs - 224 + 56) with (spZ regs + -168) by lia; exact L56|].
  split; [replace (spZ regs - 224 + 64) with (spZ regs + -160) by lia; rewrite <- HH41; exact L64|].
  replace (spZ regs - 224 + 88) with (spZ regs + -136) by lia; exact L88.
Qed.

(* ---- route R (a Theorem Labs lane crew, G8b; a Theorem Labs lane): rig PRO at a world relation R, over a Theorem Labs lane's B
   W_relay_instance_gone_cx.v Section wR (rig_pro_stmt_xR, RGO_xR / RGU_xR).  PRO's input GBASE has no journal, so the
   strict walk is kept as the CORE (strict SRr to the disjunction of its two exits); each strict exit gives its R exit
   at every R containing wle (the journal by ajournal_gx_xR_mono), and the core is lifted (SRr_SRrG) and bound
   (SRrG_bind) to the R continuations.  The copied proof changes only at its two exits (a Theorem Labs lane's routeR/g8/mkrigpro.py). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Lemma GLIVE_xR_of_x : forall cx F FL ly1 S1 W1 m1 md1 k1,
  GLIVE B PST ARx RG cx F FL ly1 S1 W1 m1 md1 k1 -> GLIVE_xR B PST ARx RG R cx F FL ly1 S1 W1 m1 md1 k1.
Proof.
intros cx F FL ly1 S1 W1 m1 md1 k1 (fpos & Hp1 & HJ & REST). exists fpos, Hp1. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Ltac conv_glive H :=
  lazymatch type of H with
  | ?A /\ ?B => let Ha := fresh "Ha" in destruct H as [Ha H];
      split; [first [exact Ha | exact (GLIVE_xR_of_x _ _ _ _ _ _ _ _ _ Ha)] | conv_glive H]
  | _ => first [exact H | exact (GLIVE_xR_of_x _ _ _ _ _ _ _ _ _ H)]
  end.
Lemma RGO_xR_of_x : forall cx i W1 c1, RGO B PST ARx MT RP MMAX RG cx i W1 c1 -> RGO_xR B PST ARx MT RP MMAX RG R cx i W1 c1.
Proof.
intros cx i W1 c1 H. unfold RGO in H. unfold RGO_xR.
destruct H as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & c2 & O2 & cap2 & out2 & spent & H).
exists regs1, ly1, S1, m1, md1, k1, F, FL, qd, c2, O2, cap2, out2, spent. conv_glive H.
Qed.
Lemma RGU_xR_of_x : forall cx W1 c1, RGU B PST ARx MT RP MMAX RG cx W1 c1 -> RGU_xR B PST ARx MT RP MMAX RG R cx W1 c1.
Proof.
intros cx W1 c1 H. unfold RGU in H. unfold RGU_xR.
destruct H as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & c2 & O2 & cap2 & out2 & spent & H).
exists regs1, ly1, S1, m1, md1, k1, F, FL, qd, c2, O2, cap2, out2, spent. conv_glive H.
Qed.
Theorem rig_pro_xR : rig_pro_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold rig_pro_stmt_xR. intros cx HB KO KU.
enough (CORE : SRr SEGS (gxW cx) (cfg_at SEGS A_rig_entryP (gxregs cx) (gxmem cx) (gxmd cx))
  (fun W2 c2 => RGO B PST ARx MT RP MMAX RG cx 0 W2 c2 \/ RGU B PST ARx MT RP MMAX RG cx W2 c2)).
{ eapply (YA0nH.SRrG_bind SEGS R R_trans); [apply (YA0nH.SRr_SRrG SEGS R WLE_R); exact CORE|].
  intros W2 c2 _ [H2 | H2].
  - exact (KO W2 c2 (RGO_xR_of_x cx 0 W2 c2 H2)).
  - exact (KU W2 c2 (RGU_xR_of_x cx W2 c2 H2)). }
clear KO KU.
destruct cx as [regs ly S Hpe W mem md ch G0 ID es hs c O mx cap out rest kr].
unfold GBASE, gsp0, gps, gtr in HB.
cbn [gxregs gxly gxS gxHp gxW gxmem gxmd gxch gxG0 gxID gxes gxhs gxc gxO gxmx gxcap gxout gxrest gxkr] in HB |- *.
destruct HB as (HPRE & H32 & HCNT & RGP & H10 & RID & Hlock & HREL & HOUT & HROM & HLEN & HDRS & HNODUP & HPERM & HTRM & HLIVE & HMOK
  & HRMe & HCNTe).
set (cx := mkGcx regs ly S Hpe W mem md ch G0 ID es hs c O mx cap out rest kr) in *.
destruct RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
assert (RGIM : forall a, (rg_lock RG <= a < rg_lock RG + 12 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
  rg_src RG <= a < rg_src RG + 8) -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4)) by (intros a Ha; apply RGIMG; unfold rg_rng; tauto).
assert (RGAL : rg_lock RG mod 8 = 0 /\ rg_nsrc RG mod 4 = 0 /\ rg_src RG mod 8 = 0)
  by (split; [exact RGAL8 | split; [exact RGAL4 | exact RGSAL]]).
assert (GSEP : forall a, (rg_lock RG <= a < rg_lock RG + 12 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
  rg_src RG <= a < rg_src RG + 8) -> ~ (VAL (A_OBJ 0) <= a < VAL (A_OBJ 0) + 8) /\
  ~ (VAL (A_OBJ 6) <= a < VAL (A_OBJ 6) + 8) /\ ~ (VAL (A_OBJ 30) <= a < VAL (A_OBJ 30) + 8) /\
  ~ (as_uar_cell B <= a < as_uar_cell B + 4)) by (intros a Ha; apply RGSEP; unfold rg_rng; tauto).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (rgp_entry W ly S Hpe regs mem md ch HPRE H32) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx RIG_STK_x (rig_fp G0 es hs cap out) ly S Hpe W regs mem md ch HPRE) as HJ.
assert (HFPcl : ~ YI16.sink_open_fp (rig_fp G0 es hs cap out)).
{ unfold rig_fp.
  apply (rgp_fp_closed ly S Hpe W mem md _ rest (proj1 HPRE)). cbn [app]. rewrite <- !app_assoc. exact HPERM. }
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs rgp_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs rgp_extra) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17232) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (SPR : 2 ^ 46 <= spZ regs <= 2 ^ 47).
{ revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 H32. clear.
  unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
unfold cfg_at. change (w64 A_rig_entryP) with (Z_to_bv 64 A_rig_entryP). unfold A_rig_entryP, A_rig_entry.
paj_run_tok_x RUN0 HS HJ SHOK rgp_Bspan. { awr_ok_tac. exact Usp. }
(* the call to __asan_stack_malloc_1 (128): the fake frame (ASMP through W_frame_x.v aj_stack_malloc_pres_at_raw_x:
   ASMP's frame clause kept in the post, so errno's view crosses the call) *)
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite (palf_sm1 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply (aj_stack_malloc_pres_at_raw_x SEGS B PST ARx LAWS Hsegs (pal_env B TL) OWNLOW WFx WFL SMALLOC 1 ASMP ltac:(lia)
    W rg mm RIG_STK_x (spZ regs) (rig_fp G0 es hs cap out) ly S Hpe W mem md [] ly S Hpe _ 0 (-224) _ HJ) end.
  - unfold spZ at 1. rewrite R2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). lia.
  - reflexivity. - lia. - rewrite WS, Hes. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp. - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HCNT. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HKgrow & HFRM & HFS).
(* the room round: the seat's state is a set_fs of S, so RPF_of carries GBASE's room to it (the lock keeps it) *)
assert (HRM2 : rp_RM RP S2 (Z.to_nat (tr_cost MT_rk (rig_tr c mx (Z.of_nat (length O)) cap ID es hs)) + kr))
by (destruct HFS as (f & ->); exact (RPF_of RP _ _ _ HRMe)).
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
pose proof (proj1 HJ) as HARa. pose proof (proj1 HJ2) as HARb. clear HJ.
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARa) as (Kc1 & Ku1 & Kg1 & Kgu1).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARb) as (Kc2 & Ku2 & Kg2 & Kgu2).
rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2. rewrite (palf_got_uar B TLF) in Kgu1, Kgu2.
pose proof (palf_uar_img B TLF) as HuR.
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | apply Forall_nil].
  - eapply rgp_region_kept_stack_aj_x; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 30)));
    [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 30) (VAL (A_OBJ 30)) 8 SHADOW_OFF);
    [exact (HEI (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 6) (VAL (A_OBJ 6)) 8 (as_uar_cell B));
    [exact (HEI (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu2) | lia].
  - apply (region_kept_val_at E _ _ 32 (as_uar_cell B) 4 1);
    [rewrite E32; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku1) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku2) | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 34)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs rgp_extra) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
prreg HS (10%bv : bv 5) RF.
(* seat the fake frame: F at atom 38 (a0), its flag FL at 512, the frame's shadow SB + F / 8 at 513 *)
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 fpos HARb Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 1 fpos HARb Hfin2) as (HFal & HFapp & HFpres & HFSpres).
pose proof (rgp_frm_off_imgB_x _ _ _ _ _ _ 1 fpos HARb Hfin2) as HFimg.
destruct (FFL _ _ _ _ _ _ 1 fpos HARb Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
fold F FL in HFal, HFapp, HFpres, HFSpres, HFimg, HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc, HF4096, HFceil, HFhigh.
assert (RF' : ew Ea 38 = Z_to_bv 64 F) by (rewrite <- RF, Ha0; reflexivity).
assert (E33a : ew Ea 33 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E33).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 6 ltac:(lia)) as HguR.
pose proof (palf_sep B TLF) as HSEP. cbn [zseps zseps_from fst snd] in HSEP.
pose proof (pa_val_range (A_OBJ 0)). pose proof (pa_val_range (A_OBJ 6)). pose proof (pa_val_range (A_OBJ 30)).
pose proof (st_ok_pi_havoc_hi 512 Ea _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc Ea 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 512)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (E512 : ew Eb 512 = Z_to_bv 64 FL) by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E513 : ew Eb 513 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAEb : env_agree 32 (Ereg regs rgp_extra) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (E38 : ew Eb 38 = Z_to_bv 64 F) by (rewrite OLDb by lia; exact RF').
assert (E33b : ew Eb 33 = Z_to_bv 64 SB) by (rewrite OLDb by lia; exact E33a).
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
pose proof (st_ok_pi_add_fact Eb _ _ 38 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E38, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_fact Eb _ _ 512 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E512, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_fact Eb _ _ 513 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E513, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_alias Eb _ _ _ _ HS (shadow_decl_ok Eb 38 33 513 F SB E38 ltac:(lia) E33b E513)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
assert (U2b : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb, OLDa by lia; exact Usp).
assert (U241 : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)) by exact (HEIb (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U247 : bv_unsigned (ew Eb 247) = VAL (A_OBJ 6)) by exact (HEIb (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U271 : bv_unsigned (ew Eb 271) = VAL (A_OBJ 30)) by exact (HEIb (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U32 : bv_unsigned (ew Eb 32) = as_uar_cell B) by (rewrite OLDb, OLDa, E32 by lia; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew Eb 38) = F) by (rewrite E38; apply unsigned_lit_small; lia).
assert (U512 : bv_unsigned (ew Eb 512) = FL) by (rewrite E512; apply unsigned_lit_small; lia).
assert (U513 : bv_unsigned (ew Eb 513) = SB + F / 8) by (rewrite E513; apply unsigned_lit_small; unfold SB; lia).
pose proof (st_ok_pi_add_region Eb _ _ (fframe_region 38 512 1 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1) with 128; rewrite U38; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Eb _ F (128 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E512, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (128 - 8)) with (F + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1) with 128; rewrite U38, U2b, U241, U247, U271, U32;
unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Eb _ _ (fshadow_region 513 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1 / 8) with 16; rewrite U513; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres; apply (proj1 (HFSpres o ltac:(lia)))
| unfold zero_shadow, shadow_of_addr in Hz; rewrite <- SB_SHADOW_OFF in Hz;
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
[ apply (chunk_ok_val SEGS Eb _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside |];
  rewrite Z.add_0_r; apply val_mem_zero8; intros i Hi; apply Hz; change (128 / 8) with 16; lia
| apply (chunk_ok_val SEGS Eb _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside |];
  apply val_mem_zero8; intros i Hi; replace (SB + F / 8 + 8 + i) with (SB + F / 8 + (8 + i)) by lia; apply Hz; change (128 / 8) with 16; lia ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1 / 8) with 16; change (fs_frame_bytes 1) with 128; rewrite U513, U38, U2b, U241, U247, U271, U32;
unfold SB, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
(* the frame header and the shadow poison: a plain run, stopping at pthread_mutex_lock *)
paj_run_shc_x RUNP RUNC HS HJ2.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2b, ?U38, ?U513, ?U241, ?U247, ?U271, ?U32 in Hr;
    first [ lia
    | left; unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia
    | right; right; right; exists 1, fpos; split; [left; reflexivity|];
      change (frame_addr ly 1 fpos) with F; change (fs_frame_bytes 1) with 128;
      first [ left; unfold in_zr; cbn [fst snd]; lia
      | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (128 / 8) with 16; lia ] ]
  | ]).
  destruct Hin. }
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0.
(* the call to pthread_mutex_lock (&g_lock) *)
eassert (HJX : ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (spZ regs) (rig_fp G0 es hs cap out)
  ly S Hpe W mem md _ _ _ _ _ _ _ _).
{ eapply ajournal_gx_pack_x; [rewrite WS; lia | lia | rewrite !Z.add_0_r; exact HJ2 | apply gagree_refl | intros a Ha Hn; lia]. }
(* the program statics PST hold no byte of the cells the walk carries (PSTG), so the journal's image clause, which
   exempts PST, speaks of them *)
assert (PSG : forall a, inG (G_RIG B RG) a -> ~ Exists (in_zr a) PST) by (intros a Ha; apply PSTG; left; exact Ha).
assert (PSL : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ Exists (in_zr a) PST)
by (intros a Ha; apply PSG; rgp_ing 0%nat Ha).
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Hi Ho He Hps. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H11 & _).
  exact (H11 a Hi Ho He Hps (fp_spares_closed (rig_fp G0 es hs cap out) a HFPcl)). }
pose proof Hlock as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
pose proof (pa_obj_img 3 ltac:(lia)) as HlkR. rewrite <- RGLOCK in HlkR.
assert (LKI : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a Ha; exact (RGIM a (or_introl Ha))).
assert (LKK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a)
by (intros a Ha; destruct (LKI a Ha) as (Hi & Ho & He); exact (KIMG a Hi Ho He (PSL a Ha))).
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) mem a <> None).
{ intros a Ha. unfold aview.
  destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
  - pose proof (LK0 (Z.to_nat (a - rg_lock RG)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + (a - rg_lock RG)) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK4 (Z.to_nat (a - (rg_lock RG + 4))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 4 + (a - (rg_lock RG + 4))) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK8 (Z.to_nat (a - (rg_lock RG + 8))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 8 + (a - (rg_lock RG + 8))) with a in X by lia. rewrite X. discriminate. }
assert (LKtb : aview SEGS (w_H W) (ms_mem ms0) (rg_lock RG) = Some 0).
{ rewrite (LKK (rg_lock RG) ltac:(lia)). unfold aview. pose proof (LK0 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X.
  rewrite Z.add_0_r in X. rewrite X. vm_compute. reflexivity. }
assert (LK4m : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (rg_lock RG + 4) 4 0).
{ apply (val_mem_moved SEGS (w_H W) (w_H W) mem (ms_mem ms0) (rg_lock RG + 4) (rg_lock RG + 4) 4 0); [|exact LK4].
  intros kk Hk. apply LKK. cbn in Hk. lia. }
assert (HSPc : spZ (ms_regs ms0) = spZ regs + -224).
{ unfold spZ at 1. rewrite QSP, U2b. rewrite unsigned_lit_small by (unfold spZ in *; lia). lia. }
assert (QA0' : getr (ms_regs ms0) 10 = w64 (rg_lock RG)).
{ rewrite QA0. change 244%nat with (A_OBJ 3). rewrite (img_env_atomP Eb (A_OBJ 3) HEIb ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite RGLOCK. reflexivity. }
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS (G_RIG B RG) 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (_ : bvmap 5 word) (mem' : word -> option byte) => val_mem SEGS (mrestrict (w_H W) mem') (rg_lock RG + 4) 4 16)
    W _ _ RIG_STK_x (spZ regs) (rig_fp G0 es hs cap out) ly S Hpe W mem md _ _ _ _ _ _ (-224) _ HGRIG eq_refl HJX).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite QGP, OLDb, OLDa, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite QTP, OLDb, OLDa, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - exact QRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
    destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
  - intros a Ha _. rewrite (LKK a ltac:(lia)). exact (LKV a ltac:(lia)).
  - intros a Ha HnG. exfalso. apply HnG. unfold G_RIG. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
  - intros HPRE2 HSC. apply (ALOCK _ _ _ _ _ _ _ (rg_lock RG) 0 HPRE2).
    + exact QA0'.
    + lia.
    + destruct RGAL as (RGAL0 & _ & _). pose proof (Z.div_mod (rg_lock RG) 8 ltac:(lia)).
      pose proof (Z.div_mod (rg_lock RG) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (rg_lock RG) 4 ltac:(lia)). lia.
    + lia.
    + exact LKtb.
    + reflexivity.
    + exact LK4m.
    + intros a Ha. split; [rewrite (LKK a ltac:(lia)); exact (LKV a ltac:(lia))|]. rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha. destruct (LKI a ltac:(lia)) as (Hi & Ho & He). split; [|split].
      * apply (RGWR (w_H W) (ms_mem ms0) a); [left; lia | exact (hidden_not_img SEGS W (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; exact Hi))].
      * intros Hown. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a (proj1 HJ2) Hi) Hown).
      * rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha HKw1. apply (proj2 (proj2 (HGRIG a ltac:(unfold G_RIG, inG; apply Exists_cons_hd; unfold in_zr;
        cbn [fst snd]; lia)))). exact (proj1 (proj2 HKw1)). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJX3 & HP3 & HLK3 & Hfr3 & Hpres3).
(* reseat: the lock wrote only g_lock + 4 .. + 8, which no region of the state covers *)
jafter_call_keep_hi HS 514%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  pose proof HFapp as HFA. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFA.
  pose proof HFimg as HFI.
  pose proof (palf_uar_img B TLF) as HUI.
  assert (LKlo : forall a, rg_lock RG <= a < rg_lock RG + 12 -> 0 <= a < 2 ^ 64) by (intros a Ha; lia).
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
    ~ (spZ regs + -224 - ESTACK <= a < spZ regs + -224) ->
    aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) (ms_mem ms0) a)
  by (intros a Hq1 Hq2 Hq3; apply Hfr3; [exact Hq1 | exact Hq2 | exact Hq3]).
  repeat apply Forall_cons; [| | | | | | | apply Forall_nil].
  - (* fshadow 513 *) apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 513 (SB + F / 8) 0 16);
    [exact U513 | intros a Ha; apply KEEP3; unfold SB in *; rewrite ?Hes; lia | exact Hpres3].
  - (* fframe 38 *) apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 38 F 0 128);
    [exact U38 | intros a Ha; apply KEEP3; rewrite ?Hes; lia | exact Hpres3].
  - (* stack *) apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 2 (spZ regs) (-224) 0);
    [exact U2b | intros a Ha; apply KEEP3; rewrite ?Hes; lia | exact Hpres3].
  - (* got A_OBJ 0 *) apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 241 (VAL (A_OBJ 0)) 0 8);
    [exact U241 | intros a Ha; apply KEEP3;
     [lia | intros Hw; assert (HL : rg_lock RG <= a < rg_lock RG + 12) by lia;
            destruct (GSEP a (or_introl HL)) as (N0 & _ & _ & _); apply N0; lia | rewrite ?Hes; lia] | exact Hpres3].
  - (* bcell A_OBJ 32 *) apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 271 (VAL (A_OBJ 30)) 0 8);
    [exact U271 | intros a Ha; apply KEEP3;
     [lia | intros Hw; assert (HL : rg_lock RG <= a < rg_lock RG + 12) by lia;
            destruct (GSEP a (or_introl HL)) as (_ & _ & N32 & _); apply N32; lia | rewrite ?Hes; lia] | exact Hpres3].
  - (* uar got A_OBJ 1 *) apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 247 (VAL (A_OBJ 6)) 0 8);
    [exact U247 | intros a Ha; apply KEEP3;
     [lia | intros Hw; assert (HL : rg_lock RG <= a < rg_lock RG + 12) by lia;
            destruct (GSEP a (or_introl HL)) as (_ & N1 & _ & _); apply N1; lia | rewrite ?Hes; lia] | exact Hpres3].
  - (* uar cell *) apply (region_kept_aview Eb (w_H W) (ms_mem ms0) mem3 32 (as_uar_cell B) 0 4);
    [exact U32 | intros a Ha; apply KEEP3;
     [lia | intros Hw; assert (HL : rg_lock RG <= a < rg_lock RG + 12) by lia;
            destruct (GSEP a (or_introl HL)) as (_ & _ & _ & Nu); apply Nu; lia | rewrite ?Hes; lia] | exact Hpres3]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
(* ---- At 0x82dcc, after the lock.  The environment, and what the state shows of the frame. ---- *)
remember (havoc Eb 514 (map (getr regs3) CLOB)) as Ec eqn:HEc in HS.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc_hi; [exact HEIb | cbv; lia]).
assert (OLDc : forall m, (m < 514)%nat -> ew Ec m = ew Eb m) by (intros m Hm; rewrite HEc; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEc : env_agree 32 (Ereg regs rgp_extra) Ec) by (rewrite HEc; apply env_agree_havoc_ge; [cbv; lia | exact HAEb]).
clear HEc.
assert (U2c : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLDc by lia; exact U2b).
assert (U38c : bv_unsigned (ew Ec 38) = F) by (rewrite OLDc by lia; exact U38).
assert (SVc : forall n v, (n < 514)%nat -> ew Eb n = Z_to_bv 64 v -> sv_denot Ec (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn Hv. cbn [sv_denot]. rewrite (OLDc n Hn), Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (UR : forall (r : bv 5), 0 <= bv_unsigned (getr regs r) < 2 ^ 64).
{ intros r. pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
assert (EBR : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 34)%nat -> ew Eb n = Z_to_bv 64 (bv_unsigned (getr regs r))).
{ intros n r Hn Hn34. rewrite OLDb, OLDa, (EE n r Hn) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  pose proof (st_ok_pi_region_nth Ec ss _ 1 _ HS eq_refl) as RFR;
  pose proof (st_ok_pi_region_nth Ec ss _ 2 _ HS eq_refl) as RST end.
cbn [ms_mem restrict mkst] in RFR, RST.
assert (FLm3 : val_mem SEGS (mrestrict (w_H W) mem3) (F + 120) 8 FL).
{ exact (field_of_region Ec _ 38 F _ 0 128 0 128 120 8%N (SOff 512 0) FL RFR U38c ltac:(rgp_in)
    (SVc 512%nat FL ltac:(lia) E512) ltac:(zside) ltac:(zside)). }
assert (S8 : val_mem SEGS (mrestrict (w_H W) mem3) (spZ regs + -216) 8 F)
by exact (slot_of_region Ec _ _ _ _ _ _ _ (-216) (SOff 38 0) F RST U2c ltac:(rgp_in) (SVc 38%nat F ltac:(lia) E38) ltac:(lia)).
assert (S16 : val_mem SEGS (mrestrict (w_H W) mem3) (spZ regs + -208) 8 F)
by exact (slot_of_region Ec _ _ _ _ _ _ _ (-208) (SOff 38 0) F RST U2c ltac:(rgp_in) (SVc 38%nat F ltac:(lia) E38) ltac:(lia)).
assert (S112 : val_mem SEGS (mrestrict (w_H W) mem3) (spZ regs + -112) 8 F)
by exact (slot_of_region Ec _ _ _ _ _ _ _ (-112) (SOff 38 0) F RST U2c ltac:(rgp_in) (SVc 38%nat F ltac:(lia) E38) ltac:(lia)).
assert (S72 : val_mem SEGS (mrestrict (w_H W) mem3) (spZ regs + -152) 8 (bv_unsigned (getr regs 10)))
by exact (slot_of_region Ec _ _ _ _ _ _ _ (-152) (SOff 10 0) _ RST U2c ltac:(rgp_in)
  (SVc 10%nat _ ltac:(lia) (EBR 10%nat 10%bv eq_refl ltac:(lia))) (UR 10%bv)).
assert (SAV : forall i, (i < 13)%nat -> val_mem SEGS (mrestrict (w_H W) mem3) (spZ regs + (-104 + 8 * Z.of_nat i)) 8
  (bv_unsigned (getr regs (nth i RIG_SAVED 0%bv)))).
{ intros i Hi.
  do 13 (destruct i as [|i]; [
    lazymatch goal with |- val_mem _ _ (spZ regs + (-104 + 8 * Z.of_nat ?k)) 8 (bv_unsigned (getr regs (nth ?k' RIG_SAVED 0%bv))) =>
      let od := eval vm_compute in (-104 + 8 * Z.of_nat k) in
      let r := eval vm_compute in (nth k RIG_SAVED 0%bv) in
      let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
      change (spZ regs + (-104 + 8 * Z.of_nat k)) with (spZ regs + od);
      change (nth k' RIG_SAVED 0%bv) with r;
      exact (slot_of_region Ec _ _ _ _ _ _ _ od (SOff n 0) _ RST U2c ltac:(rgp_in)
        (SVc n _ ltac:(lia) (EBR n r eq_refl ltac:(lia))) (UR r)) end|]).
  lia. }
clear RFR RST.
(* the image bytes the walk keeps (the journal, then the lock's frame), the blocks and errno (each step's frame) *)
assert (KG3 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Hi Ho He Hps Hl. pose proof (Hsegs a Hi) as Hlo.
  rewrite (Hfr3 a ltac:(unfold kLowMemEnd in Hlo; lia) Hl ltac:(unfold ESTACK, kLowMemEnd in *; lia)).
  exact (KIMG a Hi Ho He Hps). }
assert (NOWR1 : forall a, a < spZ regs - 224 -> ~ in_wrange E (ss_mem ss_rgp0) a).
{ intros a Ha (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
     rewrite ?Usp in Hr; lia | ]).
  destruct Hin. }
assert (Hb2 : forall p n, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly S2)) by (intros p n Hb; rewrite Eab; exact Hb).
assert (KH3 : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros p n a Hb Ha.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hb) as (_ & Hp4096 & Hpc & Hpapp & _).
  assert (HnI : ~ in_img SEGS a)
    by (exact (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hb Ha))))))).
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly S2 _ W mem2 md2 p n 1 fpos HARb (Hb2 p n Hb) Hfin2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr ly 1 fpos) with F in Hd. change (fs_frame_bytes 1) with 128 in Hd.
  rewrite (Hfr3 a ltac:(lia) ltac:(intros Hl; apply HnI; exact (proj1 (LKI a ltac:(lia))))
    ltac:(unfold ESTACK; lia)).
  rewrite (aview_kept_out Eb _ (w_H W) mem2 (ms_mem ms0) HFr0 a ltac:(lia)).
  2: { intros (r & Hin & Hr).
       lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
       cbn [In] in Hin.
       repeat (destruct Hin as [<- | Hin];
         [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U513, ?U38, ?U2b, ?U241, ?U247, ?U271, ?U32 in Hr;
          first [ lia | exfalso; refine (fshadow_not_app F 16 p (req_size n) a HF4096 _ Hpapp _ Ha); unfold SB in *; lia ] | ]).
       destruct Hin. }
  replace a with (p + (a - p)) by lia.
  rewrite (proj1 (proj2 HK) p n (a - p) Hb ltac:(lia) ltac:(intros [])).
  replace (p + (a - p)) with a by lia.
  exact (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a ltac:(lia) (NOWR1 a ltac:(lia))). }
assert (FRNI : forall x, F <= x < F + 128 -> ~ in_img SEGS x).
{ intros x Hx. exact (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ x HARb (or_intror (or_introl (ex_intro _ 1 (ex_intro _ fpos (conj Hfin2 Hx))))))). }
assert (KE3 : forall a, as_errno B <= a < as_errno B + 4 -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Ha. pose proof (pal_env B TL) as ((He0 & He1) & Heimg & _).
  assert (Hi : in_img SEGS a) by (apply Heimg; exact Ha).
  assert (HGe : inG (G_RIG B RG) a) by (rgp_ing 7%nat Ha).
  destruct (HGRIG a HGe) as (_ & Hno & _).
  rewrite (Hfr3 a ltac:(lia) ltac:(rgp_off 0%nat 14%nat Ha) ltac:(unfold ESTACK, kLowMemEnd in *; lia)).
  rewrite (aview_kept_out Eb _ (w_H W) mem2 (ms_mem ms0) HFr0 a ltac:(lia)).
  2: { intros (r & Hin & Hr).
       lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
       cbn [In] in Hin.
       repeat (destruct Hin as [<- | Hin];
         [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U513, ?U38, ?U2b, ?U241, ?U247, ?U271, ?U32 in Hr;
          first [ unfold SB, kLowMemEnd in *; lia
          | exact (FRNI a ltac:(lia) Hi) ] | ]).
       destruct Hin. }
  rewrite (HFRM a ltac:(lia) (fun Ho => Hno (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR Hi) Ho))
    (fun Ho => Hno (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARb Hi) Ho)) ltac:(unfold ESTACK, kLowMemEnd in *; lia)).
  exact (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a ltac:(lia) (NOWR1 a ltac:(unfold kLowMemEnd in *; lia))). }
assert (PRI3 : forall a, in_img SEGS a -> apresent (w_H W) mem a -> apresent (w_H W) mem3 a).
{ intros a Hi Hp. apply Hpres3. apply (apresent_grows _ _ _ a HG0). apply (HKgrow a Hi). exact (apresent_grows _ _ _ a HG Hp). }
pose proof HREL as (RL1 & RL2 & RL3 & RL4 & RL5 & RL6 & RL7 & RL8 & RL9 & RL10 & RL11).
assert (NS3 : val_mem SEGS (mrestrict (w_H W) mem3) (rg_nsrc RG) 4 (Z.of_nat (length es))).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3 (rg_nsrc RG) 4 _); [|exact RL3].
  intros kk Hk. cbn in Hk. assert (Hk' : rg_nsrc RG <= rg_nsrc RG + kk < rg_nsrc RG + 4) by lia.
  destruct (RGIMG (rg_nsrc RG + kk) ltac:(unfold rg_rng; lia)) as (Hi & Ho & He).
  exact (KG3 _ Hi Ho He (PSTG _ (or_intror (or_intror (or_introl Hk')))) ltac:(rgp_off 0%nat 3%nat Hk')). }
assert (LK3 : alock_at RG W mem3 true).
{ unfold alock_at, arm. split; [|split; [exact HLK3|split]].
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3 (rg_lock RG) 4 0); [|exact LK0].
    intros kk Hk. cbn in Hk. destruct (LKI (rg_lock RG + kk) ltac:(lia)) as (Hi & Ho & He).
    apply KG3; [exact Hi | exact Ho | exact He | apply PSL; lia | lia].
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3 (rg_lock RG + 8) 4 0); [|exact LK8].
    intros kk Hk. cbn in Hk. destruct (LKI (rg_lock RG + 8 + kk) ltac:(lia)) as (Hi & Ho & He).
    apply KG3; [exact Hi | exact Ho | exact He | apply PSL; lia | lia].
  - intros i Hi. unfold arm. destruct (LKI (rg_lock RG + i) ltac:(lia)) as (Hii & _ & _).
    apply (RGWR (w_H W) mem3 (rg_lock RG + i)); [left; lia | exact (hidden_not_img SEGS W (Z_to_bv 64 (rg_lock RG + i)) ltac:(rewrite unsigned_lit_small by (pose proof (Hsegs _ Hii); unfold kLowMemEnd in *; lia); exact Hii))]. }
(* ---- The cut predicates' common part, at any memory the walk reaches from mem3 by storing to 24(sp) .. 96(sp)
   (the id's slot 72(sp) lies inside that window, so its value at memF is a premise). ---- *)
assert (CUT : forall memF mdF kF,
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (spZ regs) (rig_fp G0 es hs cap out)
    ly S Hpe W mem md [(1, fpos)] ly S2 Hpe W memF mdF kF ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -200 <= a < spZ regs + -128) -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem3 a) ->
  val_mem SEGS (mrestrict (w_H W) memF) (spZ regs + -152) 8 (bv_unsigned (getr regs 10)) ->
  (forall a, apresent (w_H W) mem3 a -> apresent (w_H W) memF a) ->
  GLIVE B PST ARx RG cx F FL ly S2 W memF mdF kF /\ GOUT B MT RP MMAX RG cx 0 [] c O cap out 0 ly S2 W memF).
{ intros memF mdF kF HJF KEEPF S72F PRESF.
  assert (HARF : ARx ly S2 Hpe W memF mdF) by (destruct HJF as (_ & _ & (memS & HJi & _) & _); exact (proj1 HJi)).
  assert (KF : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem3 a)
    by (intros a Ha; apply KEEPF; [pose proof asan_consts as (CC1 & _); lia | rewrite WS in Hslo; lia]).
  assert (KBI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
    ~ Exists (in_zr a) PST -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> abyte_kept W mem W memF a).
  { intros a Hi Ho He Hps Hl. pose proof (Hsegs a Hi) as Hlo. split.
    - rewrite (KF a ltac:(unfold kLowMemEnd in Hlo; lia)). exact (KG3 a Hi Ho He Hps Hl).
    - unfold arm. apply writable_kept. intros Hp. apply PRESF. exact (PRI3 a Hi Hp). }
  assert (KBE : forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W mem W memF a).
  { intros a Ha. pose proof (pal_env B TL) as ((He0 & He1) & Heimg & _). split.
    - rewrite (KF a ltac:(unfold kLowMemEnd in *; lia)). exact (KE3 a Ha).
    - unfold arm. apply writable_kept. intros Hp. apply PRESF. exact (PRI3 a (Heimg a Ha) Hp). }
  assert (KBH : forall a, rgp_blk ly S a -> abyte_kept W mem W memF a).
  { intros a (p & n & Hb & Ha).
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hb) as (_ & Hp4096 & Hpc & _ & _).
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HARF (Hb2 p n Hb)) as (_ & _ & _ & _ & HpF & _).
    split.
    - rewrite (KF a ltac:(lia)). exact (KH3 p n a Hb Ha).
    - intros _. unfold arm. apply (apresent_writable SEGS). exact (proj1 (HpF a Ha)). }
  assert (KBS : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W mem W memF a).
  { intros a Ha. destruct (RGIMG a ltac:(unfold rg_rng; lia)) as (Hi & Ho & He).
    exact (KBI a Hi Ho He (PSG a ltac:(rgp_ing 1%nat Ha)) ltac:(rgp_off 0%nat 1%nat Ha)). }
  assert (KBG : forall a, inG (G_RIG B RG) a -> ~ (as_errno B <= a < as_errno B + 4) -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
    abyte_kept W mem W memF a).
  { intros a Hg He Hl. destruct (HGRIG a Hg) as (Hi & Ho & _). exact (KBI a Hi Ho He (PSG a Hg) Hl). }
  assert (KBR : forall a, (rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
    rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
    ~ (as_errno B <= a < as_errno B + 4) -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> abyte_kept W mem W memF a).
  { intros a Hr He Hl. destruct (HRGI a Hr) as (Hi & Ho). exact (KBI a Hi Ho He (PSTG a (or_intror (or_intror (or_intror Hr)))) Hl). }
  assert (HPB : forall b, In b ((G0, ATABLE) :: concat (map aentry_blks es) ++ rig_srcs (combine es hs) ++ aout_blks cap out) ->
    In b (ablocks B ly S2)).
  { intros b Hb. rewrite Eab. apply (Permutation_in _ (Permutation_sym HPERM)).
    destruct Hb as [<- | Hb]; [left; reflexivity | right].
    apply in_app_or in Hb. destruct Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|].
    apply in_or_app; right. apply in_app_or in Hb. destruct Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|].
    apply in_or_app; right. apply in_or_app; left. exact Hb. }
  split.
  - (* GLIVE *)
    unfold GLIVE. exists fpos, Hpe. split; [exact HJF|]. split.
    { eapply (ajournal_gx_rom_view_x SEGS B PST ARx).
      all: first [exact LAWS | exact Hsegs | exact HJF | exact HROMO | exact PSTR | exact HROM]. }
    split; [intros a Hi Ho He Hp; apply PRESF; exact (PRI3 a Hi Hp)|].
    split.
    { unfold g_frame, g_saved, gsp1, gsp0, cx. cbn [gxregs]. unfold RIG_FRAME.
      split; [reflexivity|]. split; [reflexivity|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF (F + 120) 8 FL); [intros kk Hk; cbn in Hk; apply KF; lia | exact FLm3]|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF _ 8 F); [intros kk Hk; cbn in Hk; apply KEEPF; lia | replace (spZ regs - 224 + 8) with (spZ regs + -216) by lia; exact S8]|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF _ 8 F); [intros kk Hk; cbn in Hk; apply KEEPF; lia | replace (spZ regs - 224 + 16) with (spZ regs + -208) by lia; exact S16]|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF _ 8 F); [intros kk Hk; cbn in Hk; apply KEEPF; lia | replace (spZ regs - 224 + 112) with (spZ regs + -112) by lia; exact S112]|].
      split; [replace (spZ regs - 224 + 72) with (spZ regs + -152) by lia; exact S72F|].
      intros i Hi. apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF _ 8 _); [intros kk Hk; cbn in Hk; apply KEEPF; lia|].
      replace (spZ regs - 224 + 120 + 8 * Z.of_nat i) with (spZ regs + (-104 + 8 * Z.of_nat i)) by lia. exact (SAV i Hi). }
    { destruct LK3 as (L0 & L4 & L8 & LW). unfold alock_at, arm in *.
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF _ 4 0); [intros kk Hk; cbn in Hk; destruct (LKI (rg_lock RG + kk) ltac:(lia)) as (Hi & _); pose proof (Hsegs _ Hi); apply KF; unfold kLowMemEnd in *; lia | exact L0]|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF _ 4 _); [intros kk Hk; cbn in Hk; destruct (LKI (rg_lock RG + 4 + kk) ltac:(lia)) as (Hi & _); pose proof (Hsegs _ Hi); apply KF; unfold kLowMemEnd in *; lia | exact L4]|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memF _ 4 0); [intros kk Hk; cbn in Hk; destruct (LKI (rg_lock RG + 8 + kk) ltac:(lia)) as (Hi & _); pose proof (Hsegs _ Hi); apply KF; unfold kLowMemEnd in *; lia | exact L8]|].
      intros i Hi. unfold arm. destruct (LKI (rg_lock RG + i) ltac:(lia)) as (Hii & _ & _).
      apply (RGWR (w_H W) memF (rg_lock RG + i)); [left; lia | exact (hidden_not_img SEGS W (Z_to_bv 64 (rg_lock RG + i)) ltac:(rewrite unsigned_lit_small by (pose proof (Hsegs _ Hii); unfold kLowMemEnd in *; lia); exact Hii))]. }
  - (* GOUT 0 *)
    unfold GOUT, gbud, gps, gtr, cx.
    cbn [gxes gxhs gxc gxO gxmx gxcap gxout gxrest gxW gxmem gxS gxHp gxly gxG0 gxID gxkr firstn skipn map app].
    split; [lia|]. split; [reflexivity|]. split; [cbn [rig_rel]; repeat split|].
    split.
    { apply (arelay_at_kept B RG ly S W mem ly S2 W memF G0 es HREL).
      - intros r Hr a Ha. unfold arelay_fp in Hr. cbn [In] in Hr.
        destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
        + destruct (RGIMG a ltac:(unfold rg_rng; lia)) as (Hi & Ho & He).
          exact (KBI a Hi Ho He (PSTG a (or_intror (or_introl Ha))) ltac:(rgp_off 0%nat 2%nat Ha)).
        + destruct (RGIMG a ltac:(unfold rg_rng; lia)) as (Hi & Ho & He).
          exact (KBI a Hi Ho He (PSTG a (or_intror (or_intror (or_introl Ha)))) ltac:(rgp_off 0%nat 3%nat Ha)).
        + exact (KBR a (or_introl Ha) ltac:(rgp_off 4%nat 14%nat Ha) ltac:(rgp_off 0%nat 4%nat Ha)).
        + apply KBH. apply (rgp_blk_of ly S G0 ATABLE a RL8); unfold ATABLE in *; lia.
        + apply in_concat in Hr as (fp & Hfp & Hr). apply in_map_iff in Hfp as (e & <- & He).
          rewrite Forall_forall in RL10. exact (KBH a (rgp_aentry_fp ly S W mem e (RL10 e He) r Hr a Ha)).
      - intros b Hb. apply HPB. destruct Hb as [<- | Hb]; [left; reflexivity | right; apply in_or_app; left; exact Hb]. }
    split.
    { apply (aout_at_kept B RG ly S W mem ly S2 W memF c O mx (Z.of_nat (length O)) cap out HOUT).
      - intros r Hr a Ha. unfold aout_fp in Hr. cbn [In] in Hr.
        destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
        + exact (KBR a (or_intror (or_introl Ha)) ltac:(rgp_off 5%nat 14%nat Ha) ltac:(rgp_off 0%nat 5%nat Ha)).
        + exact (KBG a ltac:(rgp_ing 4%nat Ha) ltac:(rgp_off 6%nat 14%nat Ha) ltac:(rgp_off 0%nat 6%nat Ha)).
        + exact (KBG a ltac:(rgp_ing 5%nat Ha) ltac:(rgp_off 7%nat 14%nat Ha) ltac:(rgp_off 0%nat 7%nat Ha)).
        + exact (KBG a ltac:(rgp_ing 6%nat Ha) ltac:(rgp_off 8%nat 14%nat Ha) ltac:(rgp_off 0%nat 8%nat Ha)).
        + exact (KBR a (or_intror (or_intror (or_introl Ha))) ltac:(rgp_off 9%nat 14%nat Ha) ltac:(rgp_off 0%nat 9%nat Ha)).
        + exact (KBG a ltac:(rgp_ing 2%nat Ha) ltac:(rgp_off 10%nat 14%nat Ha) ltac:(rgp_off 0%nat 10%nat Ha)).
        + exact (KBR a (or_intror (or_intror (or_intror Ha))) ltac:(rgp_off 11%nat 14%nat Ha) ltac:(rgp_off 0%nat 11%nat Ha)).
        + exact (KBG a ltac:(rgp_ing 3%nat Ha) ltac:(rgp_off 12%nat 14%nat Ha) ltac:(rgp_off 0%nat 12%nat Ha)).
        + exact (KBE a Ha).
        + destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []].
          cbn [fst snd] in Ha. pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HO26).
          destruct HO26 as [(Hc & _) | (Hc & _ & Hin & _)]; [lia|].
          apply KBH. apply (rgp_blk_of ly S out cap a Hin); lia.
      - intros b Hb. apply HPB. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
    split; [intros i' Hi'; lia|].
    split.
    { rewrite Forall_forall in HDRS |- *. intros p Hp He.
      destruct (HDRS p Hp He) as (Hj & Hsa & Hot & Hrest).
      split; [exact Hj|]. split.
      - apply (asrc_at_kept B ly S W mem ly S2 W memF _ _ Hsa).
        + intros r Hr a Ha. destruct (rgp_asrc_fp ly S W mem _ _ Hsa r Hr a Ha) as [Hx | Hx].
          * apply KBS. unfold ASRC in *. lia.
          * exact (KBH a Hx).
        + intros b Hb. apply HPB. right. apply in_or_app. right. apply in_or_app. left.
          unfold rig_srcs. apply in_concat. exists (asrc_blks (fst (snd p))). split; [|exact Hb].
          apply in_map_iff. exists p. split; [cbv beta; rewrite (proj2 (Z.eqb_eq _ _) He); reflexivity | exact Hp].
      - split; [|exact Hrest].
        intros i Hi Hne. destruct (Hot i Hi Hne) as (f & o & Vf & Vo & Hfo). exists f, o.
        split; [apply (akept_vm W mem W memF); [intros x Hx; apply KBS; cbn in Hx; unfold ASRC in *; lia | exact Vf]|].
        split; [apply (akept_vm W mem W memF); [intros x Hx; apply KBS; cbn in Hx; unfold ASRC in *; lia | exact Vo] | exact Hfo]. }
    split; [intros a Ha _; exact (KBS a Ha)|].
    split.
    { rewrite Eab. unfold gdone_srcs. cbn [combine map concat app]. exact HPERM. }
    split; [destruct HFS as (f & Ef); rewrite Ef; exact (MO_FR S f)|]. split; [lia|].
    lazymatch goal with |- context [grest ?cxx 0 ?no ?cp] => change (grest cxx 0 no cp) with (rig_tr c mx no cp ID es hs) end.
    rewrite Hbb2. split; [lia|]. split; [exact HLIVE|]. split; [exact HTRM|].
    (* the room round: the seat kept GBASE's room (HRM2) and the blocks (Eab), and entry 0 owes gtr's requests *)
    split; [exact HRM2 | rewrite Eab; exact HCNTe]. }
(* ---- The state for 0x82dcc .. 0x82e1c: the frame (16(sp) = F, 72(sp) = the id; writable at 24(sp) .. 96(sp)) and
   g_nsrc. ---- *)
clear SHOK.
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  pose proof (st_ok_pi_submem Ec ss _ [] HS ltac:(submem_tac) eq_refl) as HS2 end.
clear HS. rename HS2 into HS. norm_ss HS.
pose proof (st_ok_pi_havoc_hi 530 Ec _ _ [Z_to_bv 64 (Z.of_nat (length es))] HS ltac:(vm_compute; reflexivity)) as HS2.
clear HS. rename HS2 into HS.
remember (havoc Ec 530 [Z_to_bv 64 (Z.of_nat (length es))]) as Ed eqn:HEd in HS.
assert (HEId : img_env VAL A_LIM Ed) by (rewrite HEd; apply img_env_havoc_hi; [exact HEIc | cbv; lia]).
assert (OLDd : forall m, (m < 530)%nat -> ew Ed m = ew Ec m) by (intros m Hm; rewrite HEd; apply YN3v.ew_havoc_old; exact Hm).
assert (E530 : ew Ed 530 = Z_to_bv 64 (Z.of_nat (length es)))
  by (rewrite HEd; exact (ew_havoc_new _ 530 [Z_to_bv 64 (Z.of_nat (length es))] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAEd : env_agree 32 (Ereg regs rgp_extra) Ed) by (rewrite HEd; apply env_agree_havoc_ge; [cbv; lia | exact HAEc]).
clear HEd.
assert (U2d : bv_unsigned (ew Ed 2) = spZ regs) by (rewrite OLDd by lia; exact U2c).
assert (U38d : bv_unsigned (ew Ed 38) = F) by (rewrite OLDd by lia; exact U38c).
assert (U513d : bv_unsigned (ew Ed 513) = SB + F / 8) by (rewrite OLDd, OLDc by lia; exact U513).
assert (U33d : bv_unsigned (ew Ed 33) = SB) by (rewrite OLDd, OLDc, E33b by lia; apply unsigned_lit_small; unfold SB; lia).
assert (LEN16 : (length es <= 16)%nat) by exact RL7.
pose proof (st_ok_pi_add_fact Ed _ _ 530 (mkAF 0 16 0) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E530, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2.
clear HS; rename HS2 into HS.
assert (PST3 : forall a, spZ regs - RIG_STK_x <= a < spZ regs -> apresent (w_H W) mem3 a).
{ destruct HJX3 as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
  intros a Ha. apply Hp. lia. }
assert (SVe : forall n v, (n < 514)%nat -> ew Eb n = Z_to_bv 64 v -> sv_denot Ed (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn Hv. cbn [sv_denot]. rewrite (OLDd n ltac:(lia)). exact (SVc n v Hn Hv). }
pose proof (st_ok_pi_add_region Ed _ _ (YP09.mkRegion (Some 2%nat) (-224) 0 (-200) (-128)
  [YP09.mkChunk (-208) (CVal 8 (SOff 38 0)); YP09.mkChunk (-152) (CVal 8 (SOff 10 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U2d; split; [lia|]; split; [lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); apply PST3; rewrite WS; lia
    | apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      [ apply (chunk_ok_val SEGS Ed _ (spZ regs) (-208) 8 (SOff 38 0) F);
        [ exact (SVe 38%nat F ltac:(lia) E38) | zside | zside | exact S16 ]
      | apply (chunk_ok_val SEGS Ed _ (spZ regs) (-152) 8 (SOff 10 0) (bv_unsigned (getr regs 10)));
        [ exact (SVe 10%nat _ ltac:(lia) (EBR 10%nat 10%bv eq_refl ltac:(lia))) | pose proof (UR 10%bv); zside | zside | exact S72 ] ] ])
  ltac:(cbn [all_disjoint]; exact I)) as HS2.
clear HS; rename HS2 into HS.
pose proof (pa_obj_img 4 ltac:(lia)) as Hob4.
assert (U245 : bv_unsigned (ew Ed 245) = rg_nsrc RG)
  by (rewrite (HEId 245%nat ltac:(unfold A_TEXT, A_LIM; lia)); exact (eq_sym RGNSRC)).
pose proof (st_ok_pi_add_region Ed _ _ (YP09.mkRegion (Some 245%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 530 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite U245; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val SEGS Ed _ (rg_nsrc RG) 0 4 (SOff 530 0) (Z.of_nat (length es)));
    [ cbn [sv_denot]; rewrite E530, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity | zside | zside | rewrite Z.add_0_r; exact NS3 ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U245, U2d; split; [lia | exact I])) as HS2.
clear HS; rename HS2 into HS. norm_ss HS.
assert (SHOK : sh_ok SEGS rgp_Bx [] Ed (mrestrict (w_H W) mem3)) by constructor.
(* 0x82dcc .. 0x82dd4: a0 = g_nsrc's register image, 64(sp) = a0, a0 = g_nsrc; stop at the blez *)
paj_run_tok_x RUN HS HJX3 SHOK rgp_Bspan.
{ apply awr_ok_x_of0. awr_ok_tac. exact U2d. }
lazymatch goal with H : frame_of _ _ (mrestrict _ mem3) _ |- _ => rename H into FRa end.
lazymatch goal with H : mem_grows (mrestrict _ mem3) _ |- _ => rename H into GRa end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msa end.
assert (V530 : sv_denot Ed (SOff 530 0) = Z_to_bv 64 (Z.of_nat (length es)))
  by (cbn [sv_denot]; rewrite E530, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
psrr_branch_tok RUN BR HS SHOK rgp_Bspan.
- (* g_nsrc <= 0: the unlock tail RGU at 0x8312c *)
  assert (Hes0 : es = []).
  { cbn [branch_taken] in Hc.
    rewrite V530, bv_lts_signed in Hc. change (bv_signed (sv_denot Ed (SLit 0))) with 0 in Hc.
    rewrite bv_signed_small, unsigned_lit_small in Hc by (rewrite ?unsigned_lit_small by lia; lia).
    apply Bool.negb_true_iff, Z.ltb_ge in Hc. apply length_zero_iff_nil. lia. }
  paj_run_to_tok_x RUNTO HS HJX3 SHOK rgp_Bspan A_rig_unlock.
  { apply awr_ok_x_of0. awr_ok_tac. exact U2d. }
  lazymatch goal with H : frame_of _ _ (mrestrict _ (ms_mem msa)) _ |- _ => rename H into FRb end.
  lazymatch goal with H : mem_grows (mrestrict _ (ms_mem msa)) _ |- _ => rename H into GRb end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msb end.
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -200 <= a < spZ regs + -128) ->
    aview SEGS (w_H W) (ms_mem msb) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha Hw.
    rewrite (aview_kept_out Ed _ (w_H W) _ _ FRb a Ha ltac:(rgp_nowr2 U2d U245)).
    exact (aview_kept_out Ed _ (w_H W) _ _ FRa a Ha ltac:(rgp_nowr2 U2d U245)). }
  assert (PRESF : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem msb) a)
    by (intros a Hp; apply (apresent_grows _ _ _ a GRb); exact (apresent_grows _ _ _ a GRa Hp)).
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => pose proof (st_ok_pi_region_nth Ed ss _ 1 _ HS eq_refl) as RSF end.
  cbn [ms_mem restrict] in RSF.
  assert (L72 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -152) 8 (bv_unsigned (getr regs 10)))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-152) (SOff 10 0) _ RSF U2d ltac:(rgp_in)
      (SVe 10%nat _ ltac:(lia) (EBR 10%nat 10%bv eq_refl ltac:(lia))) (UR 10%bv)).
  clear RSF.
  destruct (CUT (ms_mem msb) _ _ HJX3 KEEPF L72 PRESF) as [GL GO].
  prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [3%bv; 4%bv] HS HAEd ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  assert (SPb : spZ (ms_regs msb) = spZ regs - 224) by (unfold spZ at 1; rewrite Q2, U2d, unsigned_lit_small by lia; lia).
  pmkst HS.
  apply SRr_ret; right. unfold RGU.
  lazymatch type of HJX3 with ajournal_gx_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx ?kx =>
    exists (ms_regs msb), ly, S2, (ms_mem msb), mdx, kx, F, FL, (@nil (rentry * hsrc)), c, O, cap, out, 0 end.
  split; [unfold cfg_at, A_rig_unlock; reflexivity|].
  split.
  { unfold gregs_base, gsp1, gsp0, cx. cbn [gxregs]. unfold RIG_FRAME.
    split; [exact SPb|]. split; [exact (HKR 3%bv ltac:(rgp_in))|]. split; [exact (HKR 4%bv ltac:(rgp_in))|].
    split; [rgp_regeq Q8 U2d|]. split; [rgp_regeq Q9 U2d|].
    rewrite <- SB_SHADOW_OFF. rgp_regeq Q21 U33d. }
  split; [unfold shadow_addr; rewrite <- SB_SHADOW_OFF; rgp_regeq Q20 U513d|].
  split; [exact GL|].
  replace (length (gxes cx)) with 0%nat by (unfold cx; cbn [gxes]; rewrite Hes0; reflexivity).
  exact GO.
- (* g_nsrc > 0: the loop's setup, to the outer head RGO 0 at 0x82e1c *)
  assert (Hpos : (0 < length es)%nat).
  { cbn [branch_taken] in Hc.
    rewrite V530, bv_lts_signed in Hc. change (bv_signed (sv_denot Ed (SLit 0))) with 0 in Hc.
    rewrite bv_signed_small, unsigned_lit_small in Hc by (rewrite ?unsigned_lit_small by lia; lia).
    apply Bool.negb_false_iff, Z.ltb_lt in Hc. lia. }
  paj_run_to_tok_x RUNTO HS HJX3 SHOK rgp_Bspan A_rig_outer.
  { apply awr_ok_x_of0. awr_ok_tac. exact U2d. }
  lazymatch goal with H : frame_of _ _ (mrestrict _ (ms_mem msa)) _ |- _ => rename H into FRb end.
  lazymatch goal with H : mem_grows (mrestrict _ (ms_mem msa)) _ |- _ => rename H into GRb end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msb end.
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -200 <= a < spZ regs + -128) ->
    aview SEGS (w_H W) (ms_mem msb) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha Hw.
    rewrite (aview_kept_out Ed _ (w_H W) _ _ FRb a Ha ltac:(rgp_nowr2 U2d U245)).
    exact (aview_kept_out Ed _ (w_H W) _ _ FRa a Ha ltac:(rgp_nowr2 U2d U245)). }
  assert (PRESF : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem msb) a)
    by (intros a Hp; apply (apresent_grows _ _ _ a GRb); exact (apresent_grows _ _ _ a GRa Hp)).
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => pose proof (st_ok_pi_region_nth Ed ss _ 1 _ HS eq_refl) as RSF end.
  cbn [ms_mem restrict] in RSF.
  assert (L72 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -152) 8 (bv_unsigned (getr regs 10)))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-152) (SOff 10 0) _ RSF U2d ltac:(rgp_in)
      (SVe 10%nat _ ltac:(lia) (EBR 10%nat 10%bv eq_refl ltac:(lia))) (UR 10%bv)).
  destruct (CUT (ms_mem msb) _ _ HJX3 KEEPF L72 PRESF) as [GL GO].
  assert (SVd : forall n, (A_TEXT <= n < A_LIM)%nat -> sv_denot Ed (SOff n 0) = Z_to_bv 64 (VAL n)).
  { intros n Hn. cbn [sv_denot]. rewrite (HEId n Hn), Z.add_0_r. reflexivity. }
  pose proof (pa_val_range (A_HI 42)). pose proof (pa_val_range (A_HI 41)). pose proof (pa_val_range 322%nat).
  pose proof (pa_val_range (A_OBJ 17)). pose proof (pa_val_range (A_OBJ 18)).
  assert (L24 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -200) 8 (VAL (A_HI 42)))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-200) (SOff (A_HI 42) 0) _ RSF U2d ltac:(rgp_in)
      (SVd (A_HI 42) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) ltac:(lia)).
  assert (L32 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -192) 8 0x7fffffff)
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-192) (SLit 0x7fffffff) _ RSF U2d ltac:(rgp_in) eq_refl ltac:(lia)).
  assert (L40 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -184) 8 (SB + F / 8))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-184) (SOff 513 0) _ RSF U2d ltac:(rgp_in)
      ltac:(cbn [sv_denot]; rewrite U513d, Z.add_0_r; reflexivity) ltac:(unfold SB; lia)).
  assert (L48 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -176) 8 (VAL (A_OBJ 18)))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-176) (SOff (A_OBJ 18) 0) _ RSF U2d ltac:(rgp_in)
      (SVd (A_OBJ 18) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) ltac:(lia)).
  assert (L56 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -168) 8 (VAL (A_OBJ 17)))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-168) (SOff (A_OBJ 17) 0) _ RSF U2d ltac:(rgp_in)
      (SVd (A_OBJ 17) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) ltac:(lia)).
  assert (L64 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -160) 8 (VAL (A_HI 41)))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-160) (SOff (A_HI 41) 0) _ RSF U2d ltac:(rgp_in)
      (SVd (A_HI 41) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) ltac:(lia)).
  assert (L88 : val_mem SEGS (mrestrict (w_H W) (ms_mem msb)) (spZ regs + -136) 8 (F + 32))
    by exact (slot_of_region Ed _ _ _ _ _ _ _ (-136) (SOff 38 32) _ RSF U2d ltac:(rgp_in)
      ltac:(cbn [sv_denot]; rewrite U38d; reflexivity) ltac:(lia)).
  clear RSF.
  prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [3%bv; 4%bv] HS HAEd ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  assert (SPb : spZ (ms_regs msb) = spZ regs - 224) by (unfold spZ at 1; rewrite Q2, U2d, unsigned_lit_small by lia; lia).
  pmkst HS.
  apply SRr_ret; left. unfold RGO.
  lazymatch type of HJX3 with ajournal_gx_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx ?kx =>
    exists (ms_regs msb), ly, S2, (ms_mem msb), mdx, kx, F, FL, (@nil (rentry * hsrc)), c, O, cap, out, 0 end.
  split; [unfold cfg_at, A_rig_outer; reflexivity|].
  split.
  { unfold gregs_base, gsp1, gsp0, cx. cbn [gxregs]. unfold RIG_FRAME.
    split; [exact SPb|]. split; [exact (HKR 3%bv ltac:(rgp_in))|]. split; [exact (HKR 4%bv ltac:(rgp_in))|].
    split; [rgp_regeq Q8 U2d|]. split; [rgp_regeq Q9 U2d|].
    rewrite <- SB_SHADOW_OFF. rgp_regeq Q21 U33d. }
  split; [unfold shadow_addr; rewrite <- SB_SHADOW_OFF; rgp_regeq Q20 U513d|].
  split; [rewrite Q22; reflexivity|].
  split; [rewrite <- HH42; change (A_HI 42) with 322%nat; rgp_regeq Q23 (HEId 322%nat ltac:(unfold A_TEXT, A_LIM; lia))|].
  split; [unfold cx; cbn [gxes]; exact Hpos|].
  split; [exact GL|].
  split; [|exact GO].
  unfold g_lslots, gsp1, gsp0, cx. cbn [gxregs]. unfold RIG_FRAME, arm.
  split; [replace (spZ regs - 224 + 24) with (spZ regs + -200) by lia; rewrite <- HH42; exact L24|].
  split; [replace (spZ regs - 224 + 32) with (spZ regs + -192) by lia; exact L32|].
  split; [replace (spZ regs - 224 + 40) with (spZ regs + -184) by lia; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; exact L40|].
  split; [replace (spZ regs - 224 + 48) with (spZ regs + -176) by lia; exact L48|].
  split; [replace (spZ regs - 224 + 56) with (spZ regs + -168) by lia; exact L56|].
  split; [replace (spZ regs - 224 + 64) with (spZ regs + -160) by lia; rewrite <- HH41; exact L64|].
  replace (spZ regs - 224 + 88) with (spZ regs + -136) by lia; exact L88.
Qed.
End wR.
End c.

End b.
End a.
