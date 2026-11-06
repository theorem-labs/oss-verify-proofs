(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment TOP of the IMAGE-B walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan-ubsan), track "calls": its two runtime calls, snprintf (F + 32, 48, "%s %d ", "param_gesture", id)
   at 0x82eb8 (lib/B/W_rig_top_defs.v stmt_snp_call) and strlen (F + 32) at 0x82ec0 (stmt_strlen_call), over the
   walk's journal (own = [(1, fpos)], the fake frame F).  Ported from k3's image-A track (a working branch
   80fffa8e840, lib/A/W_rig_top_calls.v).  The Section header is W_rig_top_defs.v's, verbatim.

   Image B against image A: A's stmt_snp_call took what snprintf's contract asks of the two literals as a premise
   (stmt_snp_env); here those facts are derived (ts_lit) from the Section's HLIT17 / HLIT18 (glit_at_x: the bytes in
   seg_rom, in_rom, and ashp_x: range_addressable over exactly [a, a + n) and the shadow hull in every ARx state), the
   call state's rom_view and ARx (from the journal, ts_jframe) and the stack position.  No zero-shadow fact over a
   literal is used.  ASNPRINTF's atail_vis for each literal (the bytes after its NUL to the end of its 8-byte
   granule are visible): snp_call_tail takes it as the image fact ts_lit_tail (those bytes lie in the image: seg_rom
   has them), which glit_at_x's fourth conjunct gives (ts_lit_tail_of), and ts_tail_vis turns it into atail_vis in
   every state.
   ROUTE (b), STEP 3 (the image-A twin: a Theorem Labs lane's RIG_x round of lib/A/W_rig_top.v, commit f4cd818e98d): over ARx
   at W_relay_instance_gone_cx.v's generic Section (journals ajournal_gx_x at RIG_STK_x, the sites' _x liftings
   aj_gx_entry_at_x / aj_strlen_gx_at_x).  The fake frame is only 32-aligned in a generic state (alx_frames): ts_ra
   and ts_hull (the buffer's shadow hull, in place of the AR kit's shadow_hull_vis_of_frame) read that alignment.
   THE SNPRINTF NARROWING (the window's 4d3f3ddb1df on the AR text, re-applied here over ARx): ASNPRINTF is the
   narrowed asnprintf_realizes_x (W_sites_x.v: the format premise F and M1, M3, M2); snp_call_tail discharges F by
   eq_refl, M1 by SnpNarrowSites.san_M1_pi, M3 by san_M3_pi on the register equation E13, both from the Section
   hypothesis HLITGOT (the window's text, verbatim), and M2 by SnpNarrowSites.san_M2_x_pi: san_M2_AR_pi's fact over
   ARx (the frame above ly_img by the laws' alx_img, ly_img's top at least 0x5fc000 by IMGC; a Theorem Labs lane's ruling
   14:16Z put it in SnpNarrowSites.v).
   Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_instance_gone_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_instance_gone_b_lem printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rig_top_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require SnpNarrowSites.
(* route R: a Theorem Labs lane's dr_spec_xR / ge_spec_xR, SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
(* the two literals of the snprintf call and " end\0" (.str.4, A_lit_end5 = A_OBJ 28), in the cx's glit_at_x form
   over ARx (W_relay_instance_gone_cx.v: bytes, in_rom, ashp_x, the granule's tail) *)
Hypothesis HLIT17 : glit_at_x ARx 17 (RIG_FMT ++ [0]).
Hypothesis HLIT18 : glit_at_x ARx 18 (RelayModel.K_GESTURE ++ [0]).
(* the two literals lie in .rodata below the GOT word FR_GOT_GUARD = 0x9ebd8, |"%s %d "| + 1 = 7 and
   |"param_gesture"| + 1 + 8 = 22 bytes: the location premises M1 / M3 of the narrowed asnprintf_realizes_x (W_sites_x.v),
   which this abstract placement does not fix.  PB_fr decides it by vm_compute: SnpNarrowSites.v HLITGOT_PB_fr.  (Not in
   W_rig_top_defs.v's header: only snp_call_tail and its consumers W_rig_top.v / W_relay_instance_gone.v take it.) *)
Hypothesis HLITGOT : VAL (A_OBJ 17) + 7 <= FR_GOT_GUARD /\ VAL (A_OBJ 18) + 22 <= FR_GOT_GUARD.
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

(* ------------------------------------------------------------------ the text "param_gesture <id> " *)
Lemma ts_digits : forall f x acc, 0 <= x -> Forall (fun z => 0 <= z < 256) acc ->
  Forall (fun z => 0 <= z < 256) (printf_facts_c.pf_digits f x acc) /\
  (length (printf_facts_c.pf_digits f x acc) <= length acc + f)%nat.
Proof.
induction f as [|f IH]; intros x acc Hx Ha; cbn [printf_facts_c.pf_digits]; [split; [exact Ha | lia]|].
destruct (x <? 10) eqn:E.
- apply Z.ltb_lt in E. split; [constructor; [lia | exact Ha] | cbn [length]; lia].
- apply Z.ltb_ge in E. assert (H10 : 0 <= x mod 10 < 10) by (apply Z.mod_pos_bound; lia).
  destruct (IH (x / 10) ((48 + x mod 10) :: acc)) as [H1 H2]; [apply Z.div_pos; lia | constructor; [lia | exact Ha] |].
  split; [exact H1 | cbn [length] in H2; lia].
Qed.

(* snprintf's text T: bytes, and at most 27 of them (so the 48-byte buffer holds it with its NUL) *)
Lemma ts_T : forall id,
  Forall (fun z => 0 <= z < 256) (relay_instance_gone_b_c.instance_prefix id) /\
  (length (relay_instance_gone_b_c.instance_prefix id) <= 27)%nat.
Proof.
intros id.
assert (HD : Forall (fun z => 0 <= z < 256) (printf_facts_c.pf_dec id) /\ (length (printf_facts_c.pf_dec id) <= 12)%nat).
{ unfold printf_facts_c.pf_dec. destruct (id <? 0) eqn:E.
  - apply Z.ltb_lt in E. destruct (ts_digits 11 (- id) [] ltac:(lia) (Forall_nil _)) as [H1 H2].
    split; [constructor; [lia | exact H1] | cbn [length] in H2 |- *; lia].
  - apply Z.ltb_ge in E. destruct (ts_digits 11 id [] E (Forall_nil _)) as [H1 H2].
    split; [exact H1 | cbn [length] in H2; lia]. }
destruct HD as [HD1 HD2]. unfold relay_instance_gone_b_c.instance_prefix.
rewrite !length_app. unfold RelayModel.K_GESTURE. cbn [length].
split; [|lia].
apply Forall_app; split; [repeat constructor; lia|].
apply Forall_app; split; [repeat constructor; lia|].
apply Forall_app; split; [exact HD1 | repeat constructor; lia].
Qed.

(* snprintf's post (abytes_at of pf_bytes) as the walk's garr8 *)
Lemma ts_garr8_of_abytes : forall (W : world SEGS) mem a l, Forall (fun z => 0 <= z < 256) l ->
  abytes_at W mem a (printf_facts_c.pf_bytes l) -> garr8 SEGS (arm W mem) a l.
Proof.
intros W mem a l Hr Hb j Hj.
assert (Hz : 0 <= nth j l 0 < 256) by (apply (proj1 (Forall_forall _ _) Hr); apply nth_In; exact Hj).
specialize (Hb j ltac:(unfold printf_facts_c.pf_bytes; rewrite length_map; exact Hj)).
unfold printf_facts_c.pf_bytes in Hb. rewrite map_nth in Hb.
rewrite Z_to_bv_unsigned in Hb. unfold bv_wrap in Hb. change (bv_modulus 8) with 256 in Hb. rewrite Z.mod_small in Hb by lia.
split; [|exact Hz].
destruct (aview_byte SEGS (w_H W) mem _ _ Hb) as (b & Hm & Hv & _).
intros k Hk. assert (k = 0)%nat by lia. subst k. rewrite Z.add_0_r. unfold arm. rewrite Hm. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, YO0f.le_byte. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (nth j l 0) 256) by lia. exact (eq_sym Hv).
Qed.

(* ------------------------------------------------------------------ the fake frame F and its shadow *)
(* the 6 zero shadow bytes F's shadow + 4 .. + 9 make any prefix of the buffer F + 32 .. F + 80 addressable (F is
   32-aligned: alx_frames) *)
Lemma ts_ra : forall (W : world SEGS) mem F n, F mod 32 = 0 -> 0 <= n <= 48 ->
  (forall o, 4 <= o < 10 -> aview SEGS (w_H W) mem (shadow_addr F + o) = Some 0) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (F + 32) n.
Proof.
intros W mem F n Hal Hn Hsh x Hx. exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as MF.
pose proof (Z.div_mod F 32 ltac:(lia)) as DF32. rewrite Hal in DF32.
replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr F + (x / 8 - F / 8)) by (unfold shadow_of_addr, shadow_addr; lia).
apply Hsh. lia.
Qed.

(* the shadow hull of a prefix of the buffer F + 32 .. F + 80 lies in F's 16 shadow bytes, which are present
   (alx_frames: F is 32-aligned, so its shadow address is 4-aligned and the hull's 8-byte granules stay inside them) *)
Lemma ts_hull : forall ly S Hp (W : world SEGS) mem md fpos F n,
  ARx ly S Hp W mem md -> In (1, fpos) (frames S) -> frame_addr ly 1 fpos = F -> 0 < n <= 48 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) (F + 32) n.
Proof.
intros ly S Hp W mem md fpos F n HAR Hin HF Hn s Hs.
destruct (alx_frames _ _ _ LAWS ly S Hp W mem md 1 fpos HAR Hin) as (Hal & _ & _ & Hsh).
change (fs_frame_bytes 1 / 8) with 16 in Hsh. rewrite HF in Hal, Hsh.
unfold shadow_addr, SHADOW_OFF in Hs, Hsh.
pose proof (Z.div_mod F 32 ltac:(lia)) as D32. rewrite Hal in D32.
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
pose proof (Z.div_mod (F + 32) 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound (F + 32) 8 ltac:(lia)) as N1.
pose proof (Z.div_mod (F + 32 + n - 1) 8 ltac:(lia)) as E2.
pose proof (Z.mod_pos_bound (F + 32 + n - 1) 8 ltac:(lia)) as N2.
pose proof (Z.div_mod (2147450880 + (F + 32) / 8) 8 ltac:(lia)) as E3.
pose proof (Z.mod_pos_bound (2147450880 + (F + 32) / 8) 8 ltac:(lia)) as N3.
pose proof (Z.div_mod (2147450880 + (F + 32 + n - 1) / 8) 8 ltac:(lia)) as E4.
pose proof (Z.mod_pos_bound (2147450880 + (F + 32 + n - 1) / 8) 8 ltac:(lia)) as N4.
specialize (Hsh (s - (2147450880 + F / 8)) ltac:(lia)).
replace (2147450880 + F / 8 + (s - (2147450880 + F / 8))) with s in Hsh by lia.
apply (aview_some_of_apresent SEGS). exact (proj1 Hsh).
Qed.

(* the walk's journal: the call state's allocator state, the fake frame among its frames, the stack above the
   allocator's ceiling (astk_ok) *)
Lemma ts_jframe : forall W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k,
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W
    memT mdc k ->
  ARx lyc Sc Hpc W memT mdc /\ In (1, fpos) (frames Sc) /\ alloc_ceiling + RIG_STK_x <= sp0.
Proof.
intros W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k HJ.
destruct HJ as (_ & _ & (memS & HJi & _) & _).
destruct HJi as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & _).
split; [exact HAR|]. split; [rewrite Hfrs; apply in_or_app; left; apply in_eq | lia].
Qed.

(* the class-1 fake frame F (128 bytes): below the ceiling, 32-aligned, in application memory, present, not the
   runtime's *)
Lemma ts_frame : forall ly S Hp W mem md fpos F,
  ARx ly S Hp W mem md -> In (1, fpos) (frames S) -> frame_addr ly 1 fpos = F ->
  4096 <= F /\ F + 128 <= alloc_ceiling /\ F mod 32 = 0 /\
  (F + 128 <= 2147446784 \/ 17594333495296 <= F) /\
  (forall a, F <= a < F + 128 -> apresent (w_H W) mem a /\ ~ aowned B ly S a).
Proof.
intros ly S Hp W mem md fpos F HAR Hin HF.
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 1 fpos HAR Hin) as (H1 & H2 & H3).
destruct (alx_frames _ _ _ LAWS ly S Hp W mem md 1 fpos HAR Hin) as (H4 & _ & H5 & _).
change (fs_frame_bytes 1) with 128 in H2, H3, H5. rewrite HF in H1, H2, H3, H4, H5.
unfold in_app, kLowShadowBeg, kHighMemBeg in H3.
split; [lia|]. split; [lia|]. split; [exact H4|]. split; [lia | exact H5].
Qed.

(* an image object (between 0x10000 and 0x5fc000, inside ly_img: IMGC) is not a byte of the fake frame
   (alx_client_img) *)
Lemma ts_lit_apart : forall ly S Hp W mem md fpos F x,
  ARx ly S Hp W mem md -> In (1, fpos) (frames S) -> frame_addr ly 1 fpos = F ->
  65536 <= x < 6275072 -> ~ (F <= x < F + 128).
Proof.
intros ly S Hp W mem md fpos F x HAR Hin HF Hx Hr.
destruct (alx_client_img _ _ _ LAWS ly S Hp W mem md x HAR) as [Hn _].
{ right. left. exists 1, fpos. split; [exact Hin|]. rewrite HF. change (fs_frame_bytes 1) with 128. exact Hr. }
apply Hn. destruct (IMGC ly S Hp W mem md HAR) as [H1 H2]. unfold in_zr. lia.
Qed.

(* ------------------------------------------------------------------ the two literals snprintf reads *)
(* The image fact ASNPRINTF's atail_vis asks of a literal, from glit_at_x's fourth conjunct (the first three place [a, a + n) only):
   the bytes after the literal's last byte (its NUL, at VAL (A_OBJ i) + n) to the end of that byte's 8-byte granule
   are image bytes (seg_rom has them). *)
Definition ts_lit_tail (i : nat) (n : Z) : Prop :=
forall x, VAL (A_OBJ i) + n < x < VAL (A_OBJ i) + n - (VAL (A_OBJ i) + n) mod 8 + 8 ->
  seg_rom SEGS (Z_to_bv 64 x) <> None.

(* a byte the image has is visible in every memory (aview falls back to seg_rom) *)
Lemma ts_tail_vis : forall (W : world SEGS) mem e,
  (forall x, e < x < e - e mod 8 + 8 -> seg_rom SEGS (Z_to_bv 64 x) <> None) -> atail_vis W mem e.
Proof.
intros W mem e H x Hx Hv. apply (H x Hx). unfold aview in Hv. cbv beta in Hv. unfold mbyte in Hv.
destruct (mrestrict (w_H W) mem (Z_to_bv 64 x)); [discriminate Hv|].
destruct (seg_rom SEGS (Z_to_bv 64 x)); [discriminate Hv | reflexivity].
Qed.

(* What snprintf's contract asks of a literal (its format, or a %s argument) besides the tail, from glit_at_x: the
   bytes through rom_view (astr_at), the extent in the image (in_rom, pa_img_range: below kLowMemEnd and below the
   scratch window, which lies above alloc_ceiling), the shadow from ashp_x at the state's ARx (no zero shadow). *)
Lemma ts_lit : forall i s (W : world SEGS) (regs : bvmap 5 word) mem ly S Hp md,
  (i < 31)%nat -> glit_at_x ARx i (s ++ [0]) -> Forall (fun c => 0 < c < 256) s ->
  ARx ly S Hp W mem md -> rom_view SEGS W mem -> alloc_ceiling <= spZ regs - 3 * ESTACK ->
  astr_at W mem (VAL (A_OBJ i)) (printf_facts_c.pf_bytes s) /\
  aread_ok (3 * ESTACK) W regs mem (VAL (A_OBJ i)) (Z.of_nat (length s) + 1).
Proof.
intros i s W regs mem ly S Hp md Hi (Hb & Hr & Hs & _) Hc HAR Hrom Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_obj_img i Hi) as O.
assert (EL : Z.of_nat (length (s ++ [0])) = Z.of_nat (length s) + 1) by (rewrite length_app; cbn [length]; lia).
rewrite EL in Hr, Hs.
(* the bytes, read through rom_view *)
assert (HV : forall k, (k < length s + 1)%nat ->
  aview SEGS (w_H W) mem (VAL (A_OBJ i) + Z.of_nat k) = Some (bv_unsigned (Z_to_bv 8 (nth k (s ++ [0]) 0)))).
{ intros k Hk.
  rewrite (Hrom (VAL (A_OBJ i) + Z.of_nat k) (Hr (VAL (A_OBJ i) + Z.of_nat k) ltac:(lia))).
  rewrite (Hb k ltac:(rewrite length_app; cbn [length]; lia)).
  assert (E : nth_error (s ++ [0]) k = Some (nth k (s ++ [0]) 0))
    by (apply nth_error_nth'; rewrite length_app; cbn [length]; lia).
  rewrite E. reflexivity. }
(* the literal lies in the image *)
assert (HT : VAL (A_OBJ i) + Z.of_nat (length s) < 0x5fc000).
{ destruct (Hr (VAL (A_OBJ i) + Z.of_nat (length s)) ltac:(lia)) as (sg & H1 & _ & H2).
  apply (pa_img_range (VAL (A_OBJ i) + Z.of_nat (length s))). exists sg. split; [exact H1 | exact H2]. }
destruct (Hs ly S Hp W mem md HAR) as [Hra Hhull].
split.
- split.
  + unfold abytes_at, printf_facts_c.pf_bytes.
    replace (map (Z_to_bv 8) s ++ [Z_to_bv 8 0]) with (map (Z_to_bv 8) (s ++ [0])) by (rewrite map_app; reflexivity).
    intros j Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj.
    rewrite map_nth. apply HV. lia.
  + unfold printf_facts_c.pf_bytes. intros Hin. apply in_map_iff in Hin as (c & Ec & Hcin).
    pose proof (proj1 (Forall_forall _ _) Hc c Hcin) as Hc'. cbv beta in Hc'.
    apply (f_equal bv_unsigned) in Ec. rewrite !Z_to_bv_unsigned in Ec. unfold bv_wrap in Ec.
    change (bv_modulus 8) with 256 in Ec. rewrite (Z.mod_small c 256) in Ec by lia.
    rewrite Z.mod_0_l in Ec by lia. lia.
- unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
  { intros a Ha. split.
    - replace a with (VAL (A_OBJ i) + Z.of_nat (Z.to_nat (a - VAL (A_OBJ i)))) by lia.
      rewrite HV by lia. discriminate.
    - unfold ascratch_stk. lia. }
  split; [unfold amem_range; left; lia|]. split; [exact Hra|].
  intros _. apply Hhull. lia.
Qed.


(* ------------------------------------------------------------------ S1. snprintf at 0x82eb8 *)
(* ASNPRINTF at d = F + 32, n = 48, the format "%s %d " (A_OBJ 17), the arguments "param_gesture" (A_OBJ 18) and
   id, lifted over the walk's journal by aj_gx_entry_at_x (its written bytes F + 32 .. F + 80 are bytes of the walk's
   own fake frame: awr_byte's in_frames clause).  The literals' facts come from HLIT17 / HLIT18 (ts_lit) and their
   granule tails from ts_lit_tail (ts_tail_vis); the guard is the statement's premise. *)
Lemma ts_lit_tail_of : forall i s, glit_at_x ARx i (s ++ [0]) -> ts_lit_tail i (Z.of_nat (length s)).
Proof.
intros i s (_ & _ & _ & Ht). unfold ts_lit_tail. intros x Hx. apply Ht.
replace (Z.of_nat (length (s ++ [0]))) with (Z.of_nat (length s) + 1)
  by (rewrite length_app; cbn [length]; lia).
replace (VAL (A_OBJ i) + (Z.of_nat (length s) + 1) - 1) with (VAL (A_OBJ i) + Z.of_nat (length s)) by lia.
lia.
Qed.

Lemma snp_call_tail : ts_lit_tail 17 6 -> ts_lit_tail 18 13 -> stmt_snp_call B PST ARx RG.
Proof.
intros T17 T18. unfold stmt_snp_call.
intros W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F id idv Post
  HJ Hsp Hsp16 Hgp Htp Hra Hraw R10 R11 R12 R13 R14 Hidv Hid HF Hsh Hrom Hgd K.
set (T := relay_instance_gone_b_c.instance_prefix id) in *.
destruct (ts_T id) as [TR TL27]. fold T in TR, TL27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17232) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (ts_jframe W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k HJ) as (HAR & Hin & Hceil).
destruct (ts_frame lyc Sc Hpc W memT mdc fpos F HAR Hin HF) as (HF0 & HFc & HF32 & HFr & HFb).
pose proof (pa_obj_img 17 ltac:(lia)) as O17. pose proof (pa_obj_img 18 ltac:(lia)) as O18.
pose proof (ts_lit_apart lyc Sc Hpc W memT mdc fpos F (VAL (A_OBJ 18)) HAR Hin HF ltac:(lia)) as A18.
assert (Hsp' : alloc_ceiling <= spZ regsT - 3 * ESTACK) by lia.
destruct (ts_lit 17 TP_FMT W regsT memT lyc Sc Hpc mdc ltac:(lia) HLIT17
  ltac:(unfold TP_FMT; repeat constructor; lia) HAR Hrom Hsp') as [E17s E17r].
destruct (ts_lit 18 RelayModel.K_GESTURE W regsT memT lyc Sc Hpc mdc ltac:(lia) HLIT18
  ltac:(unfold RelayModel.K_GESTURE; repeat constructor; lia) HAR Hrom Hsp') as [E18s E18r].
assert (E17t : atail_vis W memT (VAL (A_OBJ 17) + Z.of_nat (length TP_FMT))) by (apply ts_tail_vis; exact T17).
assert (E18t : atail_vis W memT (VAL (A_OBJ 18) + Z.of_nat (length RelayModel.K_GESTURE)))
  by (apply ts_tail_vis; exact T18).
(* the narrowing's premises (W_sites_x.v asnprintf_realizes_x; SnpNarrowSites.v at this placement): the format and
   "param_gesture" below the GOT word (HLITGOT), the buffer F + 32 above the image (san_M2_x_pi at LAWS / IMGC) *)
destruct (SnpNarrowSites.san_M1_pi (PI := PI) TP_FMT eq_refl (proj1 HLITGOT)) as (N1a & N1b).
assert (E13 : bv_unsigned (getr regsT 13) = VAL (A_OBJ 18))
  by (rewrite R13; unfold w64; apply unsigned_lit_small; lia).
pose proof (SnpNarrowSites.san_M2_x_pi (PI := PI) B ARx hl LAWS IMGC lyc Sc Hpc W memT mdc fpos HAR Hin) as N2.
rewrite HF in N2.
eapply SRr_bind.
{ apply (aj_gx_entry_at_x B PST ARx LAWS (G_RIG B RG) 0 [] (3 * ESTACK) (SIGMA WS_snprintf)
    (fun a => F + 32 <= a < F + 32 + 48)
    (fun regs' mem' => getr regs' 10 = w64 (Z.of_nat (length T)) /\
       abytes_at W mem' (F + 32) (printf_facts_c.pf_bytes (firstn (Z.to_nat (48 - 1)) T ++ [0])))
    W regsT memT RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc mdc k (-224) raw HGRIG eq_refl HJ
    ltac:(lia) eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Hgp Htp Hra Hraw).
  - intros a. destruct (Z_lt_dec a (F + 32)) as [H|H]; [right; lia|].
    destruct (Z_lt_dec a (F + 32 + 48)) as [H'|H']; [left; lia | right; lia].
  - intros a Ha _. cbv beta in Ha. apply (aview_some_of_apresent SEGS). apply (proj1 (HFb a ltac:(lia))).
  - intros a Ha _. cbv beta in Ha. split; [|lia]. unfold awr_byte. right. right. right.
    unfold in_frames. exists 1, fpos. split; [apply in_eq|].
    left. unfold in_zr. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 1) with 128. lia.
  - intros HPRE HSC. eapply SRr_mono.
    { apply (ASNPRINTF lyc Sc Hpc W regsT memT mdc (F + 32) 48 (VAL (A_OBJ 17)) TP_FMT
        [printf_facts_c.Ps; printf_facts_c.PLit 32; printf_facts_c.Pd; printf_facts_c.PLit 32]
        [printf_facts_c.APtr RelayModel.K_GESTURE; printf_facts_c.AInt id] T Hgd
        (ecall_pre_stk_of_x B ARx (3 * ESTACK) lyc Sc Hpc W regsT memT mdc HPRE HSC) R10 R11 R12
        ltac:(lia) ltac:(lia) ltac:(lia) E17s eq_refl eq_refl N1a N1b
        (fun s Hs => SnpNarrowSites.san_M3_pi (PI := PI) (getr regsT 13) id s E13 (proj2 HLITGOT) Hs) N2
        eq_refl ltac:(lia) E17r E17t).
      + (* the arguments: "param_gesture" in the image, apart from the buffer; id in a4 *)
        cbn [apf_args_ok apf_arg_ok]. rewrite R13, R14. unfold w64.
        rewrite (unsigned_lit_small (VAL (A_OBJ 18))) by lia.
        split; [|split; [|exact I]].
        * split; [unfold RelayModel.K_GESTURE; repeat constructor; lia|].
          split; [lia|]. split; [exact E18s|]. split; [exact E18r|]. split; [exact E18t|].
          change (Z.of_nat (length RelayModel.K_GESTURE)) with 13. lia.
        * split; [exact Hid|]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
          rewrite Z.mod_mod_divide; [exact Hidv|]. exists (2 ^ 32). reflexivity.
      + (* the buffer F + 32 .. F + 80: frame bytes (present, not the runtime's), below the scratch, its shadow *)
        unfold awrite_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
        { intros a Ha. destruct (HFb a ltac:(lia)) as [Hpa Hno].
          split; [exact (apresent_writable SEGS _ _ _ Hpa)|]. split; [exact Hno|]. unfold ascratch_stk. lia. }
        split; [apply amem_range_high; lia|]. split; [exact (ts_ra W memT F 48 HF32 ltac:(lia) Hsh)|].
        intros _. exact (ts_hull lyc Sc Hpc W memT mdc fpos F 48 HAR Hin HF ltac:(lia)).
      + (* seven bytes past the buffer (the shared snprintf route's amem_range d (n + 7)): F + 87 <= F + 128 *)
        apply amem_range_high; lia.
      + exact (rt_rom_view_of_rom_view B W memT Hrom). }
    intros W' c' _ Hp'. apply aentry_post_of_art_post_x. exact Hp'. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (R10' & Hby) & Hfr & Hpres).
assert (EF : firstn (Z.to_nat (48 - 1)) T = T) by (apply firstn_all2; change (Z.to_nat (48 - 1)) with 47%nat; lia).
rewrite EF in Hby.
apply (K regs2 mem2 md2 HJ2 HP2 R10').
- apply ts_garr8_of_abytes; [apply Forall_app; split; [exact TR | repeat constructor; lia] | exact Hby].
- intros a Ha H1 H2. apply Hfr; [exact Ha | cbv beta; lia | lia].
- exact Hpres.
Qed.

(* ------------------------------------------------------------------ S2. strlen at 0x82ec0 *)
(* ASTRLEN at x = F + 32, kk = |pre|, by aj_strlen_gx_at_x: the bytes and the NUL from the garr8 premise, the rest of
   the NUL's granule inside the fake frame (present), the shadow as for snprintf. *)
(* the two tails from HLIT17 / HLIT18 (glit_at_x's fourth conjunct, added to the cx at 36f4712b8a5 on this finding) *)
Lemma snp_call : stmt_snp_call B PST ARx RG.
Proof.
apply snp_call_tail.
- exact (ts_lit_tail_of 17 RIG_FMT HLIT17).
- exact (ts_lit_tail_of 18 RelayModel.K_GESTURE HLIT18).
Qed.

Lemma strlen_call : stmt_strlen_call B PST ARx RG.
Proof.
unfold stmt_strlen_call.
intros W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F pre Post
  HJ Hsp Hsp16 Hgp Htp Hra Hraw R10 HF Hg Hnz Hlen Hsh Hrom K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17232) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (ts_jframe W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k HJ) as (HAR & Hin & Hceil).
destruct (ts_frame lyc Sc Hpc W memT mdc fpos F HAR Hin HF) as (HF0 & HFc & HF32 & HFr & HFb).
eapply SRr_bind.
{ apply (aj_strlen_gx_at_x B PST ARx LAWS (SIGMA WS_strlen) ASTRLEN (G_RIG B RG) 0 [] W regsT memT RIG_STK_x sp0 FP ly S Hp
    W0 mem md [(1, fpos)] lyc Sc Hpc mdc k (F + 32) (Z.of_nat (length pre)) (-224) raw HGRIG eq_refl HJ R10
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) ltac:(lia) Hgp Htp Hra Hraw).
  - unfold first_byte. split; [lia|]. split.
    + intros i Hi. exists (nth (Z.to_nat i) pre 0). split.
      * pose proof (ge_garr8_aview (w_H W) memT (F + 32) (pre ++ [0]) (Z.to_nat i) Hg
          ltac:(rewrite length_app; cbn [length]; lia)) as Hv.
        rewrite Z2Nat.id in Hv by lia. rewrite app_nth1 in Hv by lia. exact Hv.
      * intros E. apply Hnz. rewrite <- E. apply nth_In. lia.
    + intros _. pose proof (ge_garr8_aview (w_H W) memT (F + 32) (pre ++ [0]) (length pre) Hg
        ltac:(rewrite length_app; cbn [length]; lia)) as Hv.
      rewrite nth_middle in Hv. exact Hv.
  - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HFb a ltac:(lia)))|]. lia.
  - intros a Ha. lia.
  - apply amem_range_high; lia.
  - apply amem_range_high; lia.
  - exact (ts_ra W memT F (Z.of_nat (length pre) + 1) HF32 ltac:(lia) Hsh).
  - exact (ts_hull lyc Sc Hpc W memT mdc fpos F (Z.of_nat (length pre) + 1) HAR Hin HF ltac:(lia)).
  - intros a Ha. pose proof (Z.mod_pos_bound (F + 32 + Z.of_nat (length pre)) 8 ltac:(lia)) as M8.
    apply (aview_some_of_apresent SEGS). apply (proj1 (HFb a ltac:(lia))).
  - exact Hrom. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & R10' & Hfr & Hpres).
apply (K regs2 mem2 md2 HJ2 HP2 R10').
- intros a Ha Hn. apply Hfr; [exact Ha | lia].
- exact Hpres.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the two runtime calls at a world relation R.  Each X_xR is X above with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the cx file's carriers (GLIVE, RGO, RGI, RGE, gPOST)
   and W_rig_top_defs.v's journal statements -> their R twins, the runtime entries -> aj_gx_entry_at_xR / aj_strlen_gx_at_xR (W_sites_x.v).  Every other token is X's.  The hypothesis list is
   the cx file's Section wR, verbatim. ---- *)
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
(* :286 ts_jframe *)
Lemma ts_jframe_xR : forall W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k,
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W
    memT mdc k ->
  ARx lyc Sc Hpc W memT mdc /\ In (1, fpos) (frames Sc) /\ alloc_ceiling + RIG_STK_x <= sp0.
Proof.
intros W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k HJ.
destruct HJ as (_ & _ & (memS & HJi & _) & _).
destruct HJi as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & _).
split; [exact HAR|]. split; [rewrite Hfrs; apply in_or_app; left; apply in_eq | lia].
Qed.
(* :406 snp_call_tail *)
Lemma snp_call_tail_xR : ts_lit_tail 17 6 -> ts_lit_tail 18 13 -> stmt_snp_call_xR B PST ARx RG R.
Proof.
intros T17 T18. unfold stmt_snp_call_xR.
intros W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F id idv Post
  HJ Hsp Hsp16 Hgp Htp Hra Hraw R10 R11 R12 R13 R14 Hidv Hid HF Hsh Hrom Hgd K.
set (T := relay_instance_gone_b_c.instance_prefix id) in *.
destruct (ts_T id) as [TR TL27]. fold T in TR, TL27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17232) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (ts_jframe_xR W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k HJ) as (HAR & Hin & Hceil).
destruct (ts_frame lyc Sc Hpc W memT mdc fpos F HAR Hin HF) as (HF0 & HFc & HF32 & HFr & HFb).
pose proof (pa_obj_img 17 ltac:(lia)) as O17. pose proof (pa_obj_img 18 ltac:(lia)) as O18.
pose proof (ts_lit_apart lyc Sc Hpc W memT mdc fpos F (VAL (A_OBJ 18)) HAR Hin HF ltac:(lia)) as A18.
assert (Hsp' : alloc_ceiling <= spZ regsT - 3 * ESTACK) by lia.
destruct (ts_lit 17 TP_FMT W regsT memT lyc Sc Hpc mdc ltac:(lia) HLIT17
  ltac:(unfold TP_FMT; repeat constructor; lia) HAR Hrom Hsp') as [E17s E17r].
destruct (ts_lit 18 RelayModel.K_GESTURE W regsT memT lyc Sc Hpc mdc ltac:(lia) HLIT18
  ltac:(unfold RelayModel.K_GESTURE; repeat constructor; lia) HAR Hrom Hsp') as [E18s E18r].
assert (E17t : atail_vis W memT (VAL (A_OBJ 17) + Z.of_nat (length TP_FMT))) by (apply ts_tail_vis; exact T17).
assert (E18t : atail_vis W memT (VAL (A_OBJ 18) + Z.of_nat (length RelayModel.K_GESTURE)))
  by (apply ts_tail_vis; exact T18).
(* the narrowing's premises (W_sites_x.v asnprintf_realizes_x; SnpNarrowSites.v at this placement): the format and
   "param_gesture" below the GOT word (HLITGOT), the buffer F + 32 above the image (san_M2_x_pi at LAWS / IMGC) *)
destruct (SnpNarrowSites.san_M1_pi (PI := PI) TP_FMT eq_refl (proj1 HLITGOT)) as (N1a & N1b).
assert (E13 : bv_unsigned (getr regsT 13) = VAL (A_OBJ 18))
  by (rewrite R13; unfold w64; apply unsigned_lit_small; lia).
pose proof (SnpNarrowSites.san_M2_x_pi (PI := PI) B ARx hl LAWS IMGC lyc Sc Hpc W memT mdc fpos HAR Hin) as N2.
rewrite HF in N2.
eapply (SRrG_bind SEGS R R_trans).
{ apply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_RIG B RG) 0 [] (3 * ESTACK) (SIGMA WS_snprintf)
    (fun a => F + 32 <= a < F + 32 + 48)
    (fun regs' mem' => getr regs' 10 = w64 (Z.of_nat (length T)) /\
       abytes_at W mem' (F + 32) (printf_facts_c.pf_bytes (firstn (Z.to_nat (48 - 1)) T ++ [0])))
    W regsT memT RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc mdc k (-224) raw HGRIG eq_refl HJ
    ltac:(lia) eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Hgp Htp Hra Hraw).
  - intros a. destruct (Z_lt_dec a (F + 32)) as [H|H]; [right; lia|].
    destruct (Z_lt_dec a (F + 32 + 48)) as [H'|H']; [left; lia | right; lia].
  - intros a Ha _. cbv beta in Ha. apply (aview_some_of_apresent SEGS). apply (proj1 (HFb a ltac:(lia))).
  - intros a Ha _. cbv beta in Ha. split; [|lia]. unfold awr_byte. right. right. right.
    unfold in_frames. exists 1, fpos. split; [apply in_eq|].
    left. unfold in_zr. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 1) with 128. lia.
  - intros HPRE HSC. eapply SRr_mono.
    { apply (ASNPRINTF lyc Sc Hpc W regsT memT mdc (F + 32) 48 (VAL (A_OBJ 17)) TP_FMT
        [printf_facts_c.Ps; printf_facts_c.PLit 32; printf_facts_c.Pd; printf_facts_c.PLit 32]
        [printf_facts_c.APtr RelayModel.K_GESTURE; printf_facts_c.AInt id] T Hgd
        (ecall_pre_stk_of_x B ARx (3 * ESTACK) lyc Sc Hpc W regsT memT mdc HPRE HSC) R10 R11 R12
        ltac:(lia) ltac:(lia) ltac:(lia) E17s eq_refl eq_refl N1a N1b
        (fun s Hs => SnpNarrowSites.san_M3_pi (PI := PI) (getr regsT 13) id s E13 (proj2 HLITGOT) Hs) N2
        eq_refl ltac:(lia) E17r E17t).
      + (* the arguments: "param_gesture" in the image, apart from the buffer; id in a4 *)
        cbn [apf_args_ok apf_arg_ok]. rewrite R13, R14. unfold w64.
        rewrite (unsigned_lit_small (VAL (A_OBJ 18))) by lia.
        split; [|split; [|exact I]].
        * split; [unfold RelayModel.K_GESTURE; repeat constructor; lia|].
          split; [lia|]. split; [exact E18s|]. split; [exact E18r|]. split; [exact E18t|].
          change (Z.of_nat (length RelayModel.K_GESTURE)) with 13. lia.
        * split; [exact Hid|]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
          rewrite Z.mod_mod_divide; [exact Hidv|]. exists (2 ^ 32). reflexivity.
      + (* the buffer F + 32 .. F + 80: frame bytes (present, not the runtime's), below the scratch, its shadow *)
        unfold awrite_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
        { intros a Ha. destruct (HFb a ltac:(lia)) as [Hpa Hno].
          split; [exact (apresent_writable SEGS _ _ _ Hpa)|]. split; [exact Hno|]. unfold ascratch_stk. lia. }
        split; [apply amem_range_high; lia|]. split; [exact (ts_ra W memT F 48 HF32 ltac:(lia) Hsh)|].
        intros _. exact (ts_hull lyc Sc Hpc W memT mdc fpos F 48 HAR Hin HF ltac:(lia)).
      + (* seven bytes past the buffer (the shared snprintf route's amem_range d (n + 7)): F + 87 <= F + 128 *)
        apply amem_range_high; lia.
      + exact (rt_rom_view_of_rom_view B W memT Hrom). }
    intros W' c' _ Hp'. apply aentry_post_of_art_post_x. exact Hp'. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (R10' & Hby) & Hfr & Hpres).
assert (EF : firstn (Z.to_nat (48 - 1)) T = T) by (apply firstn_all2; change (Z.to_nat (48 - 1)) with 47%nat; lia).
rewrite EF in Hby.
apply (K regs2 mem2 md2 HJ2 HP2 R10').
- apply ts_garr8_of_abytes; [apply Forall_app; split; [exact TR | repeat constructor; lia] | exact Hby].
- intros a Ha H1 H2. apply Hfr; [exact Ha | cbv beta; lia | lia].
- exact Hpres.
Qed.
(* :487 snp_call *)
Lemma snp_call_xR : stmt_snp_call_xR B PST ARx RG R.
Proof.
apply snp_call_tail_xR.
- exact (ts_lit_tail_of 17 RIG_FMT HLIT17).
- exact (ts_lit_tail_of 18 RelayModel.K_GESTURE HLIT18).
Qed.
(* :494 strlen_call *)
Lemma strlen_call_xR : stmt_strlen_call_xR B PST ARx RG R.
Proof.
unfold stmt_strlen_call_xR.
intros W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F pre Post
  HJ Hsp Hsp16 Hgp Htp Hra Hraw R10 HF Hg Hnz Hlen Hsh Hrom K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17232) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (ts_jframe_xR W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k HJ) as (HAR & Hin & Hceil).
destruct (ts_frame lyc Sc Hpc W memT mdc fpos F HAR Hin HF) as (HF0 & HFc & HF32 & HFr & HFb).
eapply (SRrG_bind SEGS R R_trans).
{ apply (aj_strlen_gx_at_xR B PST ARx LAWS R_trans WLE_R (SIGMA WS_strlen) ASTRLEN (G_RIG B RG) 0 [] W regsT memT RIG_STK_x sp0 FP ly S Hp
    W0 mem md [(1, fpos)] lyc Sc Hpc mdc k (F + 32) (Z.of_nat (length pre)) (-224) raw HGRIG eq_refl HJ R10
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) ltac:(lia) Hgp Htp Hra Hraw).
  - unfold first_byte. split; [lia|]. split.
    + intros i Hi. exists (nth (Z.to_nat i) pre 0). split.
      * pose proof (ge_garr8_aview (w_H W) memT (F + 32) (pre ++ [0]) (Z.to_nat i) Hg
          ltac:(rewrite length_app; cbn [length]; lia)) as Hv.
        rewrite Z2Nat.id in Hv by lia. rewrite app_nth1 in Hv by lia. exact Hv.
      * intros E. apply Hnz. rewrite <- E. apply nth_In. lia.
    + intros _. pose proof (ge_garr8_aview (w_H W) memT (F + 32) (pre ++ [0]) (length pre) Hg
        ltac:(rewrite length_app; cbn [length]; lia)) as Hv.
      rewrite nth_middle in Hv. exact Hv.
  - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HFb a ltac:(lia)))|]. lia.
  - intros a Ha. lia.
  - apply amem_range_high; lia.
  - apply amem_range_high; lia.
  - exact (ts_ra W memT F (Z.of_nat (length pre) + 1) HF32 ltac:(lia) Hsh).
  - exact (ts_hull lyc Sc Hpc W memT mdc fpos F (Z.of_nat (length pre) + 1) HAR Hin HF ltac:(lia)).
  - intros a Ha. pose proof (Z.mod_pos_bound (F + 32 + Z.of_nat (length pre)) 8 ltac:(lia)) as M8.
    apply (aview_some_of_apresent SEGS). apply (proj1 (HFb a ltac:(lia))).
  - exact Hrom. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & R10' & Hfr & Hpres).
apply (K regs2 mem2 md2 HJ2 HP2 R10').
- intros a Ha Hn. apply Hfr; [exact Ha | lia].
- exact Hpres.
Qed.
End wR.

End c.
End b.
End a.
