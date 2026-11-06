(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment TOP of the IMAGE-B walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan-ubsan), its second half: top_p2, the walk from the mid cut PD (0x82e6c, after entry i's drain
   step) through snprintf (0x82eb8) and strlen (0x82ec0) to RGI i 0 r (0x82f08) or RGE i (0x830c4), over the
   lemma-track statements of lib/B/W_rig_top_defs.v as premises.  Ported from k3's image-A top_p2
   (a working branch 80fffa8e840, lib/A/W_rig_top.v:880-1289) to image B's code
   (fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record) 86246-86284, lib/B/W_listing.v slots 754-792): the g_src reload at 0x82e6c and its
   checks (the pointer-overflow trap 0x82e80 by W_traps.v trap_ptr_bltu; the others decided by the seat's facts,
   W_traps.v SEAT RECIPE R1 / R2), the store of i at 80(sp), F's shadow bytes 4 .. 9, the call arguments from the
   loop's frame slots, and the shadow check of s->nheld (0x82ed8-0x82ee4, fast path) by a shadow entry.
   ROUTE (b), STEP 3 (the image-A twin: a Theorem Labs lane's RIG_x round of lib/A/W_rig_top.v top_p2, commit f4cd818e98d): over
   ARx at W_relay_instance_gone_cx.v's generic Section.  The fake frame is only 32-aligned in a generic state
   (alx_frames), so F's shadow address is 4-aligned: tp2_facts2 seats atom 20 at alignment 2 and tp2_seat2 reads
   `sh mod 4 = 0` (Hsh4).
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rig_top_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
(* route R: a Theorem Labs lane's dr_spec_xR / ge_spec_xR, SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* ---- byte lists (A's lib/A/W_rr_scan.v rrs_concat_split / rrs_eb_len / rrs_concat_len, renamed) ---- *)
Lemma tp2_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma tp2_concat_split : forall {X : Type} (f : X -> list byte) (l : list X) (d : X) (i : nat),
  (i < length l)%nat ->
  concat (map f l) = concat (map f (firstn i l)) ++ f (nth i l d) ++ concat (map f (skipn (S i) l)).
Proof.
  intros X f l d. induction l as [|x l IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [firstn skipn nth map concat].
  - reflexivity.
  - rewrite (IH i ltac:(cbn [length] in Hi; lia)) at 1. cbn [map concat]. rewrite app_assoc. reflexivity.
Qed.
Lemma tp2_eb_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
intros e P1 P2. unfold entry_bytes.
rewrite !length_app, !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8, P1, P2. reflexivity.
Qed.
Lemma tp2_concat_len : forall l, Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) l ->
  length (concat (map entry_bytes l)) = (56 * length l)%nat.
Proof.
induction l as [|e l IH]; intros HF; [reflexivity|].
apply Forall_cons_iff in HF as [[P1 P2] HF]. cbn [map concat length]. rewrite length_app, (tp2_eb_len e P1 P2), (IH HF). lia.
Qed.
(* a word of eight visible bytes *)
Lemma tp2_rdword_some : forall (rd : Z -> option Z) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
pose proof (H 1 ltac:(lia)) as H1. pose proof (H 2 ltac:(lia)) as H2. pose proof (H 3 ltac:(lia)) as H3.
pose proof (H 4 ltac:(lia)) as H4. pose proof (H 5 ltac:(lia)) as H5. pose proof (H 6 ltac:(lia)) as H6.
pose proof (H 7 ltac:(lia)) as H7.
destruct (rd a); [|congruence]. destruct (rd (a + 1)); [|congruence]. destruct (rd (a + 2)); [|congruence].
destruct (rd (a + 3)); [|congruence]. destruct (rd (a + 4)); [|congruence]. destruct (rd (a + 5)); [|congruence].
destruct (rd (a + 6)); [|congruence]. destruct (rd (a + 7)); [|congruence].
eexists. reflexivity.
Qed.
(* the value of a sum of two atoms (the R2 alias of the seat at 0x82e6c) *)
Lemma tp2_add_den : forall E a b c x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> ew E c = Z_to_bv 64 (x + y) ->
  sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = sv_denot E (SOff c 0).
Proof.
intros E a b c x y Ha Hb Hc. cbn [sv_denot]. rewrite Ha, Hb, Hc, !Z.add_0_r, !Z_to_bv_bv_unsigned.
apply bv_eq. rewrite alu64_unsigned, !unsigned_lit. cbn [zalu_raw]. unfold bv_wrap, zcanon, M64.
change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.
(* A's lib/A/W_rr_tail.v regs_ok_same, renamed: seating one register at a known value *)
Lemma tp2_regs_ok_same : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr He r'. pose proof (Hr r') as Hr'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hr0; [exact Hr'|].
unfold sr_get in *. destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr'|].
rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr'].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact He.
Qed.

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

(* ======================================================================================================
   Helpers (k3's image-A top_p2 helpers, lib/A/W_rig_top.v:416-878, renamed tp2_ and relocated to image B).
   ====================================================================================================== *)
(* an image byte (seg_rom) is visible in every state: mbyte falls back to seg_rom where the memory has none *)
Lemma tp2_aview_rom : forall H (mem : word -> option byte) a,
  seg_rom SEGS (Z_to_bv 64 a) <> None -> aview SEGS H mem a <> None.
Proof.
intros H mem a Hr. unfold aview, mbyte.
destruct (mrestrict H mem (Z_to_bv 64 a)); [cbn; discriminate|].
destruct (seg_rom SEGS (Z_to_bv 64 a)); [cbn; discriminate | contradiction].
Qed.
Lemma tp2_garr8_le : forall m a n z, garr8 SEGS m a (bzs (Z_to_le_bytes n z)) -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  val_mem SEGS m a n z.
Proof.
intros m a n z Hg Hz k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n z)))%nat) by (unfold bzs; rewrite length_map, length_Z_to_le_bytes; exact Hk).
destruct (Hg k Hl) as [Hv _]. specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
rewrite Hv. apply f_equal.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite map_nth, tp2_nth_le_bytes by exact Hk. unfold bz.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Lemma tp2_table_entry : forall M G l tail k,
garr8 SEGS M G (bzs (concat (map entry_bytes l) ++ tail)) ->
Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) l -> (k < length l)%nat ->
garr8 SEGS M (G + AENT * Z.of_nat k) (bzs (entry_bytes (nth k l relay_remove_b_c.no_entry))).
Proof.
intros M G l tail k Hg HF Hk.
rewrite (tp2_concat_split entry_bytes l relay_remove_b_c.no_entry k Hk) in Hg.
unfold bzs in Hg |- *. rewrite !map_app in Hg.
apply garr8_app in Hg as [Hg _]. apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [Hg _].
assert (HF1 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (firstn k l)).
{ rewrite <- (firstn_skipn k l) in HF. apply Forall_app in HF as [HF1 _]. exact HF1. }
rewrite length_map, (tp2_concat_len _ HF1), length_firstn in Hg.
replace (Nat.min k (length l)) with k in Hg by lia.
unfold AENT. replace (G + 56 * Z.of_nat k) with (G + Z.of_nat (56 * k)) by lia. exact Hg.
Qed.
Lemma tp2_entry_nheld : forall M SA e, garr8 SEGS M SA (bzs (entry_bytes e)) -> length (re_pad1 e) = 4%nat ->
0 <= re_nheld e < 2 ^ 31 -> val_mem SEGS M (SA + 48) 4 (re_nheld e).
Proof.
intros M SA e Hg Hp He. unfold entry_bytes, bzs in Hg. rewrite !map_app in Hg.
do 8 (apply garr8_app in Hg as [_ Hg]). apply garr8_app in Hg as [Hg _].
lazymatch type of Hg with garr8 _ _ ?b _ => replace b with (SA + 48) in Hg by
  (rewrite ?length_map, ?OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4,
     ?OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8, ?Hp; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) end.
apply tp2_garr8_le; [|cbn; lia].
unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4 in Hg.
rewrite unsigned_lit_small in Hg by lia. exact Hg.
Qed.

Lemma tp2_env_agree_ewset : forall R E n w, env_agree 32 R E -> (32 <= n)%nat -> env_agree 32 R (ewset E n w).
Proof. intros R E n w [HA HD] Hn. split; [|exact HD]. intros k Hk. rewrite ew_ewset_other by lia. apply HA. exact Hk. Qed.

Lemma tp2_pres : forall regs regs' r (b : bv 5), aregs_preserved regs regs' -> bv_unsigned b = r -> acallee_saved r ->
getr regs' b = getr regs b.
Proof. intros regs regs' r b H <- Hr. rewrite <- (Z_to_bv_bv_unsigned _ b). apply H. exact Hr. Qed.

Lemma tp2_digits : forall f x acc, 0 <= x -> ~ In 0 acc ->
  ~ In 0 (printf_facts_c.pf_digits f x acc) /\ (length acc <= length (printf_facts_c.pf_digits f x acc))%nat.
Proof.
induction f as [|f IH]; intros x acc Hx Ha; cbn [printf_facts_c.pf_digits]; [split; [exact Ha | lia]|].
destruct (x <? 10) eqn:E.
- apply Z.ltb_lt in E. split; [|cbn [length]; lia].
  intros [H|H]; [lia | exact (Ha H)].
- apply Z.ltb_ge in E.
  assert (H10 : 0 <= x mod 10) by (apply Z.mod_pos_bound; lia).
  destruct (IH (x / 10) ((48 + x mod 10) :: acc)) as [H1 H2].
  + apply Z.div_pos; lia.
  + intros [H|H]; [lia | exact (Ha H)].
  + split; [exact H1|]. cbn [length] in H2. lia.
Qed.
Lemma tp2_digits_le : forall f x acc, (length (printf_facts_c.pf_digits f x acc) <= length acc + f)%nat.
Proof.
induction f as [|f IH]; intros x acc; cbn [printf_facts_c.pf_digits]; [lia|].
destruct (x <? 10); [cbn [length]; lia|]. specialize (IH (x / 10) ((48 + x mod 10) :: acc)). cbn [length] in IH. lia.
Qed.
Lemma tp2_digits11 : forall x, 0 <= x ->
  ~ In 0 (printf_facts_c.pf_digits 11 x []) /\ (1 <= length (printf_facts_c.pf_digits 11 x []) <= 11)%nat.
Proof.
intros x Hx. destruct (tp2_digits 11 x [] Hx (fun H => H)) as [H1 _]. split; [exact H1|].
pose proof (tp2_digits_le 11 x []) as H3. cbn [length] in H3. split; [|lia].
change (printf_facts_c.pf_digits 11 x []) with
  (if x <? 10 then [48 + x] else printf_facts_c.pf_digits 10 (x / 10) [48 + x mod 10]).
destruct (x <? 10) eqn:E; [cbn [length]; lia|].
apply Z.ltb_ge in E.
destruct (tp2_digits 10 (x / 10) [48 + x mod 10]) as [_ H2].
- apply Z.div_pos; lia.
- assert (Hm : 0 <= x mod 10) by (apply Z.mod_pos_bound; lia). intros [Hd|[]]; lia.
- cbn [length] in H2. lia.
Qed.
Lemma tp2_pre_nz : forall cx, ~ In 0 (gpre cx) /\ (16 <= length (gpre cx))%nat /\ (length (gpre cx) <= 27)%nat.
Proof.
intros cx. unfold gpre, relay_instance_gone_b_c.instance_prefix.
assert (HD : ~ In 0 (printf_facts_c.pf_dec (gxID cx)) /\
             (1 <= length (printf_facts_c.pf_dec (gxID cx)) <= 12)%nat).
{ unfold printf_facts_c.pf_dec. destruct (gxID cx <? 0) eqn:E.
  - apply Z.ltb_lt in E. destruct (tp2_digits11 (- gxID cx) ltac:(lia)) as [H1 H2].
    split; [intros [H|H]; [lia | exact (H1 H)] | cbn [length]; lia].
  - apply Z.ltb_ge in E. destruct (tp2_digits11 (gxID cx) E) as [H1 H2]. split; [exact H1 | lia]. }
destruct HD as [HD1 HD2]. split; [|split].
- rewrite !in_app_iff. intros [H|[H|[H|H]]].
  + unfold RelayModel.K_GESTURE in H. cbn in H. lia.
  + cbn in H. lia.
  + exact (HD1 H).
  + cbn in H. lia.
- rewrite !length_app. unfold RelayModel.K_GESTURE. cbn [length]. lia.
- rewrite !length_app. unfold RelayModel.K_GESTURE. cbn [length]. lia.
Qed.

Lemma tp2_branch_ge : forall E a b va vb, sv_denot E a = Z_to_bv 64 va -> sv_denot E b = Z_to_bv 64 vb ->
0 <= va < 2 ^ 63 -> 0 <= vb < 2 ^ 63 -> branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (va <? vb).
Proof.
intros E a b va vb Ha Hb Hva Hvb. rewrite Ha, Hb. cbn [branch_taken]. rewrite bv_lts_signed.
rewrite !bv_signed_small by (rewrite unsigned_lit_small; lia). rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma tp2_sh_den2 : forall x y, y = w64 SHADOW_OFF -> 0 <= x < 2 ^ 60 ->
alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) y = w64 (SHADOW_OFF + x / 8).
Proof.
intros x y -> Hb.
assert (H8 : 0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (x / 8) (2 ^ 64)) by lia. rewrite Z.add_comm. apply Z.mod_small. unfold SHADOW_OFF. lia.
Qed.

Lemma tp2_frm : forall cx fpos ly1 S1 Hp1 W1 m1 md1 k1,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
ARx ly1 S1 Hp1 W1 m1 md1 /\ In (1, fpos) (frames S1) /\
4096 <= frame_addr ly1 1 fpos /\ frame_addr ly1 1 fpos + 128 <= alloc_ceiling /\ in_app (frame_addr ly1 1 fpos) 128 /\
(forall a, frame_addr ly1 1 fpos <= a < frame_addr ly1 1 fpos + 128 -> ~ in_img SEGS a).
Proof.
intros cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ.
pose proof (tj_AR B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 fpos HAR Hfin) as (H1 & H2 & H3).
change (fs_frame_bytes 1) with 128 in H2, H3.
split; [exact HAR|]. split; [exact Hfin|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
intros a Ha Hi. refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR _) Hi). right. left.
exists 1, fpos. split; [exact Hfin|]. change (fs_frame_bytes 1) with 128. exact Ha.
Qed.

(* No byte outside the window P is in a run's write range (A's tp_nw with two base rewrites). *)
Ltac tp2_nw HFr NW P U1 U2 :=
lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
assert (NW : forall a, ~ P a -> ~ in_wrange Ex rs a);
[ let a := fresh "a" in let Na := fresh "Na" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a Na (r & Hin & Hr); cbv beta in Na;
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
    repeat (rewrite ew_ewset_other in Hr by lia); repeat (rewrite YN3v.ew_havoc_old in Hr by (cbv; lia));
    rewrite ?U1, ?U2 in Hr; lia | ]);
  destruct Hin
| ] end.

(* ======================================================================================================
   The seats.
   ====================================================================================================== *)
Definition TP2_PHI : Z := 140737479966720.
(* 0x82e6c: s7 = g_src's register image (A_HI 42), s2 = 56 i (atom 18), s4 = F's shadow (atom 20), s5 = the shadow
   offset (atom 21), s6 = i, s1 = sp (atom 9).  g_src holds G0 (atom 32); SA = G0 + 56 i is atom 33 with both sum
   orders as aliases (R2); 72(sp) = the id (atom 34), 88(sp) = F + 32 (atom 35); 80(sp) and F's shadow bytes 4 .. 9
   are the stretch's stores. *)
Definition tp2_sr2 : list sv := sr_set sr_atoms 23%bv (SOff (A_HI 42) 0).
Definition tp2_regions2 : smem :=
[ YP09.mkRegion (Some (A_OBJ 5)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 9%nat) 48 96 80 88
    [YP09.mkChunk 48 (CVal 8 (SOff (A_OBJ 18) 0)); YP09.mkChunk 56 (CVal 8 (SOff (A_OBJ 17) 0));
     YP09.mkChunk 72 (CVal 8 (SOff 34 0)); YP09.mkChunk 88 (CVal 8 (SOff 35 0))];
  YP09.mkRegion (Some 20%nat) 4 10 4 10 [] ].
Definition tp2_facts2 : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 5); (18%nat, mkAF 0 896 3); (20%nat, mkAF SB (SB + 2^44) 2);
          (21%nat, mkAF SB SB 0); (32%nat, mkAF 4096 TP2_PHI 4); (33%nat, mkAF 4096 TP2_PHI 3) ] []
  [ (SAlu ALU_ADD (SOff 18 0) (SOff 32 0), SOff 33 0); (SAlu ALU_ADD (SOff 32 0) (SOff 18 0), SOff 33 0) ].
Definition tp2_ss2 : sstate := mkSS A_rig_pd tp2_sr2 tp2_regions2 None tp2_facts2.
Definition tp2_Bspan0 : Z * Z := (0, 0).
Definition tp2_extra2 (G0 SA idv P : Z) : list word := map (Z_to_bv 64) [G0; SA; idv; P].

Lemma tp2_seat2 : forall (W : world SEGS) regs mem G0 SA idv P sp sh (i : Z),
getr regs 23 = Z_to_bv 64 (VAL (A_HI 42)) -> bv_unsigned (getr regs 9) = sp -> getr regs 21 = w64 SHADOW_OFF ->
bv_unsigned (getr regs 20) = sh -> SB <= sh <= SB + 2 ^ 44 -> sh mod 4 = 0 ->
getr regs 18 = w64 (56 * i) -> 0 <= i < 16 -> SA = G0 + 56 * i ->
4096 <= G0 -> G0 + 896 <= TP2_PHI -> G0 mod 16 = 0 ->
0x10000 <= VAL (A_OBJ 5) -> VAL (A_OBJ 5) + 8 <= 0x5fc000 -> 2 ^ 46 <= sp -> sp + 96 <= 2 ^ 47 -> sp mod 32 = 0 ->
0 <= idv < 2 ^ 64 -> 0 <= P < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 5)) 8 G0 ->
val_mem SEGS (mrestrict (w_H W) mem) (sp + 48) 8 (VAL (A_OBJ 18)) ->
val_mem SEGS (mrestrict (w_H W) mem) (sp + 56) 8 (VAL (A_OBJ 17)) ->
val_mem SEGS (mrestrict (w_H W) mem) (sp + 72) 8 idv ->
val_mem SEGS (mrestrict (w_H W) mem) (sp + 88) 8 P ->
(forall o, 80 <= o < 88 -> apresent (w_H W) mem (sp + o)) ->
(forall o, 4 <= o < 10 -> apresent (w_H W) mem (sh + o)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (tp2_extra2 G0 SA idv P))) tp2_ss2
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_rig_pd)) mem (seg_rom SEGS))).
Proof.
intros W regs mem G0 SA idv P sp sh i H23 H9 H21 H20 Hsh1 Hsh2 H18 Hi HSA HG1 HG2 HG3 Hs1 Hs2 Hsp1 Hsp2 Hsp3 Hid HP
  VG V48 V56 V72 V88 HP80 HPsh.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_val_range (A_OBJ 5)) as HV5r. pose proof (pa_val_range (A_OBJ 17)) as HV17r.
pose proof (pa_val_range (A_OBJ 18)) as HV18r.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (tp2_extra2 G0 SA idv P))).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 G0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 idv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 P) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (EO5 : ew E (A_OBJ 5) = Z_to_bv 64 (VAL (A_OBJ 5))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO17 : ew E (A_OBJ 17) = Z_to_bv 64 (VAL (A_OBJ 17))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO18 : ew E (A_OBJ 18) = Z_to_bv 64 (VAL (A_OBJ 18))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EH42 : ew E (A_HI 42) = Z_to_bv 64 (VAL (A_HI 42))) by (subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (U5 : base_val E (Some (A_OBJ 5)) = VAL (A_OBJ 5)) by (cbn [base_val]; rewrite EO5; apply unsigned_lit_small; lia).
assert (U9 : base_val E (Some 9%nat) = sp) by (cbn [base_val]; rewrite (EL 9%nat 9%bv eq_refl); exact H9).
assert (U20 : base_val E (Some 20%nat) = sh) by (cbn [base_val]; rewrite (EL 20%nat 20%bv eq_refl); exact H20).
assert (U21 : bv_unsigned (ew E 21) = SB)
by (rewrite (EL 21%nat 21%bv eq_refl), H21; unfold w64, SHADOW_OFF, SB; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = 56 * i)
by (rewrite (EL 18%nat 18%bv eq_refl), H18; unfold w64; apply unsigned_lit_small; lia).
assert (HSA8 : SA mod 8 = 0).
{ rewrite HSA. pose proof (Z.div_mod G0 16 ltac:(lia)) as D. rewrite HG3, Z.add_0_r in D.
  replace (G0 + 56 * i) with ((2 * (G0 / 16) + 7 * i) * 8) by lia. apply Z_mod_mult. }
assert (H568 : (56 * i) mod 8 = 0) by (replace (56 * i) with ((7 * i) * 8) by ring; apply Z_mod_mult).
unfold tp2_ss2. apply pa_entry_st_ok_full.
- unfold tp2_sr2. apply tp2_regs_ok_same; [apply regs_ok_Eimg_Ereg|].
  cbn [sv_denot]. rewrite EH42, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. exact H23.
- vm_compute. reflexivity.
- unfold tp2_regions2. repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U5.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 5)) 0 8 _ G0);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold TP2_PHI in *; zside | zside |].
    rewrite Z.add_0_r. exact VG.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); exact (HP80 o Ho)|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp 48 8 _ (VAL (A_OBJ 18)));
      [cbn [sv_denot]; rewrite EO18, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V48].
    * apply (chunk_ok_val SEGS E _ sp 56 8 _ (VAL (A_OBJ 17)));
      [cbn [sv_denot]; rewrite EO17, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V56].
    * apply (chunk_ok_val SEGS E _ sp 72 8 _ idv);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V72].
    * apply (chunk_ok_val SEGS E _ sp 88 8 _ P);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V88].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U20.
    split; [unfold SB in *; lia|]. split; [unfold SB in *; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (HPsh o Ho).
- apply pairwise_disjoint_of_extents.
  unfold tp2_regions2, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U5, U9, U20.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SB in *. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [tp2_facts2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EL 9%nat 9%bv eq_refl), H9, U18, (EL 20%nat 20%bv eq_refl), H20, U21, E32, E33, !unsigned_lit_small
      by (unfold TP2_PHI in *; lia).
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 4) with 16. change (2 ^ 2) with 4.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB, TP2_PHI in *. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
  + cbn [tp2_facts2 f_alias alias_ok]. split; [|split; [|exact I]].
    * apply (tp2_add_den E 18 32 33 (56 * i) G0); [rewrite (EL 18%nat 18%bv eq_refl); exact H18 | exact E32 |].
      rewrite E33, HSA; try (f_equal; lia).
    * apply (tp2_add_den E 32 18 33 G0 (56 * i)); [exact E32 | rewrite (EL 18%nat 18%bv eq_refl); exact H18 |].
      rewrite E33, HSA; try (f_equal; lia).
Qed.

(* 0x82ebc, snprintf's return: nothing seated (mv a0,s4; jal strlen). *)
Definition tp2_ss3 : sstate := mkSS 2936 sr_atoms [] None (mkFacts [] [] []).
Lemma tp2_seat3 : forall (W : world SEGS) regs mem,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) tp2_ss3
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 2936)) mem (seg_rom SEGS))).
Proof.
intros W regs mem. rewrite restrict_mkst_fx. unfold tp2_ss3. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [exact I | split; exact I].
Qed.

(* 0x82ec4, strlen's return: s2 = SA (atom 18), s3 = G0 (atom 19), s5 = the shadow offset (atom 21); nheld at SA + 48
   (atom 32, an int32 >= 0), its shadow entry for the check at 0x82ee0. *)
Definition tp2_regions4 : smem :=
[ YP09.mkRegion (Some 18%nat) 48 52 48 48 [YP09.mkChunk 48 (CVal 4 (SOff 32 0))] ].
Definition tp2_facts4 : facts :=
mkFacts [ (18%nat, mkAF 4096 TP2_PHI 3); (19%nat, mkAF 4096 TP2_PHI 4); (21%nat, mkAF SB SB 0);
          (32%nat, mkAF 0 (2^31 - 1) 0) ] [] [].
Definition tp2_ss4 : sstate := mkSS 2944 sr_atoms tp2_regions4 None tp2_facts4.
Definition tp2_SH4 : list shent := [ mkSHE 18 48 52 ].
Definition tp2_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

Lemma tp2_seat4 : forall (W : world SEGS) regs mem SA G0 nh,
bv_unsigned (getr regs 18) = SA -> bv_unsigned (getr regs 19) = G0 -> getr regs 21 = w64 SHADOW_OFF ->
4096 <= SA -> SA + 56 <= TP2_PHI -> SA mod 8 = 0 -> 4096 <= G0 <= TP2_PHI -> G0 mod 16 = 0 ->
0 <= nh < 2 ^ 31 ->
val_mem SEGS (mrestrict (w_H W) mem) (SA + 48) 4 nh ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 nh])) tp2_ss4
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 2944)) mem (seg_rom SEGS))).
Proof.
intros W regs mem SA G0 nh H18 H19 H21 HS1 HS2 HS3 HG1 HG2 Hnh VN.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [Z_to_bv 64 nh])).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 nh) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U18 : base_val E (Some 18%nat) = SA) by (cbn [base_val]; rewrite (EL 18%nat 18%bv eq_refl); exact H18).
assert (U21 : bv_unsigned (ew E 21) = SB)
by (rewrite (EL 21%nat 21%bv eq_refl), H21; unfold w64, SHADOW_OFF, SB; apply unsigned_lit_small; lia).
unfold tp2_ss4. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold tp2_regions4. repeat apply Forall_cons; try apply Forall_nil.
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U18.
  split; [unfold TP2_PHI in *; lia|]. split; [unfold TP2_PHI in *; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ SA 48 4 _ nh);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VN].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [tp2_facts4 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (EL 18%nat 18%bv eq_refl), H18, (EL 19%nat 19%bv eq_refl), H19, U21, E32, unsigned_lit_small by lia.
  change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, TP2_PHI in *. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.

(* the runners over the generic journal (image A's lib/A/W_rig_top.v Lets) *)
Let RUN := paj_run_x_x B PST ARx LAWS (G_RIG B RG) HGRIG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_RIG B RG) HGRIG 0 [].
Let BR := paj_branch (PI := PI).

(* ======================================================================================================
   top_p2: PD i (0x82e6c) -> RGI i 0 r (0x82f08) | RGE i (0x830c4).
   ====================================================================================================== *)
Lemma top_p2 :
stmt_gtopm_kept B ARx MT RP MMAX RG -> stmt_live_kept B PST ARx MT RP MMAX RG -> stmt_gin_top B ARx MT RP MMAX RG ->
stmt_gout_top B ARx MT RP MMAX RG -> stmt_snp_call B PST ARx RG -> stmt_strlen_call B PST ARx RG ->
forall cx i W1 c1,
GBASE B ARx MT RP MMAX RG cx -> PD B PST ARx MT RP MMAX RG cx i W1 c1 ->
(forall r W2 c2, RGI B PST ARx MT RP MMAX RG cx i 0 r W2 c2 -> SRr SEGS W2 c2 (gPOST B PST ARx MT RP RG cx)) ->
(forall W2 c2, RGE B PST ARx MT RP MMAX RG cx i W2 c2 -> SRr SEGS W2 c2 (gPOST B PST ARx MT RP RG cx)) ->
SRr SEGS W1 c1 (gPOST B PST ARx MT RP RG cx).
Proof.
intros LTK LLK LGI LGO LSC LSL cx i W1 c1 HB HPD KI KE.
destruct HPD as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & cB & OB & capB & e1 & h1 & ev & LB & c1' & O1 & cap1 & out1
  & spent & -> & HRB & R18 & R20 & R22 & R23 & HGL & HLS & HTM & HBU).
pose proof HGL as (fpos & Hp1 & HJ & HROM1 & HPK & HFR & HLK).
pose proof HRB as (Hsp1 & Hgp1 & Htp1 & H8 & H9 & H21).
pose proof HB as (HPRE & H32 & HCNT & RGP & H10 & RID & _).
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof HLS as (L24 & L32 & L40 & L48 & L56 & L64 & L88).
pose proof HFR as (HFa & HFLa & HF120 & HF8 & HF16 & HF112 & HF72 & HSV).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17232) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (SP1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
pose proof HPRE as (_ & _ & _ & HGP0 & HTP0 & HAS0 & _). pose proof HAS0 as (_ & _ & As3 & As4 & As5 & As6 & _).
fold (gsp0 cx) in As4, As5. rewrite WS in As4.
assert (SPB : alloc_ceiling + 17104 <= gsp0 cx <= 2 ^ 47) by lia.
assert (Hsp32 : gsp1 cx mod 32 = 0) by (rewrite SP1; rewrite Zminus_mod, H32; reflexivity).
destruct (tp2_frm cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ) as (HAR1 & Hfin & HF4 & HFc & HFapp & HFni).
rewrite HFa in HF4, HFc, HFapp, HFni.
pose proof HFapp as HFA. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFA.
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 1 fpos HAR1 Hfin) as (HFal & _ & HFpres & HFSpres).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *. rewrite HFa in HFal, HFpres, HFSpres.
pose proof HTM as (Hi & Hlq & Hrel & HGD & Hrly & Hout & Hdone & Hsrc1 & Hdrs & Hgs & Hperm).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HREL0 & _). pose proof HREL0 as (_ & _ & _ & _ & _ & _ & Rlen0 & _).
pose proof Hrly as (RS1 & _ & _ & _ & _ & _ & Rlen & RSG & (tail & _ & _ & Rtab) & Rok & _).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 RSG) as (HG16 & HG4096 & HGc & HGapp & HGpres & _).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in HGc, HGapp, HGpres.
assert (Hi16 : (i < 16)%nat) by lia.
set (G0 := gxG0 cx) in *.
set (idv := bv_unsigned (getr (gxregs cx) 10)) in *.
set (SA := G0 + AENT * Z.of_nat i) in *.
assert (Hshv : shadow_addr F = SB + F / 8) by (unfold shadow_addr, SB; reflexivity).
assert (HF8b : 0 <= F / 8 <= F) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
(* F is 32-aligned (alx_frames), so its shadow address is 4-aligned *)
assert (Hsh4 : (SB + F / 8) mod 4 = 0).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HFal, Z.add_0_r in D.
  assert (F / 8 = 4 * (F / 32)) by (rewrite D at 1; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by ring; apply Z.div_mul; lia).
  assert (SB mod 4 = 0) by reflexivity. pose proof (Z.div_mod SB 4 ltac:(lia)).
  replace (SB + F / 8) with ((SB / 4 + F / 32) * 4) by lia.
  apply Z_mod_mult. }
assert (HSAm : SA mod 8 = 0).
{ unfold SA, AENT. pose proof (Z.div_mod G0 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
  replace (G0 + 56 * Z.of_nat i) with ((2 * (G0 / 16) + 7 * Z.of_nat i) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8c.
assert (Hidr : 0 <= idv < 2 ^ 64)
by (unfold idv; pose proof (bv_unsigned_in_range 64 (getr (gxregs cx) 10)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R).
pose proof (pa_obj_img 5 ltac:(lia)) as HO5.
pose proof (tp2_seat2 W1 regs1 m1 G0 SA idv (F + 32) (gsp1 cx) (shadow_addr F) (Z.of_nat i)) as HS.
specialize (HS ltac:(rewrite R23, HH42; reflexivity)
  ltac:(rewrite H9; unfold w64; apply unsigned_lit_small; lia) H21
  ltac:(rewrite R20; unfold w64; apply unsigned_lit_small; rewrite Hshv; unfold SB; lia)
  ltac:(rewrite Hshv; unfold SB; lia) ltac:(rewrite Hshv; exact Hsh4)
  R18 ltac:(lia) ltac:(unfold SA, AENT; lia)
  ltac:(lia) ltac:(unfold TP2_PHI; lia) HG16
  (proj1 HO5) (proj2 HO5)
  ltac:(rewrite SP1; lia) ltac:(rewrite SP1; lia) Hsp32
  Hidr ltac:(lia)
  ltac:(rewrite <- RGSRC; exact RS1) L48 L56 HF72 L88
  ltac:(intros o Ho; eapply ajgx_pres_x; [exact HJ | rewrite WS; lia])
  ltac:(intros o Ho; exact (proj1 (HFSpres o ltac:(lia))))).
remember (Eimg (Ereg regs1 (tp2_extra2 G0 SA idv (F + 32)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (tp2_extra2 G0 SA idv (F + 32))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 G0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 idv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (F + 32))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
clear HE.
assert (U20 : bv_unsigned (ew E 20) = shadow_addr F)
by (rewrite (EEo 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; rewrite Hshv; unfold SB; lia).
assert (U9 : bv_unsigned (ew E 9) = gsp1 cx)
by (rewrite (EEo 9%nat 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS (SOff 21 0) [] E (mrestrict (w_H W1) m1)) by constructor.
unfold cfg_at. change (w64 (BASE + A_rig_pd)) with (Z_to_bv 64 (BASE + A_rig_pd)).
pose proof HJ as HJ0.
(* 0x82e6c .. 0x82e80: g_src reloaded (s3 = G0), s2 = SA; the null checks are decided; the overflow check stops *)
paj_run_tok_x RUN HS HJ SHOK tp2_Bspan0.
{ apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons.
  { intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite U9 in Ha.
    left. split; [left; rewrite SP1, WS in *; lia | lia]. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite U20 in Ha.
  left. split; [|lia]. right; right; right. exists 1, fpos. split; [left; reflexivity|].
  right. rewrite HFa. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. lia. }
rename ms into ms1a, mat into mat1a, HF into HF1a, HFr into HFr1a, HG into HG1a.
psrr_branch_tok RUN BR HS SHOK tp2_Bspan0.
(* 0x82e80 bltu s2,s3: the pointer-overflow trap (R5), refuted by SA = G0 + 56 i >= G0 *)
{ assert (HG0p : 0 <= G0) by lia. assert (Hd0 : 0 <= AENT * Z.of_nat i) by (unfold AENT; lia).
  assert (Hsum : G0 + AENT * Z.of_nat i < 2 ^ 64) by (unfold AENT; lia).
  rewrite (trap_ptr_wrap_atom E 33 32 G0 (AENT * Z.of_nat i) E33 E32 HG0p Hd0 Hsum) in Hc.
  discriminate Hc. }
(* 0x82e84 .. 0x82eb8: 80(sp) = i, F's shadow bytes 4 .. 9 = 0, the arguments, jal snprintf *)
paj_run_tok_x RUN HS HJ SHOK tp2_Bspan0.
{ apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons.
  { intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite U9 in Ha.
    left. split; [left; rewrite SP1, WS in *; lia | lia]. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite U20 in Ha.
  left. split; [|lia]. right; right; right. exists 1, fpos. split; [left; reflexivity|].
  right. rewrite HFa. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. lia. }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RGP1. cbn [ms_mem restrict] in RGP1.
pose proof (st_ok_region_nth _ _ _ 2 _ HS eq_refl) as RGS. cbn [ms_mem restrict] in RGS.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE2 : env_agree 32 (Ereg regs1 (tp2_extra2 G0 SA idv (F + 32))) Ex)
  by (repeat first [exact HAE | apply tp2_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 _ [2; 3; 4; 8; 9; 21]%bv HS HAE2 ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
tp2_nw HFr1a NW1a (fun a => (gsp1 cx + 80 <= a < gsp1 cx + 88) \/ (shadow_addr F + 4 <= a < shadow_addr F + 10)) U9 U20.
tp2_nw HFr1 NW1 (fun a => (gsp1 cx + 80 <= a < gsp1 cx + 88) \/ (shadow_addr F + 4 <= a < shadow_addr F + 10)) U9 U20.
pmkst HS.
prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12. prreg HS (13%bv : bv 5) N13.
prreg HS (14%bv : bv 5) N14. prreg HS (1%bv : bv 5) N1. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
prreg HS (20%bv : bv 5) N20.
assert (ZSv : forall o, 4 <= o < 10 -> val_mem SEGS (mrestrict (w_H W1) (ms_mem ms1)) (shadow_addr F + o) 1 0).
{ intros o Ho. rewrite <- U20.
  assert (Ho' : o = 4 \/ o = 5 \/ o = 6 \/ o = 7 \/ o = 8 \/ o = 9) by lia.
  destruct Ho' as [-> | [-> | [-> | [-> | [-> | ->]]]]];
  (eapply (field_of_region _ _ 20 _ _ 4 10 4 10 _ 1%N (SLit 0) 0 RGS); [reflexivity | cbn [In]; tauto | reflexivity | cbn; lia | cbn; lia]). }
assert (ZS : forall o, 4 <= o < 10 -> aview SEGS (w_H W1) (ms_mem ms1) (shadow_addr F + o) = Some 0)
by (intros o Ho; apply aview_of_val_mem1; [exact (ZSv o Ho) | lia]).
assert (V80 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms1)) (gsp1 cx + 80) 8 (Z.of_nat i)).
{ rewrite <- U9.
  eapply (field_of_region _ _ 9 _ _ 48 96 80 88 _ 8%N (SOff 22 0) (Z.of_nat i) RGP1);
  [reflexivity | cbn [In]; tauto | | cbn; lia | cbn; lia].
  cbn [sv_denot]. rewrite (EEo 22%nat 22%bv eq_refl), R22. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite Z.add_0_r. reflexivity. }
assert (ROM1 : rom_view SEGS W1 (ms_mem ms1)).
{ intros a Hin.
  assert (HI : 0x10000 <= a < 0x5fc000)
    by (destruct Hin as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
  rewrite (aview_kept_out _ _ (w_H W1) _ (ms_mem ms1) HFr1 a ltac:(lia) (NW1 a ltac:(rewrite Hshv; unfold SB; lia))).
  rewrite (aview_kept_out _ _ (w_H W1) m1 _ HFr1a a ltac:(lia) (NW1a a ltac:(rewrite Hshv; unfold SB; lia))).
  exact (HROM1 a Hin). }
(* snprintf's guard: the GOT word (an AR fact) and the canary's eight bytes, image bytes (HCANR) that aview reads
   through mbyte's seg_rom fallback in every state *)
assert (GRD : aguard_ok W1 (ms_mem ms1) FR_GOT_GUARD FR_GUARD).
{ split.
  - exact (HGOTG _ _ _ _ _ _ (tj_AR B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
  - apply tp2_rdword_some. intros kk Hkk. apply tp2_aview_rom. apply HCANR. lia. }
eapply (LSC W1 (ms_regs ms1) (ms_mem ms1) (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) fpos
  ly1 S1 _ _ k1
  (Z_to_bv 64 (BASE + 2936)) F (gxID cx) idv (gPOST B PST ARx MT RP RG cx) HJ).
- unfold spZ. rewrite HK by (cbv; tauto). fold (spZ regs1). rewrite Hsp1, SP1. reflexivity.
- pose proof (Z.div_mod (gsp0 cx) 32 ltac:(lia)) as D. rewrite H32, Z.add_0_r in D. rewrite D.
  replace (32 * (gsp0 cx / 32)) with ((2 * (gsp0 cx / 32)) * 16) by ring. apply Z_mod_mult.
- rewrite HK by (cbv; tauto). rewrite Hgp1. exact HGP0.
- rewrite HK by (cbv; tauto). rewrite Htp1. exact HTP0.
- exact N1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite N10, E35. reflexivity.
- rewrite N11. reflexivity.
- change 258%nat with (A_OBJ 17) in N12.
  rewrite N12, (img_env_atomP E (A_OBJ 17) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). reflexivity.
- change 259%nat with (A_OBJ 18) in N13.
  rewrite N13, (img_env_atomP E (A_OBJ 18) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). reflexivity.
- rewrite N14, E34. reflexivity.
- unfold idv. rewrite H10. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity.
- exact RID.
- exact HFa.
- exact ZS.
- exact ROM1.
- exact GRD.
- intros regs2 mem2 md2 HJ2 HP2 HR2 HPRE2 HKP2 HPS2.
  pose proof (tp2_seat3 W1 regs2 mem2) as HS3.
  remember (Eimg (Ereg regs2 [])) as E3 eqn:HE3.
  assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; apply Eimg_env).
  assert (HAE3 : env_agree 32 (Ereg regs2 []) E3)
  by (rewrite HE3; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE3 : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E3 m = getr regs2 rr)
  by (intros m rr Hm; subst E3; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
  rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  clear HE3.
  assert (SHOK3 : sh_ok SEGS (SOff 21 0) [] E3 (mrestrict (w_H W1) mem2)) by constructor.
  (* 0x82ebc .. 0x82ec0: mv a0,s4; jal strlen *)
  paj_run_tok_x RUN HS3 HJ2 SHOK3 tp2_Bspan0. { apply awr_ok_x_nil. }
  rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs2 _ [2; 3; 4; 8; 9; 18; 19; 20; 21]%bv HS3 HAE3 ltac:(vm_compute; reflexivity))
    as HK3.
  cbn [ms_regs restrict] in HK3.
  pmkst HS3.
  prreg HS3 (10%bv : bv 5) Q10. prreg HS3 (1%bv : bv 5) Q1.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) mem2 a)
  by (intros a Ha; apply (aview_kept_out E3 _ (w_H W1) mem2 (ms_mem ms2) HFr2 a Ha); intros (r & Hin & _); destruct Hin).
  assert (U2s : spZ (ms_regs ms1) = gsp1 cx) by (unfold spZ; rewrite HK by (cbv; tauto); exact Hsp1).
  destruct (tp2_pre_nz cx) as (PNZ & PL1 & PL2).
  eapply (LSL W1 (ms_regs ms2) (ms_mem ms2) (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) fpos
    ly1 S1 _ _ k1
    (Z_to_bv 64 (BASE + 2944)) F (gpre cx) (gPOST B PST ARx MT RP RG cx) HJ2).
  + unfold spZ. rewrite (HK3 2%bv ltac:(cbv; tauto)).
    rewrite (tp2_pres _ _ 2 2%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)). fold (spZ (ms_regs ms1)).
    rewrite U2s, SP1. reflexivity.
  + pose proof (Z.div_mod (gsp0 cx) 32 ltac:(lia)) as D. rewrite H32, Z.add_0_r in D. rewrite D.
    replace (32 * (gsp0 cx / 32)) with ((2 * (gsp0 cx / 32)) * 16) by ring. apply Z_mod_mult.
  + rewrite (HK3 3%bv ltac:(cbv; tauto)). rewrite (tp2_pres _ _ 3 3%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)), HK
      by (cbv; tauto). rewrite Hgp1. exact HGP0.
  + rewrite (HK3 4%bv ltac:(cbv; tauto)). rewrite (tp2_pres _ _ 4 4%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)), HK
      by (cbv; tauto). rewrite Htp1. exact HTP0.
  + exact Q1.
  + apply ret_ok_codeptr_v; [lia | reflexivity].
  + rewrite Q10, (EE3 20%nat 20%bv eq_refl), (tp2_pres _ _ 20 20%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)), N20, E35.
    reflexivity.
  + exact HFa.
  + unfold arm in *. eapply ge_garr8_kept; [exact HPRE2|]. intros b Hb. apply K3. rewrite length_app in Hb. cbn [length] in Hb. lia.
  + exact PNZ.
  + lia.
  + intros o Ho. rewrite K3 by (rewrite Hshv; unfold SB; lia).
    rewrite HKP2; [exact (ZS o Ho) | rewrite Hshv; unfold SB; lia | rewrite Hshv; unfold SB; lia |
      rewrite Hshv; unfold SB; rewrite ?SP1 in *; lia].
  + intros a Hin.
    assert (HI : 0x10000 <= a < 0x5fc000)
      by (destruct Hin as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
    rewrite K3 by lia. rewrite HKP2; [exact (ROM1 a Hin) | lia | | rewrite ?SP1 in *; lia].
    intros Hb. apply (HFni a ltac:(lia)). destruct Hin as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr].
  + intros regs4 mem4 md4 HJ4 HP4 HR4 HKP4 HPS4.
    assert (GR : forall (r : bv 5) n, bv_unsigned r = n -> acallee_saved n -> In r [2; 3; 4; 8; 9; 18; 19; 20; 21]%bv ->
      getr regs4 r = getr (ms_regs ms1) r).
    { intros r n Hn Hcs Hin. rewrite (tp2_pres _ _ n r HP4 Hn Hcs), (HK3 r Hin). exact (tp2_pres _ _ n r HP2 Hn Hcs). }
    assert (U18r : bv_unsigned (getr regs4 18) = SA).
    { rewrite (GR 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), N18, E33.
      apply unsigned_lit_small. unfold SA, AENT. lia. }
    assert (U19r : bv_unsigned (getr regs4 19) = G0).
    { rewrite (GR 19%bv 19 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), N19, E32.
      apply unsigned_lit_small. lia. }
    assert (R21r : getr regs4 21 = w64 SHADOW_OFF).
    { rewrite (GR 21%bv 21 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), HK by (cbv; tauto). exact H21. }
    assert (U9r : bv_unsigned (getr regs4 9) = gsp1 cx).
    { rewrite (GR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), HK by (cbv; tauto). rewrite H9.
      unfold w64. apply unsigned_lit_small. lia. }
    (* GTOPM at strlen's return memory: the table's entry i, its nheld *)
    assert (KEEP14 : forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a ->
      aview SEGS (w_H W1) mem4 a = aview SEGS (w_H W1) m1 a).
    { intros a Ha Hnf.
      assert (Nsh : ~ (shadow_addr F + 4 <= a < shadow_addr F + 10)).
      { intros Hs. apply Hnf. exists 1, fpos. split; [left; reflexivity|]. right. rewrite HFa. unfold in_zr. cbn [fst snd].
        change (fs_frame_bytes 1 / 8) with 16. lia. }
      assert (Nbf : ~ (F + 32 <= a < F + 80)).
      { intros Hs. apply Hnf. exists 1, fpos. split; [left; reflexivity|]. left. rewrite HFa. unfold in_zr. cbn [fst snd].
        change (fs_frame_bytes 1) with 128. lia. }
      rewrite HKP4 by (rewrite ?SP1 in *; lia). rewrite K3 by lia. rewrite HKP2 by (rewrite ?SP1 in *; lia).
      assert (NPa : ~ ((gsp1 cx + 80 <= a < gsp1 cx + 88) \/ (shadow_addr F + 4 <= a < shadow_addr F + 10))) by lia.
      rewrite (aview_kept_out _ _ (w_H W1) _ (ms_mem ms1) HFr1 a ltac:(lia) (NW1 a NPa)).
      exact (aview_kept_out _ _ (w_H W1) m1 _ HFr1a a ltac:(lia) (NW1a a NPa)). }
    assert (PRES14 : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mem4 a).
    { intros a Hp. apply HPS4. eapply apresent_grows; [exact HG2|]. apply HPS2.
      eapply apresent_grows; [exact HG1|]. eapply apresent_grows; [exact HG1a | exact Hp]. }
    pose proof (LTK cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 mem4 fpos HB HAR1 Hfin KEEP14 PRES14 HTM)
      as HTM4.
    pose proof HTM4 as (_ & _ & _ & _ & Hrly4 & _).
    pose proof Hrly4 as (_ & _ & _ & _ & _ & _ & _ & _ & (tail4 & _ & _ & Rtab4) & Rok4 & _).
    assert (HLmq : length (map fst qd) = i) by (rewrite length_map; exact Hlq).
    assert (Hok4 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat)
      (map fst qd ++ e1 :: skipn (S i) (gxes cx))).
    { eapply Forall_impl; [|exact Rok4]. intros e (_ & _ & Q1' & Q2' & _). split; assumption. }
    assert (Hnth : nth i (map fst qd ++ e1 :: skipn (S i) (gxes cx)) relay_remove_b_c.no_entry = e1).
    { rewrite app_nth2 by lia. rewrite HLmq, Nat.sub_diag. reflexivity. }
    assert (HLtab : (i < length (map fst qd ++ e1 :: skipn (S i) (gxes cx)))%nat)
      by (rewrite length_app, HLmq; cbn [length]; lia).
    pose proof (tp2_table_entry _ _ _ _ i Rtab4 Hok4 HLtab) as HTE4. rewrite Hnth in HTE4.
    assert (HEOK4 : aentry_ok B ly1 S1 W1 mem4 e1).
    { rewrite Forall_forall in Rok4. apply Rok4. apply in_or_app. right. left. reflexivity. }
    pose proof HEOK4 as (_ & _ & Hp14 & _ & _ & _ & _ & _ & _ & _ & Hnh26 & _).
    assert (Hnh0 : 0 <= re_nheld e1) by (unfold re_nheld; lia).
    assert (Hnh31 : 0 <= re_nheld e1 < 2 ^ 31) by lia.
    pose proof (tp2_entry_nheld _ _ _ HTE4 Hp14 Hnh31) as VN4.
    assert (VN4' : val_mem SEGS (mrestrict (w_H W1) mem4) (SA + 48) 4 (re_nheld e1)) by exact VN4.
    pose proof (tj_AR B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4.
    assert (HSA1 : 4096 <= SA) by (unfold SA, AENT; lia).
    assert (HSA2 : SA + 56 <= TP2_PHI) by (unfold SA, AENT, TP2_PHI; lia).
    assert (HG0b : 4096 <= G0 <= TP2_PHI) by (unfold TP2_PHI; lia).
    pose proof (tp2_seat4 W1 regs4 mem4 SA G0 (re_nheld e1) U18r U19r R21r HSA1 HSA2 HSAm HG0b HG16 Hnh31 VN4') as HS4.
    remember (Eimg (Ereg regs4 [Z_to_bv 64 (re_nheld e1)])) as E4 eqn:HE4.
    assert (HEI4 : img_env VAL A_LIM E4) by (subst E4; apply Eimg_env).
    assert (HAE4 : env_agree 32 (Ereg regs4 [Z_to_bv 64 (re_nheld e1)]) E4)
    by (rewrite HE4; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EE4 : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E4 m = getr regs4 rr)
    by (intros m rr Hm; subst E4; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
    rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
    assert (E4_32 : ew E4 32 = Z_to_bv 64 (re_nheld e1))
      by (subst E4; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 0)).
    clear HE4.
    assert (HBx4 : U E4 (SOff 21 0) = SHADOW_OFF)
      by (rewrite (U_atom E4 21 SHADOW_OFF ltac:(rewrite (EE4 21%nat 21%bv eq_refl); exact R21r)) by (unfold SHADOW_OFF; lia);
          reflexivity).
    assert (U18E4 : U E4 (SOff 18 0) = SA).
    { apply U_atom; [|unfold SA, AENT; lia]. rewrite (EE4 18%nat 18%bv eq_refl), <- U18r. symmetry. apply Z_to_bv_bv_unsigned. }
    assert (SHOK4 : sh_ok SEGS (SOff 21 0) tp2_SH4 E4 (mrestrict (w_H W1) mem4)).
    { constructor; [|constructor].
      eapply shent_ok_of_range.
      + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 _ W1 mem4 _ G0 ATABLE (SA + 48) 4 HAR4 RSG);
        [unfold SA, AENT; lia | rewrite RQT; unfold SA, AENT; lia].
      + exact HBx4.
      + exact U18E4.
      + lia.
      + lia.
      + intros x Hx. pose proof HGapp as HGA. revert Hx HGA Hi16. unfold SA, AENT. clear.
        unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros Hx HGA Hi16. lia. }
    pose proof HJ4 as HJ40.
    (* 0x82ec4 .. 0x82eec: the alignment and null traps of SA / G0 (decided), s8 = |prefix|, the shadow check of
       &nheld (fast path, the shadow entry), nheld; stops at blez *)
    paj_run_tok_x RUN HS4 HJ4 SHOK4 tp2_Bspan.
    { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]. }
    rename ms into ms5, mat into mat5, HF into HF5, HFr into HFr5, HG into HG5.
    rename w into w5a, w0 into w5b.
    assert (E5_32 : sv_denot (ewset (ewset E4 512 w5a) 513 w5b) (SOff 32 0) = Z_to_bv 64 (re_nheld e1))
    by (cbn [sv_denot]; rewrite !ew_ewset_other, E4_32, Z.add_0_r, Z_to_bv_bv_unsigned by lia; reflexivity).
    assert (U9E4 : bv_unsigned (ew E4 9) = gsp1 cx) by (rewrite (EE4 9%nat 9%bv eq_refl); exact U9r).
    (* 0x82eec blez a0: nheld <= 0 -> RGE i (0x830c4); nheld > 0 -> the inner loop's setup -> RGI i 0 r (0x82f08) *)
    psrr_branch_tok RUN BR HS4 SHOK4 tp2_Bspan.
    * lazymatch goal with Hb : branch_taken BC_GE _ _ = true |- _ => rename Hb into Hc4 end.
      rewrite (tp2_branch_ge (ewset (ewset E4 512 w5a) 513 w5b) (SLit 0) (SOff 32 0) 0 (re_nheld e1) eq_refl E5_32
        ltac:(lia) ltac:(lia)) in Hc4.
      assert (Hnh00 : re_nheld e1 <= 0) by (destruct (Z.ltb_spec 0 (re_nheld e1)); [discriminate Hc4 | lia]).
      paj_run_to_tok_x RUNTO HS4 HJ4 SHOK4 tp2_Bspan (AF_fr_relay_instance_gone + 0x424).
      { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]. }
      rename ms into ms6, mat into mat6, HF into HF6, HFr into HFr6, HG into HG6.
      tp2_nw HFr5 NW5 (fun _ : Z => False) U9E4 U9E4.
      tp2_nw HFr6 NW6 (fun _ : Z => False) U9E4 U9E4.
      assert (K56 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) mem4 a).
      { intros a Ha. rewrite (aview_kept_out _ _ (w_H W1) _ (ms_mem ms6) HFr6 a Ha (NW6 a (fun H => H))).
        exact (aview_kept_out _ _ (w_H W1) mem4 _ HFr5 a Ha (NW5 a (fun H => H))). }
      set (PF := fun a => (gsp1 cx - 3 * ESTACK <= a < gsp1 cx) \/ (gsp1 cx + 80 <= a < gsp1 cx + 88) \/
        (F + 32 <= a < F + 80) \/ (shadow_addr F + 4 <= a < shadow_addr F + 10)).
      assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ PF a -> aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Na. unfold PF in Na.
        assert (NPa : ~ ((gsp1 cx + 80 <= a < gsp1 cx + 88) \/ (shadow_addr F + 4 <= a < shadow_addr F + 10))) by tauto.
        rewrite K56 by lia. rewrite HKP4 by (rewrite ?SP1 in *; lia). rewrite K3 by lia. rewrite HKP2 by (rewrite ?SP1 in *; lia).
        rewrite (aview_kept_out _ _ (w_H W1) _ (ms_mem ms1) HFr1 a Ha (NW1 a NPa)).
        exact (aview_kept_out _ _ (w_H W1) m1 _ HFr1a a Ha (NW1a a NPa)). }
      assert (PRESF : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms6) a).
      { intros a Hp. eapply apresent_grows; [exact HG6|]. eapply apresent_grows; [exact HG5|]. apply PRES14. exact Hp. }
      assert (KEEPL : forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a ->
        aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Hnf. apply KEEPF; [lia|]. unfold PF. intros [X | [X | [X | X]]]; [lia | lia | |]; apply Hnf; exists 1, fpos;
        (split; [left; reflexivity|]); rewrite HFa; unfold in_zr; cbn [fst snd];
        [left; change (fs_frame_bytes 1) with 128; lia | right; change (fs_frame_bytes 1 / 8) with 16; lia]. }
      pose proof (LTK cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 (ms_mem ms6) fpos HB HAR1 Hfin KEEPL PRESF
        HTM) as HTM6.
      destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms6) _ PF HB HJ0 HROM1 HPK HFR HLK HLS HJ4) as [HGL6 HLS6].
      { intros a Ha. unfold PF in Ha. rewrite SP1 in *. lia. }
      { exact KEEPF. }
      { exact PRESF. }
      assert (V80F : val_mem SEGS (arm W1 (ms_mem ms6)) (gsp1 cx + 80) 8 (Z.of_nat i)).
      { unfold arm. eapply val_mem_kept; [|exact V80]. intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
        rewrite K56 by lia. rewrite HKP4 by (rewrite ?SP1 in *; lia). rewrite K3 by lia.
        apply HKP2; [lia | lia | rewrite ?SP1 in *; lia]. }
      lazymatch type of HS4 with st_ok_pi _ _ ?Ex _ _ => assert (HAE6 : env_agree 32 (Ereg regs4 [Z_to_bv 64 (re_nheld e1)]) Ex)
        by (repeat first [exact HAE4 | apply tp2_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs4 _ [2; 3; 4; 8; 9; 21]%bv HS4 HAE6 ltac:(vm_compute; reflexivity)) as HK6.
      cbn [ms_regs restrict] in HK6.
      pmkst HS4.
      destruct (LGO cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 spent ly1 S1 W1 (ms_mem ms6) HB HTM6 HBU Hnh00) as (qd' & HGO').
      apply KE. unfold RGE.
      exists (ms_regs ms6), ly1, S1, (ms_mem ms6). eexists. exists k1, F, FL, qd', c1', O1, cap1, out1, spent.
      split; [unfold cfg_at, A_rig_step; reflexivity|].
      split.
      { unfold gregs_base, spZ. rewrite !HK6 by (cbv; tauto).
        rewrite (GR 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 21%bv 21 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite !HK by (cbv; tauto). exact HRB. }
      split; [exact V80F|]. split; [exact Hi|]. split; [exact HGL6|]. split; [exact HLS6 | exact HGO'].
    * lazymatch goal with Hb : branch_taken BC_GE _ _ = false |- _ => rename Hb into Hc4 end.
      rewrite (tp2_branch_ge (ewset (ewset E4 512 w5a) 513 w5b) (SLit 0) (SOff 32 0) 0 (re_nheld e1) eq_refl E5_32
        ltac:(lia) ltac:(lia)) in Hc4.
      assert (Hnh01 : 0 < re_nheld e1) by (destruct (Z.ltb_spec 0 (re_nheld e1)); [lia | discriminate Hc4]).
      paj_run_to_tok_x RUNTO HS4 HJ4 SHOK4 tp2_Bspan (AF_fr_relay_instance_gone + 0x268).
      { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]. }
      rename ms into ms6, mat into mat6, HF into HF6, HFr into HFr6, HG into HG6.
      tp2_nw HFr5 NW5 (fun _ : Z => False) U9E4 U9E4.
      tp2_nw HFr6 NW6 (fun _ : Z => False) U9E4 U9E4.
      assert (K56 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) mem4 a).
      { intros a Ha. rewrite (aview_kept_out _ _ (w_H W1) _ (ms_mem ms6) HFr6 a Ha (NW6 a (fun H => H))).
        exact (aview_kept_out _ _ (w_H W1) mem4 _ HFr5 a Ha (NW5 a (fun H => H))). }
      set (PF := fun a => (gsp1 cx - 3 * ESTACK <= a < gsp1 cx) \/ (gsp1 cx + 80 <= a < gsp1 cx + 88) \/
        (F + 32 <= a < F + 80) \/ (shadow_addr F + 4 <= a < shadow_addr F + 10)).
      assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ PF a -> aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Na. unfold PF in Na.
        assert (NPa : ~ ((gsp1 cx + 80 <= a < gsp1 cx + 88) \/ (shadow_addr F + 4 <= a < shadow_addr F + 10))) by tauto.
        rewrite K56 by lia. rewrite HKP4 by (rewrite ?SP1 in *; lia). rewrite K3 by lia. rewrite HKP2 by (rewrite ?SP1 in *; lia).
        rewrite (aview_kept_out _ _ (w_H W1) _ (ms_mem ms1) HFr1 a Ha (NW1 a NPa)).
        exact (aview_kept_out _ _ (w_H W1) m1 _ HFr1a a Ha (NW1a a NPa)). }
      assert (PRESF : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms6) a).
      { intros a Hp. eapply apresent_grows; [exact HG6|]. eapply apresent_grows; [exact HG5|]. apply PRES14. exact Hp. }
      assert (KEEPL : forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a ->
        aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Hnf. apply KEEPF; [lia|]. unfold PF. intros [X | [X | [X | X]]]; [lia | lia | |]; apply Hnf; exists 1, fpos;
        (split; [left; reflexivity|]); rewrite HFa; unfold in_zr; cbn [fst snd];
        [left; change (fs_frame_bytes 1) with 128; lia | right; change (fs_frame_bytes 1 / 8) with 16; lia]. }
      pose proof (LTK cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 (ms_mem ms6) fpos HB HAR1 Hfin KEEPL PRESF
        HTM) as HTM6.
      destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms6) _ PF HB HJ0 HROM1 HPK HFR HLK HLS HJ4) as [HGL6 HLS6].
      { intros a Ha. unfold PF in Ha. rewrite SP1 in *. lia. }
      { exact KEEPF. }
      { exact PRESF. }
      assert (V80F : val_mem SEGS (arm W1 (ms_mem ms6)) (gsp1 cx + 80) 8 (Z.of_nat i)).
      { unfold arm. eapply val_mem_kept; [|exact V80]. intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
        rewrite K56 by lia. rewrite HKP4 by (rewrite ?SP1 in *; lia). rewrite K3 by lia.
        apply HKP2; [lia | lia | rewrite ?SP1 in *; lia]. }
      lazymatch type of HS4 with st_ok_pi _ _ ?Ex _ _ => assert (HAE6 : env_agree 32 (Ereg regs4 [Z_to_bv 64 (re_nheld e1)]) Ex)
        by (repeat first [exact HAE4 | apply tp2_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs4 _ [2; 3; 4; 8; 9; 21]%bv HS4 HAE6 ltac:(vm_compute; reflexivity)) as HK6.
      cbn [ms_regs restrict] in HK6.
      prreg HS4 (19%bv : bv 5) F19. prreg HS4 (22%bv : bv 5) F22. prreg HS4 (20%bv : bv 5) F20.
      prreg HS4 (23%bv : bv 5) F23. prreg HS4 (27%bv : bv 5) F27. prreg HS4 (24%bv : bv 5) F24.
      prreg HS4 (25%bv : bv 5) F25. prreg HS4 (18%bv : bv 5) F18.
      pmkst HS4.
      assert (E18' : bv_unsigned (ew E4 18) = SA) by (rewrite (EE4 18%nat 18%bv eq_refl); exact U18r).
      assert (E21' : ew E4 21 = w64 SHADOW_OFF) by (rewrite (EE4 21%nat 21%bv eq_refl); exact R21r).
      assert (E10' : ew E4 10 = w64 (Z.of_nat (length (gpre cx)))) by (rewrite (EE4 10%nat 10%bv eq_refl); exact HR4).
      set (r := (Z.to_nat (re_nheld e1) - 1)%nat).
      assert (HNHr : re_nheld e1 = Z.of_nat (S r)) by (unfold r; lia).
      assert (HPREF : garr8 SEGS (arm W1 (ms_mem ms6)) (F + 32) (gpre cx ++ [0])).
      { unfold arm in *. eapply ge_garr8_kept; [exact HPRE2|]. intros b Hb. rewrite length_app in Hb. cbn [length] in Hb.
        rewrite K56 by lia. rewrite HKP4 by (rewrite ?SP1 in *; lia). apply K3. lia. }
      assert (HZSF : garr8 SEGS (arm W1 (ms_mem ms6)) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0]).
      { intros j Hj. cbn [length] in Hj. split; [|destruct j as [|[|[|[|[|[|j]]]]]]; cbn; lia].
        replace (nth j [0; 0; 0; 0; 0; 0] 0) with 0 by (destruct j as [|[|[|[|[|[|j]]]]]]; cbn; lia).
        replace (shadow_addr F + 4 + Z.of_nat j) with (shadow_addr F + (4 + Z.of_nat j)) by lia.
        unfold arm. eapply val_mem_kept; [|exact (ZSv (4 + Z.of_nat j) ltac:(lia))].
        intros kk Hkk. change (Z.of_nat 1) with 1 in Hkk.
        replace (shadow_addr F + (4 + Z.of_nat j) + kk) with (shadow_addr F + (4 + Z.of_nat j)) by lia.
        rewrite K56 by (rewrite Hshv; unfold SB; lia). rewrite HKP4 by (rewrite Hshv; unfold SB; rewrite ?SP1 in *; lia).
        rewrite K3 by (rewrite Hshv; unfold SB; lia).
        rewrite HKP2; [reflexivity | rewrite Hshv; unfold SB; lia | rewrite Hshv; unfold SB; lia |
          rewrite Hshv; unfold SB; rewrite ?SP1 in *; lia]. }
      destruct (LGI cx i r F qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 spent ly1 S1 W1 (ms_mem ms6) HB HTM6 HBU HNHr HPREF HZSF)
        as (ks & f & HGIN).
      apply (KI r). unfold RGI.
      exists (ms_regs ms6), ly1, S1, (ms_mem ms6). eexists.
      exists k1, F, FL, qd, cB, OB, capB, e1, h1, ev, LB, c1', O1, cap1, ks, [], f, c1', O1, cap1, out1, spent.
      split; [unfold cfg_at, A_rig_inner; reflexivity|].
      split.
      { unfold gregs_base, spZ. rewrite !HK6 by (cbv; tauto).
        rewrite (GR 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 21%bv 21 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite !HK by (cbv; tauto). exact HRB. }
      split; [rewrite F19; reflexivity|].
      split; [rewrite F22; reflexivity|].
      split; [rewrite F20; reflexivity|].
      split; [rewrite F23, E18'; reflexivity|].
      split; [rewrite F27, E18'; apply (tp2_sh_den2 (SA + 48)); [exact E21' | unfold SA, AENT; lia]|].
      split; [rewrite F24; exact E10'|].
      split; [rewrite F25, E18'; reflexivity|].
      split; [rewrite F18, E18'; apply (tp2_sh_den2 (SA + 40)); [exact E21' | unfold SA, AENT; lia]|].
      split; [exact V80F|]. split; [exact HGL6|]. split; [exact HLS6 | exact HGIN].
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): TOP's second half at a world relation R.  Each X_xR is X above with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the cx file's carriers (GLIVE, RGO, RGI, RGE, gPOST)
   and W_rig_top_defs.v's journal statements -> their R twins, the runs and the branch -> their SRrG forms, the binds -> SRrG_bind SEGS R R_trans, the calls -> W_rig_top_calls.v's R twins.  Every other token is X's.  The hypothesis list is
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
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_RIG B RG) HGRIG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_RIG B RG) HGRIG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* :374 tp2_frm *)
Lemma tp2_frm_xR : forall cx fpos ly1 S1 Hp1 W1 m1 md1 k1,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
ARx ly1 S1 Hp1 W1 m1 md1 /\ In (1, fpos) (frames S1) /\
4096 <= frame_addr ly1 1 fpos /\ frame_addr ly1 1 fpos + 128 <= alloc_ceiling /\ in_app (frame_addr ly1 1 fpos) 128 /\
(forall a, frame_addr ly1 1 fpos <= a < frame_addr ly1 1 fpos + 128 -> ~ in_img SEGS a).
Proof.
intros cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ.
pose proof (tj_AR_xR B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (ajournal_gx_inner_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 fpos HAR Hfin) as (H1 & H2 & H3).
change (fs_frame_bytes 1) with 128 in H2, H3.
split; [exact HAR|]. split; [exact Hfin|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
intros a Ha Hi. refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR _) Hi). right. left.
exists 1, fpos. split; [exact Hfin|]. change (fs_frame_bytes 1) with 128. exact Ha.
Qed.
(* :587 top_p2 *)
Lemma top_p2_xR :
stmt_gtopm_kept B ARx MT RP MMAX RG -> stmt_live_kept_xR B PST ARx MT RP MMAX RG R -> stmt_gin_top B ARx MT RP MMAX RG ->
stmt_gout_top B ARx MT RP MMAX RG -> stmt_snp_call_xR B PST ARx RG R -> stmt_strlen_call_xR B PST ARx RG R ->
forall cx i W1 c1,
GBASE B ARx MT RP MMAX RG cx -> PD_xR B PST ARx MT RP MMAX RG R cx i W1 c1 ->
(forall r W2 c2, RGI_xR B PST ARx MT RP MMAX RG R cx i 0 r W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR B PST ARx MT RP RG R cx)) ->
(forall W2 c2, RGE_xR B PST ARx MT RP MMAX RG R cx i W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR B PST ARx MT RP RG R cx)) ->
SRrG SEGS R W1 c1 (gPOST_xR B PST ARx MT RP RG R cx).
Proof.
intros LTK LLK LGI LGO LSC LSL cx i W1 c1 HB HPD KI KE.
destruct HPD as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & cB & OB & capB & e1 & h1 & ev & LB & c1' & O1 & cap1 & out1
  & spent & -> & HRB & R18 & R20 & R22 & R23 & HGL & HLS & HTM & HBU).
pose proof HGL as (fpos & Hp1 & HJ & HROM1 & HPK & HFR & HLK).
pose proof HRB as (Hsp1 & Hgp1 & Htp1 & H8 & H9 & H21).
pose proof HB as (HPRE & H32 & HCNT & RGP & H10 & RID & _).
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof HLS as (L24 & L32 & L40 & L48 & L56 & L64 & L88).
pose proof HFR as (HFa & HFLa & HF120 & HF8 & HF16 & HF112 & HF72 & HSV).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17232) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (SP1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
pose proof HPRE as (_ & _ & _ & HGP0 & HTP0 & HAS0 & _). pose proof HAS0 as (_ & _ & As3 & As4 & As5 & As6 & _).
fold (gsp0 cx) in As4, As5. rewrite WS in As4.
assert (SPB : alloc_ceiling + 17104 <= gsp0 cx <= 2 ^ 47) by lia.
assert (Hsp32 : gsp1 cx mod 32 = 0) by (rewrite SP1; rewrite Zminus_mod, H32; reflexivity).
destruct (tp2_frm_xR cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ) as (HAR1 & Hfin & HF4 & HFc & HFapp & HFni).
rewrite HFa in HF4, HFc, HFapp, HFni.
pose proof HFapp as HFA. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFA.
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 1 fpos HAR1 Hfin) as (HFal & _ & HFpres & HFSpres).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *. rewrite HFa in HFal, HFpres, HFSpres.
pose proof HTM as (Hi & Hlq & Hrel & HGD & Hrly & Hout & Hdone & Hsrc1 & Hdrs & Hgs & Hperm).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HREL0 & _). pose proof HREL0 as (_ & _ & _ & _ & _ & _ & Rlen0 & _).
pose proof Hrly as (RS1 & _ & _ & _ & _ & _ & Rlen & RSG & (tail & _ & _ & Rtab) & Rok & _).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 RSG) as (HG16 & HG4096 & HGc & HGapp & HGpres & _).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in HGc, HGapp, HGpres.
assert (Hi16 : (i < 16)%nat) by lia.
set (G0 := gxG0 cx) in *.
set (idv := bv_unsigned (getr (gxregs cx) 10)) in *.
set (SA := G0 + AENT * Z.of_nat i) in *.
assert (Hshv : shadow_addr F = SB + F / 8) by (unfold shadow_addr, SB; reflexivity).
assert (HF8b : 0 <= F / 8 <= F) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
(* F is 32-aligned (alx_frames), so its shadow address is 4-aligned *)
assert (Hsh4 : (SB + F / 8) mod 4 = 0).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HFal, Z.add_0_r in D.
  assert (F / 8 = 4 * (F / 32)) by (rewrite D at 1; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by ring; apply Z.div_mul; lia).
  assert (SB mod 4 = 0) by reflexivity. pose proof (Z.div_mod SB 4 ltac:(lia)).
  replace (SB + F / 8) with ((SB / 4 + F / 32) * 4) by lia.
  apply Z_mod_mult. }
assert (HSAm : SA mod 8 = 0).
{ unfold SA, AENT. pose proof (Z.div_mod G0 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
  replace (G0 + 56 * Z.of_nat i) with ((2 * (G0 / 16) + 7 * Z.of_nat i) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8c.
assert (Hidr : 0 <= idv < 2 ^ 64)
by (unfold idv; pose proof (bv_unsigned_in_range 64 (getr (gxregs cx) 10)) as Rq; change (bv_modulus 64) with (2 ^ 64) in Rq; exact Rq).
pose proof (pa_obj_img 5 ltac:(lia)) as HO5.
pose proof (tp2_seat2 W1 regs1 m1 G0 SA idv (F + 32) (gsp1 cx) (shadow_addr F) (Z.of_nat i)) as HS.
specialize (HS ltac:(rewrite R23, HH42; reflexivity)
  ltac:(rewrite H9; unfold w64; apply unsigned_lit_small; lia) H21
  ltac:(rewrite R20; unfold w64; apply unsigned_lit_small; rewrite Hshv; unfold SB; lia)
  ltac:(rewrite Hshv; unfold SB; lia) ltac:(rewrite Hshv; exact Hsh4)
  R18 ltac:(lia) ltac:(unfold SA, AENT; lia)
  ltac:(lia) ltac:(unfold TP2_PHI; lia) HG16
  (proj1 HO5) (proj2 HO5)
  ltac:(rewrite SP1; lia) ltac:(rewrite SP1; lia) Hsp32
  Hidr ltac:(lia)
  ltac:(rewrite <- RGSRC; exact RS1) L48 L56 HF72 L88
  ltac:(intros o Ho; eapply ajgx_pres_xR; [exact HJ | rewrite WS; lia])
  ltac:(intros o Ho; exact (proj1 (HFSpres o ltac:(lia))))).
remember (Eimg (Ereg regs1 (tp2_extra2 G0 SA idv (F + 32)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (tp2_extra2 G0 SA idv (F + 32))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 G0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 idv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (F + 32))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
clear HE.
assert (U20 : bv_unsigned (ew E 20) = shadow_addr F)
by (rewrite (EEo 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; rewrite Hshv; unfold SB; lia).
assert (U9 : bv_unsigned (ew E 9) = gsp1 cx)
by (rewrite (EEo 9%nat 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS (SOff 21 0) [] E (mrestrict (w_H W1) m1)) by constructor.
unfold cfg_at. change (w64 (BASE + A_rig_pd)) with (Z_to_bv 64 (BASE + A_rig_pd)).
pose proof HJ as HJ0.
(* 0x82e6c .. 0x82e80: g_src reloaded (s3 = G0), s2 = SA; the null checks are decided; the overflow check stops *)
paj_run_tok_xR RUNG HS HJ SHOK tp2_Bspan0.
{ apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons.
  { intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite U9 in Ha.
    left. split; [left; rewrite SP1, WS in *; lia | lia]. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite U20 in Ha.
  left. split; [|lia]. right; right; right. exists 1, fpos. split; [left; reflexivity|].
  right. rewrite HFa. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. lia. }
rename ms into ms1a, mat into mat1a, HF into HF1a, HFr into HFr1a, HG into HG1a.
psrr_branch_tok RUNG BRR HS SHOK tp2_Bspan0.
(* 0x82e80 bltu s2,s3: the pointer-overflow trap (R5), refuted by SA = G0 + 56 i >= G0 *)
{ assert (HG0p : 0 <= G0) by lia. assert (Hd0 : 0 <= AENT * Z.of_nat i) by (unfold AENT; lia).
  assert (Hsum : G0 + AENT * Z.of_nat i < 2 ^ 64) by (unfold AENT; lia).
  rewrite (trap_ptr_wrap_atom E 33 32 G0 (AENT * Z.of_nat i) E33 E32 HG0p Hd0 Hsum) in Hc.
  discriminate Hc. }
(* 0x82e84 .. 0x82eb8: 80(sp) = i, F's shadow bytes 4 .. 9 = 0, the arguments, jal snprintf *)
paj_run_tok_xR RUNG HS HJ SHOK tp2_Bspan0.
{ apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons.
  { intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite U9 in Ha.
    left. split; [left; rewrite SP1, WS in *; lia | lia]. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite U20 in Ha.
  left. split; [|lia]. right; right; right. exists 1, fpos. split; [left; reflexivity|].
  right. rewrite HFa. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. lia. }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RGP1. cbn [ms_mem restrict] in RGP1.
pose proof (st_ok_region_nth _ _ _ 2 _ HS eq_refl) as RGS. cbn [ms_mem restrict] in RGS.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE2 : env_agree 32 (Ereg regs1 (tp2_extra2 G0 SA idv (F + 32))) Ex)
  by (repeat first [exact HAE | apply tp2_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 _ [2; 3; 4; 8; 9; 21]%bv HS HAE2 ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
tp2_nw HFr1a NW1a (fun a => (gsp1 cx + 80 <= a < gsp1 cx + 88) \/ (shadow_addr F + 4 <= a < shadow_addr F + 10)) U9 U20.
tp2_nw HFr1 NW1 (fun a => (gsp1 cx + 80 <= a < gsp1 cx + 88) \/ (shadow_addr F + 4 <= a < shadow_addr F + 10)) U9 U20.
pmkst HS.
prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12. prreg HS (13%bv : bv 5) N13.
prreg HS (14%bv : bv 5) N14. prreg HS (1%bv : bv 5) N1. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
prreg HS (20%bv : bv 5) N20.
assert (ZSv : forall o, 4 <= o < 10 -> val_mem SEGS (mrestrict (w_H W1) (ms_mem ms1)) (shadow_addr F + o) 1 0).
{ intros o Ho. rewrite <- U20.
  assert (Ho' : o = 4 \/ o = 5 \/ o = 6 \/ o = 7 \/ o = 8 \/ o = 9) by lia.
  destruct Ho' as [-> | [-> | [-> | [-> | [-> | ->]]]]];
  (eapply (field_of_region _ _ 20 _ _ 4 10 4 10 _ 1%N (SLit 0) 0 RGS); [reflexivity | cbn [In]; tauto | reflexivity | cbn; lia | cbn; lia]). }
assert (ZS : forall o, 4 <= o < 10 -> aview SEGS (w_H W1) (ms_mem ms1) (shadow_addr F + o) = Some 0)
by (intros o Ho; apply aview_of_val_mem1; [exact (ZSv o Ho) | lia]).
assert (V80 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms1)) (gsp1 cx + 80) 8 (Z.of_nat i)).
{ rewrite <- U9.
  eapply (field_of_region _ _ 9 _ _ 48 96 80 88 _ 8%N (SOff 22 0) (Z.of_nat i) RGP1);
  [reflexivity | cbn [In]; tauto | | cbn; lia | cbn; lia].
  cbn [sv_denot]. rewrite (EEo 22%nat 22%bv eq_refl), R22. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite Z.add_0_r. reflexivity. }
assert (ROM1 : rom_view SEGS W1 (ms_mem ms1)).
{ intros a Hin.
  assert (HI : 0x10000 <= a < 0x5fc000)
    by (destruct Hin as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
  rewrite (aview_kept_out _ _ (w_H W1) _ (ms_mem ms1) HFr1 a ltac:(lia) (NW1 a ltac:(rewrite Hshv; unfold SB; lia))).
  rewrite (aview_kept_out _ _ (w_H W1) m1 _ HFr1a a ltac:(lia) (NW1a a ltac:(rewrite Hshv; unfold SB; lia))).
  exact (HROM1 a Hin). }
(* snprintf's guard: the GOT word (an AR fact) and the canary's eight bytes, image bytes (HCANR) that aview reads
   through mbyte's seg_rom fallback in every state *)
assert (GRD : aguard_ok W1 (ms_mem ms1) FR_GOT_GUARD FR_GUARD).
{ split.
  - exact (HGOTG _ _ _ _ _ _ (tj_AR_xR B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
  - apply tp2_rdword_some. intros kk Hkk. apply tp2_aview_rom. apply HCANR. lia. }
eapply (LSC W1 (ms_regs ms1) (ms_mem ms1) (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) fpos
  ly1 S1 _ _ k1
  (Z_to_bv 64 (BASE + 2936)) F (gxID cx) idv (gPOST_xR B PST ARx MT RP RG R cx) HJ).
- unfold spZ. rewrite HK by (cbv; tauto). fold (spZ regs1). rewrite Hsp1, SP1. reflexivity.
- pose proof (Z.div_mod (gsp0 cx) 32 ltac:(lia)) as D. rewrite H32, Z.add_0_r in D. rewrite D.
  replace (32 * (gsp0 cx / 32)) with ((2 * (gsp0 cx / 32)) * 16) by ring. apply Z_mod_mult.
- rewrite HK by (cbv; tauto). rewrite Hgp1. exact HGP0.
- rewrite HK by (cbv; tauto). rewrite Htp1. exact HTP0.
- exact N1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite N10, E35. reflexivity.
- rewrite N11. reflexivity.
- change 258%nat with (A_OBJ 17) in N12.
  rewrite N12, (img_env_atomP E (A_OBJ 17) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). reflexivity.
- change 259%nat with (A_OBJ 18) in N13.
  rewrite N13, (img_env_atomP E (A_OBJ 18) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). reflexivity.
- rewrite N14, E34. reflexivity.
- unfold idv. rewrite H10. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity.
- exact RID.
- exact HFa.
- exact ZS.
- exact ROM1.
- exact GRD.
- intros regs2 mem2 md2 HJ2 HP2 HR2 HPRE2 HKP2 HPS2.
  pose proof (tp2_seat3 W1 regs2 mem2) as HS3.
  remember (Eimg (Ereg regs2 [])) as E3 eqn:HE3.
  assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; apply Eimg_env).
  assert (HAE3 : env_agree 32 (Ereg regs2 []) E3)
  by (rewrite HE3; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE3 : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E3 m = getr regs2 rr)
  by (intros m rr Hm; subst E3; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
  rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  clear HE3.
  assert (SHOK3 : sh_ok SEGS (SOff 21 0) [] E3 (mrestrict (w_H W1) mem2)) by constructor.
  (* 0x82ebc .. 0x82ec0: mv a0,s4; jal strlen *)
  paj_run_tok_xR RUNG HS3 HJ2 SHOK3 tp2_Bspan0. { apply awr_ok_x_nil. }
  rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs2 _ [2; 3; 4; 8; 9; 18; 19; 20; 21]%bv HS3 HAE3 ltac:(vm_compute; reflexivity))
    as HK3.
  cbn [ms_regs restrict] in HK3.
  pmkst HS3.
  prreg HS3 (10%bv : bv 5) Q10. prreg HS3 (1%bv : bv 5) Q1.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) mem2 a)
  by (intros a Ha; apply (aview_kept_out E3 _ (w_H W1) mem2 (ms_mem ms2) HFr2 a Ha); intros (r & Hin & _); destruct Hin).
  assert (U2s : spZ (ms_regs ms1) = gsp1 cx) by (unfold spZ; rewrite HK by (cbv; tauto); exact Hsp1).
  destruct (tp2_pre_nz cx) as (PNZ & PL1 & PL2).
  eapply (LSL W1 (ms_regs ms2) (ms_mem ms2) (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) fpos
    ly1 S1 _ _ k1
    (Z_to_bv 64 (BASE + 2944)) F (gpre cx) (gPOST_xR B PST ARx MT RP RG R cx) HJ2).
  + unfold spZ. rewrite (HK3 2%bv ltac:(cbv; tauto)).
    rewrite (tp2_pres _ _ 2 2%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)). fold (spZ (ms_regs ms1)).
    rewrite U2s, SP1. reflexivity.
  + pose proof (Z.div_mod (gsp0 cx) 32 ltac:(lia)) as D. rewrite H32, Z.add_0_r in D. rewrite D.
    replace (32 * (gsp0 cx / 32)) with ((2 * (gsp0 cx / 32)) * 16) by ring. apply Z_mod_mult.
  + rewrite (HK3 3%bv ltac:(cbv; tauto)). rewrite (tp2_pres _ _ 3 3%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)), HK
      by (cbv; tauto). rewrite Hgp1. exact HGP0.
  + rewrite (HK3 4%bv ltac:(cbv; tauto)). rewrite (tp2_pres _ _ 4 4%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)), HK
      by (cbv; tauto). rewrite Htp1. exact HTP0.
  + exact Q1.
  + apply ret_ok_codeptr_v; [lia | reflexivity].
  + rewrite Q10, (EE3 20%nat 20%bv eq_refl), (tp2_pres _ _ 20 20%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)), N20, E35.
    reflexivity.
  + exact HFa.
  + unfold arm in *. eapply ge_garr8_kept; [exact HPRE2|]. intros b Hb. apply K3. rewrite length_app in Hb. cbn [length] in Hb. lia.
  + exact PNZ.
  + lia.
  + intros o Ho. rewrite K3 by (rewrite Hshv; unfold SB; lia).
    rewrite HKP2; [exact (ZS o Ho) | rewrite Hshv; unfold SB; lia | rewrite Hshv; unfold SB; lia |
      rewrite Hshv; unfold SB; rewrite ?SP1 in *; lia].
  + intros a Hin.
    assert (HI : 0x10000 <= a < 0x5fc000)
      by (destruct Hin as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
    rewrite K3 by lia. rewrite HKP2; [exact (ROM1 a Hin) | lia | | rewrite ?SP1 in *; lia].
    intros Hb. apply (HFni a ltac:(lia)). destruct Hin as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr].
  + intros regs4 mem4 md4 HJ4 HP4 HR4 HKP4 HPS4.
    assert (GR : forall (r : bv 5) n, bv_unsigned r = n -> acallee_saved n -> In r [2; 3; 4; 8; 9; 18; 19; 20; 21]%bv ->
      getr regs4 r = getr (ms_regs ms1) r).
    { intros r n Hn Hcs Hin. rewrite (tp2_pres _ _ n r HP4 Hn Hcs), (HK3 r Hin). exact (tp2_pres _ _ n r HP2 Hn Hcs). }
    assert (U18r : bv_unsigned (getr regs4 18) = SA).
    { rewrite (GR 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), N18, E33.
      apply unsigned_lit_small. unfold SA, AENT. lia. }
    assert (U19r : bv_unsigned (getr regs4 19) = G0).
    { rewrite (GR 19%bv 19 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), N19, E32.
      apply unsigned_lit_small. lia. }
    assert (R21r : getr regs4 21 = w64 SHADOW_OFF).
    { rewrite (GR 21%bv 21 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), HK by (cbv; tauto). exact H21. }
    assert (U9r : bv_unsigned (getr regs4 9) = gsp1 cx).
    { rewrite (GR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), HK by (cbv; tauto). rewrite H9.
      unfold w64. apply unsigned_lit_small. lia. }
    (* GTOPM at strlen's return memory: the table's entry i, its nheld *)
    assert (KEEP14 : forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a ->
      aview SEGS (w_H W1) mem4 a = aview SEGS (w_H W1) m1 a).
    { intros a Ha Hnf.
      assert (Nsh : ~ (shadow_addr F + 4 <= a < shadow_addr F + 10)).
      { intros Hs. apply Hnf. exists 1, fpos. split; [left; reflexivity|]. right. rewrite HFa. unfold in_zr. cbn [fst snd].
        change (fs_frame_bytes 1 / 8) with 16. lia. }
      assert (Nbf : ~ (F + 32 <= a < F + 80)).
      { intros Hs. apply Hnf. exists 1, fpos. split; [left; reflexivity|]. left. rewrite HFa. unfold in_zr. cbn [fst snd].
        change (fs_frame_bytes 1) with 128. lia. }
      rewrite HKP4 by (rewrite ?SP1 in *; lia). rewrite K3 by lia. rewrite HKP2 by (rewrite ?SP1 in *; lia).
      assert (NPa : ~ ((gsp1 cx + 80 <= a < gsp1 cx + 88) \/ (shadow_addr F + 4 <= a < shadow_addr F + 10))) by lia.
      rewrite (aview_kept_out _ _ (w_H W1) _ (ms_mem ms1) HFr1 a ltac:(lia) (NW1 a NPa)).
      exact (aview_kept_out _ _ (w_H W1) m1 _ HFr1a a ltac:(lia) (NW1a a NPa)). }
    assert (PRES14 : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mem4 a).
    { intros a Hp. apply HPS4. eapply apresent_grows; [exact HG2|]. apply HPS2.
      eapply apresent_grows; [exact HG1|]. eapply apresent_grows; [exact HG1a | exact Hp]. }
    pose proof (LTK cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 mem4 fpos HB HAR1 Hfin KEEP14 PRES14 HTM)
      as HTM4.
    pose proof HTM4 as (_ & _ & _ & _ & Hrly4 & _).
    pose proof Hrly4 as (_ & _ & _ & _ & _ & _ & _ & _ & (tail4 & _ & _ & Rtab4) & Rok4 & _).
    assert (HLmq : length (map fst qd) = i) by (rewrite length_map; exact Hlq).
    assert (Hok4 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat)
      (map fst qd ++ e1 :: skipn (S i) (gxes cx))).
    { eapply Forall_impl; [|exact Rok4]. intros e (_ & _ & Q1' & Q2' & _). split; assumption. }
    assert (Hnth : nth i (map fst qd ++ e1 :: skipn (S i) (gxes cx)) relay_remove_b_c.no_entry = e1).
    { rewrite app_nth2 by lia. rewrite HLmq, Nat.sub_diag. reflexivity. }
    assert (HLtab : (i < length (map fst qd ++ e1 :: skipn (S i) (gxes cx)))%nat)
      by (rewrite length_app, HLmq; cbn [length]; lia).
    pose proof (tp2_table_entry _ _ _ _ i Rtab4 Hok4 HLtab) as HTE4. rewrite Hnth in HTE4.
    assert (HEOK4 : aentry_ok B ly1 S1 W1 mem4 e1).
    { rewrite Forall_forall in Rok4. apply Rok4. apply in_or_app. right. left. reflexivity. }
    pose proof HEOK4 as (_ & _ & Hp14 & _ & _ & _ & _ & _ & _ & _ & Hnh26 & _).
    assert (Hnh0 : 0 <= re_nheld e1) by (unfold re_nheld; lia).
    assert (Hnh31 : 0 <= re_nheld e1 < 2 ^ 31) by lia.
    pose proof (tp2_entry_nheld _ _ _ HTE4 Hp14 Hnh31) as VN4.
    assert (VN4' : val_mem SEGS (mrestrict (w_H W1) mem4) (SA + 48) 4 (re_nheld e1)) by exact VN4.
    pose proof (tj_AR_xR B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4.
    assert (HSA1 : 4096 <= SA) by (unfold SA, AENT; lia).
    assert (HSA2 : SA + 56 <= TP2_PHI) by (unfold SA, AENT, TP2_PHI; lia).
    assert (HG0b : 4096 <= G0 <= TP2_PHI) by (unfold TP2_PHI; lia).
    pose proof (tp2_seat4 W1 regs4 mem4 SA G0 (re_nheld e1) U18r U19r R21r HSA1 HSA2 HSAm HG0b HG16 Hnh31 VN4') as HS4.
    remember (Eimg (Ereg regs4 [Z_to_bv 64 (re_nheld e1)])) as E4 eqn:HE4.
    assert (HEI4 : img_env VAL A_LIM E4) by (subst E4; apply Eimg_env).
    assert (HAE4 : env_agree 32 (Ereg regs4 [Z_to_bv 64 (re_nheld e1)]) E4)
    by (rewrite HE4; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EE4 : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E4 m = getr regs4 rr)
    by (intros m rr Hm; subst E4; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
    rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
    assert (E4_32 : ew E4 32 = Z_to_bv 64 (re_nheld e1))
      by (subst E4; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 0)).
    clear HE4.
    assert (HBx4 : U E4 (SOff 21 0) = SHADOW_OFF)
      by (rewrite (U_atom E4 21 SHADOW_OFF ltac:(rewrite (EE4 21%nat 21%bv eq_refl); exact R21r)) by (unfold SHADOW_OFF; lia);
          reflexivity).
    assert (U18E4 : U E4 (SOff 18 0) = SA).
    { apply U_atom; [|unfold SA, AENT; lia]. rewrite (EE4 18%nat 18%bv eq_refl), <- U18r. symmetry. apply Z_to_bv_bv_unsigned. }
    assert (SHOK4 : sh_ok SEGS (SOff 21 0) tp2_SH4 E4 (mrestrict (w_H W1) mem4)).
    { constructor; [|constructor].
      eapply shent_ok_of_range.
      + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 _ W1 mem4 _ G0 ATABLE (SA + 48) 4 HAR4 RSG);
        [unfold SA, AENT; lia | rewrite RQT; unfold SA, AENT; lia].
      + exact HBx4.
      + exact U18E4.
      + lia.
      + lia.
      + intros x Hx. pose proof HGapp as HGA. revert Hx HGA Hi16. unfold SA, AENT. clear.
        unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros Hx HGA Hi16. lia. }
    pose proof HJ4 as HJ40.
    (* 0x82ec4 .. 0x82eec: the alignment and null traps of SA / G0 (decided), s8 = |prefix|, the shadow check of
       &nheld (fast path, the shadow entry), nheld; stops at blez *)
    paj_run_tok_xR RUNG HS4 HJ4 SHOK4 tp2_Bspan.
    { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]. }
    rename ms into ms5, mat into mat5, HF into HF5, HFr into HFr5, HG into HG5.
    rename w into w5a, w0 into w5b.
    assert (E5_32 : sv_denot (ewset (ewset E4 512 w5a) 513 w5b) (SOff 32 0) = Z_to_bv 64 (re_nheld e1))
    by (cbn [sv_denot]; rewrite !ew_ewset_other, E4_32, Z.add_0_r, Z_to_bv_bv_unsigned by lia; reflexivity).
    assert (U9E4 : bv_unsigned (ew E4 9) = gsp1 cx) by (rewrite (EE4 9%nat 9%bv eq_refl); exact U9r).
    (* 0x82eec blez a0: nheld <= 0 -> RGE i (0x830c4); nheld > 0 -> the inner loop's setup -> RGI i 0 r (0x82f08) *)
    psrr_branch_tok RUNG BRR HS4 SHOK4 tp2_Bspan.
    * lazymatch goal with Hb : branch_taken BC_GE _ _ = true |- _ => rename Hb into Hc4 end.
      rewrite (tp2_branch_ge (ewset (ewset E4 512 w5a) 513 w5b) (SLit 0) (SOff 32 0) 0 (re_nheld e1) eq_refl E5_32
        ltac:(lia) ltac:(lia)) in Hc4.
      assert (Hnh00 : re_nheld e1 <= 0) by (destruct (Z.ltb_spec 0 (re_nheld e1)); [discriminate Hc4 | lia]).
      paj_run_to_tok_xR RUNTOG HS4 HJ4 SHOK4 tp2_Bspan (AF_fr_relay_instance_gone + 0x424).
      { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]. }
      rename ms into ms6, mat into mat6, HF into HF6, HFr into HFr6, HG into HG6.
      tp2_nw HFr5 NW5 (fun _ : Z => False) U9E4 U9E4.
      tp2_nw HFr6 NW6 (fun _ : Z => False) U9E4 U9E4.
      assert (K56 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) mem4 a).
      { intros a Ha. rewrite (aview_kept_out _ _ (w_H W1) _ (ms_mem ms6) HFr6 a Ha (NW6 a (fun H => H))).
        exact (aview_kept_out _ _ (w_H W1) mem4 _ HFr5 a Ha (NW5 a (fun H => H))). }
      set (PF := fun a => (gsp1 cx - 3 * ESTACK <= a < gsp1 cx) \/ (gsp1 cx + 80 <= a < gsp1 cx + 88) \/
        (F + 32 <= a < F + 80) \/ (shadow_addr F + 4 <= a < shadow_addr F + 10)).
      assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ PF a -> aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Na. unfold PF in Na.
        assert (NPa : ~ ((gsp1 cx + 80 <= a < gsp1 cx + 88) \/ (shadow_addr F + 4 <= a < shadow_addr F + 10))) by tauto.
        rewrite K56 by lia. rewrite HKP4 by (rewrite ?SP1 in *; lia). rewrite K3 by lia. rewrite HKP2 by (rewrite ?SP1 in *; lia).
        rewrite (aview_kept_out _ _ (w_H W1) _ (ms_mem ms1) HFr1 a Ha (NW1 a NPa)).
        exact (aview_kept_out _ _ (w_H W1) m1 _ HFr1a a Ha (NW1a a NPa)). }
      assert (PRESF : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms6) a).
      { intros a Hp. eapply apresent_grows; [exact HG6|]. eapply apresent_grows; [exact HG5|]. apply PRES14. exact Hp. }
      assert (KEEPL : forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a ->
        aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Hnf. apply KEEPF; [lia|]. unfold PF. intros [X | [X | [X | X]]]; [lia | lia | |]; apply Hnf; exists 1, fpos;
        (split; [left; reflexivity|]); rewrite HFa; unfold in_zr; cbn [fst snd];
        [left; change (fs_frame_bytes 1) with 128; lia | right; change (fs_frame_bytes 1 / 8) with 16; lia]. }
      pose proof (LTK cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 (ms_mem ms6) fpos HB HAR1 Hfin KEEPL PRESF
        HTM) as HTM6.
      destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms6) _ PF HB HJ0 HROM1 HPK HFR HLK HLS HJ4) as [HGL6 HLS6].
      { intros a Ha. unfold PF in Ha. rewrite SP1 in *. lia. }
      { exact KEEPF. }
      { exact PRESF. }
      assert (V80F : val_mem SEGS (arm W1 (ms_mem ms6)) (gsp1 cx + 80) 8 (Z.of_nat i)).
      { unfold arm. eapply val_mem_kept; [|exact V80]. intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
        rewrite K56 by lia. rewrite HKP4 by (rewrite ?SP1 in *; lia). rewrite K3 by lia.
        apply HKP2; [lia | lia | rewrite ?SP1 in *; lia]. }
      lazymatch type of HS4 with st_ok_pi _ _ ?Ex _ _ => assert (HAE6 : env_agree 32 (Ereg regs4 [Z_to_bv 64 (re_nheld e1)]) Ex)
        by (repeat first [exact HAE4 | apply tp2_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs4 _ [2; 3; 4; 8; 9; 21]%bv HS4 HAE6 ltac:(vm_compute; reflexivity)) as HK6.
      cbn [ms_regs restrict] in HK6.
      pmkst HS4.
      destruct (LGO cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 spent ly1 S1 W1 (ms_mem ms6) HB HTM6 HBU Hnh00) as (qd' & HGO').
      apply KE. unfold RGE_xR.
      exists (ms_regs ms6), ly1, S1, (ms_mem ms6). eexists. exists k1, F, FL, qd', c1', O1, cap1, out1, spent.
      split; [unfold cfg_at, A_rig_step; reflexivity|].
      split.
      { unfold gregs_base, spZ. rewrite !HK6 by (cbv; tauto).
        rewrite (GR 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 21%bv 21 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite !HK by (cbv; tauto). exact HRB. }
      split; [exact V80F|]. split; [exact Hi|]. split; [exact HGL6|]. split; [exact HLS6 | exact HGO'].
    * lazymatch goal with Hb : branch_taken BC_GE _ _ = false |- _ => rename Hb into Hc4 end.
      rewrite (tp2_branch_ge (ewset (ewset E4 512 w5a) 513 w5b) (SLit 0) (SOff 32 0) 0 (re_nheld e1) eq_refl E5_32
        ltac:(lia) ltac:(lia)) in Hc4.
      assert (Hnh01 : 0 < re_nheld e1) by (destruct (Z.ltb_spec 0 (re_nheld e1)); [lia | discriminate Hc4]).
      paj_run_to_tok_xR RUNTOG HS4 HJ4 SHOK4 tp2_Bspan (AF_fr_relay_instance_gone + 0x268).
      { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]. }
      rename ms into ms6, mat into mat6, HF into HF6, HFr into HFr6, HG into HG6.
      tp2_nw HFr5 NW5 (fun _ : Z => False) U9E4 U9E4.
      tp2_nw HFr6 NW6 (fun _ : Z => False) U9E4 U9E4.
      assert (K56 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) mem4 a).
      { intros a Ha. rewrite (aview_kept_out _ _ (w_H W1) _ (ms_mem ms6) HFr6 a Ha (NW6 a (fun H => H))).
        exact (aview_kept_out _ _ (w_H W1) mem4 _ HFr5 a Ha (NW5 a (fun H => H))). }
      set (PF := fun a => (gsp1 cx - 3 * ESTACK <= a < gsp1 cx) \/ (gsp1 cx + 80 <= a < gsp1 cx + 88) \/
        (F + 32 <= a < F + 80) \/ (shadow_addr F + 4 <= a < shadow_addr F + 10)).
      assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ PF a -> aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Na. unfold PF in Na.
        assert (NPa : ~ ((gsp1 cx + 80 <= a < gsp1 cx + 88) \/ (shadow_addr F + 4 <= a < shadow_addr F + 10))) by tauto.
        rewrite K56 by lia. rewrite HKP4 by (rewrite ?SP1 in *; lia). rewrite K3 by lia. rewrite HKP2 by (rewrite ?SP1 in *; lia).
        rewrite (aview_kept_out _ _ (w_H W1) _ (ms_mem ms1) HFr1 a Ha (NW1 a NPa)).
        exact (aview_kept_out _ _ (w_H W1) m1 _ HFr1a a Ha (NW1a a NPa)). }
      assert (PRESF : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms6) a).
      { intros a Hp. eapply apresent_grows; [exact HG6|]. eapply apresent_grows; [exact HG5|]. apply PRES14. exact Hp. }
      assert (KEEPL : forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a ->
        aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Hnf. apply KEEPF; [lia|]. unfold PF. intros [X | [X | [X | X]]]; [lia | lia | |]; apply Hnf; exists 1, fpos;
        (split; [left; reflexivity|]); rewrite HFa; unfold in_zr; cbn [fst snd];
        [left; change (fs_frame_bytes 1) with 128; lia | right; change (fs_frame_bytes 1 / 8) with 16; lia]. }
      pose proof (LTK cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 (ms_mem ms6) fpos HB HAR1 Hfin KEEPL PRESF
        HTM) as HTM6.
      destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms6) _ PF HB HJ0 HROM1 HPK HFR HLK HLS HJ4) as [HGL6 HLS6].
      { intros a Ha. unfold PF in Ha. rewrite SP1 in *. lia. }
      { exact KEEPF. }
      { exact PRESF. }
      assert (V80F : val_mem SEGS (arm W1 (ms_mem ms6)) (gsp1 cx + 80) 8 (Z.of_nat i)).
      { unfold arm. eapply val_mem_kept; [|exact V80]. intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
        rewrite K56 by lia. rewrite HKP4 by (rewrite ?SP1 in *; lia). rewrite K3 by lia.
        apply HKP2; [lia | lia | rewrite ?SP1 in *; lia]. }
      lazymatch type of HS4 with st_ok_pi _ _ ?Ex _ _ => assert (HAE6 : env_agree 32 (Ereg regs4 [Z_to_bv 64 (re_nheld e1)]) Ex)
        by (repeat first [exact HAE4 | apply tp2_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs4 _ [2; 3; 4; 8; 9; 21]%bv HS4 HAE6 ltac:(vm_compute; reflexivity)) as HK6.
      cbn [ms_regs restrict] in HK6.
      prreg HS4 (19%bv : bv 5) F19. prreg HS4 (22%bv : bv 5) F22. prreg HS4 (20%bv : bv 5) F20.
      prreg HS4 (23%bv : bv 5) F23. prreg HS4 (27%bv : bv 5) F27. prreg HS4 (24%bv : bv 5) F24.
      prreg HS4 (25%bv : bv 5) F25. prreg HS4 (18%bv : bv 5) F18.
      pmkst HS4.
      assert (E18' : bv_unsigned (ew E4 18) = SA) by (rewrite (EE4 18%nat 18%bv eq_refl); exact U18r).
      assert (E21' : ew E4 21 = w64 SHADOW_OFF) by (rewrite (EE4 21%nat 21%bv eq_refl); exact R21r).
      assert (E10' : ew E4 10 = w64 (Z.of_nat (length (gpre cx)))) by (rewrite (EE4 10%nat 10%bv eq_refl); exact HR4).
      set (r := (Z.to_nat (re_nheld e1) - 1)%nat).
      assert (HNHr : re_nheld e1 = Z.of_nat (S r)) by (unfold r; lia).
      assert (HPREF : garr8 SEGS (arm W1 (ms_mem ms6)) (F + 32) (gpre cx ++ [0])).
      { unfold arm in *. eapply ge_garr8_kept; [exact HPRE2|]. intros b Hb. rewrite length_app in Hb. cbn [length] in Hb.
        rewrite K56 by lia. rewrite HKP4 by (rewrite ?SP1 in *; lia). apply K3. lia. }
      assert (HZSF : garr8 SEGS (arm W1 (ms_mem ms6)) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0]).
      { intros j Hj. cbn [length] in Hj. split; [|destruct j as [|[|[|[|[|[|j]]]]]]; cbn; lia].
        replace (nth j [0; 0; 0; 0; 0; 0] 0) with 0 by (destruct j as [|[|[|[|[|[|j]]]]]]; cbn; lia).
        replace (shadow_addr F + 4 + Z.of_nat j) with (shadow_addr F + (4 + Z.of_nat j)) by lia.
        unfold arm. eapply val_mem_kept; [|exact (ZSv (4 + Z.of_nat j) ltac:(lia))].
        intros kk Hkk. change (Z.of_nat 1) with 1 in Hkk.
        replace (shadow_addr F + (4 + Z.of_nat j) + kk) with (shadow_addr F + (4 + Z.of_nat j)) by lia.
        rewrite K56 by (rewrite Hshv; unfold SB; lia). rewrite HKP4 by (rewrite Hshv; unfold SB; rewrite ?SP1 in *; lia).
        rewrite K3 by (rewrite Hshv; unfold SB; lia).
        rewrite HKP2; [reflexivity | rewrite Hshv; unfold SB; lia | rewrite Hshv; unfold SB; lia |
          rewrite Hshv; unfold SB; rewrite ?SP1 in *; lia]. }
      destruct (LGI cx i r F qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 spent ly1 S1 W1 (ms_mem ms6) HB HTM6 HBU HNHr HPREF HZSF)
        as (ks & f & HGIN).
      apply (KI r). unfold RGI_xR.
      exists (ms_regs ms6), ly1, S1, (ms_mem ms6). eexists.
      exists k1, F, FL, qd, cB, OB, capB, e1, h1, ev, LB, c1', O1, cap1, ks, [], f, c1', O1, cap1, out1, spent.
      split; [unfold cfg_at, A_rig_inner; reflexivity|].
      split.
      { unfold gregs_base, spZ. rewrite !HK6 by (cbv; tauto).
        rewrite (GR 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 21%bv 21 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite !HK by (cbv; tauto). exact HRB. }
      split; [rewrite F19; reflexivity|].
      split; [rewrite F22; reflexivity|].
      split; [rewrite F20; reflexivity|].
      split; [rewrite F23, E18'; reflexivity|].
      split; [rewrite F27, E18'; apply (tp2_sh_den2 (SA + 48)); [exact E21' | unfold SA, AENT; lia]|].
      split; [rewrite F24; exact E10'|].
      split; [rewrite F25, E18'; reflexivity|].
      split; [rewrite F18, E18'; apply (tp2_sh_den2 (SA + 40)); [exact E21' | unfold SA, AENT; lia]|].
      split; [exact V80F|]. split; [exact HGL6|]. split; [exact HLS6 | exact HGIN].
Qed.
End wR.

End c.
End b.
End a.
