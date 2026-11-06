(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment TOP of the IMAGE-B walk of fuzz_reply's relay_instance_gone, its first
   half: RGO i (0x82e1c) -> g_src + 56 i and its traps (0x82e38-0x82e48), the shadow check and load of s->eof
   (0x82e4c-0x82e60), drain (s) when s->eof = 0 (0x82e68) -> the mid cut PD (0x82e6c, W_rig_top_defs.v).  The B run is
   fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record) 86226-86246; the shape of the image-A TOP.
   ROUTE (b), STEP 3 (the image-A twin: a Theorem Labs lane's RIG_x round of lib/A/W_rig_top.v top_p1, commit f4cd818e98d): over
   ARx at W_relay_instance_gone_cx.v's generic Section; the runners paj_run_x_x / paj_run_to_x_x, the shadow entries by
   range_addressable_of_block_hp0_x (HP0), drain's call by gx_callS_x at DRAIN_STK_x with dr_spec_x's room (dr_kr) and
   count premise (stmt_top_room), the count step after drain from stmt_dr_cnt (lib/B/W_rr_m_dcnt.v rmc_dr_cnt), and the
   entry alignment by q1_sa_align (W_drain_sa.v's lemma over alx_blocks).
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rig_top_defs W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
(* tr_netP: part I0 of lib/B/W_rr_m_dcnt.v, A's lib/A/W_tr_cnt.v names *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rr_m_dcnt.
(* route R: a Theorem Labs lane's dr_spec_xR / ge_spec_xR, SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



(* ---- byte-list helpers (lib/A/W_rr_scan.v rrs_*, renamed) ---- *)
Lemma q1_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma q1_skipn_cons : forall {X : Type} (l : list X) (d : X) (k : nat), (k < length l)%nat ->
skipn k l = nth k l d :: skipn (S k) l.
Proof.
intros X l d. induction l as [|x l IH]; intros k Hk; cbn [length] in Hk; [lia|].
destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.
Lemma q1_concat_split : forall {X : Type} (f : X -> list byte) (l : list X) (d : X) (i : nat),
  (i < length l)%nat ->
  concat (map f l) = concat (map f (firstn i l)) ++ f (nth i l d) ++ concat (map f (skipn (S i) l)).
Proof.
  intros X f l d. induction l as [|x l IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [firstn skipn nth map concat].
  - reflexivity.
  - rewrite (IH i ltac:(cbn [length] in Hi; lia)) at 1. cbn [map concat]. rewrite app_assoc. reflexivity.
Qed.
Lemma q1_eb_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
intros e P1 P2. unfold entry_bytes.
rewrite !length_app, !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8, P1, P2. reflexivity.
Qed.
Lemma q1_concat_len : forall l, Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) l ->
  length (concat (map entry_bytes l)) = (56 * length l)%nat.
Proof.
induction l as [|e l IH]; intros HF; [reflexivity|].
apply Forall_cons_iff in HF as [[P1 P2] HF]. cbn [map concat length]. rewrite length_app, (q1_eb_len e P1 P2), (IH HF). lia.
Qed.

(* ---- the symbolic state at RGO (0x82e1c): s1 = sp (atom 9), s5 = the shadow offset (21), s6 = i (22),
   s7 = g_src's register image (A_HI 42); g_src's cell (A_OBJ 5) holds G0 (atom 32); SA = G0 + 56 i is atom 33
   (the engine's form of a0 at 0x82e2c, aliased), the eof field at SA + 4 holds atom 34; its shadow is zero. ---- *)
Definition q1_PHI : Z := 140737479966720.
Definition q1_sr : list sv := sr_set sr_atoms 23%bv (SOff (A_HI 42) 0).
Definition q1_regions : smem :=
[ YP09.mkRegion (Some (A_OBJ 5)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 33%nat) 4 8 8 8 [YP09.mkChunk 4 (CVal 4 (SOff 34 0))] ].
Definition q1_SA : sv := SAlu ALU_ADD (SMd M_MUL (SOff 22 0) (SLit 56)) (SOff 32 0).
Definition q1_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 5); (21%nat, mkAF SB SB 0); (22%nat, mkAF 0 15 0); (32%nat, mkAF 4096 q1_PHI 4);
  (33%nat, mkAF 4096 q1_PHI 3); (34%nat, mkAF 0 1 0) ] [] [ (q1_SA, SOff 33 0) ].
Definition q1_ss : sstate := mkSS A_rig_outer q1_sr q1_regions None q1_facts.
Definition q1_SH : list shent := [ mkSHE 33 4 8 ].
Definition q1_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition q1_Bx : sv := SOff 21 0.
Definition q1_extra (G0 SA eof : Z) : list word := map (Z_to_bv 64) [G0; SA; eof].

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

(* the runners over the generic journal (image A's lib/A/W_rig_top.v Lets) *)
Let RUN := paj_run_x_x B PST ARx LAWS (G_RIG B RG) HGRIG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_RIG B RG) HGRIG 0 [].
Let BR := paj_branch (PI := PI).

Lemma q1_garr8_le : forall m a n z, garr8 SEGS m a (bzs (Z_to_le_bytes n z)) -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  val_mem SEGS m a n z.
Proof.
intros m a n z Hg Hz k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n z)))%nat) by (unfold bzs; rewrite length_map, length_Z_to_le_bytes; exact Hk).
destruct (Hg k Hl) as [Hv _]. specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
rewrite Hv. apply f_equal.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite map_nth, q1_nth_le_bytes by exact Hk. unfold bz.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Lemma q1_table_entry : forall M G l tail k,
garr8 SEGS M G (bzs (concat (map entry_bytes l) ++ tail)) ->
Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) l -> (k < length l)%nat ->
garr8 SEGS M (G + AENT * Z.of_nat k) (bzs (entry_bytes (nth k l relay_remove_b_c.no_entry))).
Proof.
intros M G l tail k Hg HF Hk.
rewrite (q1_concat_split entry_bytes l relay_remove_b_c.no_entry k Hk) in Hg.
unfold bzs in Hg |- *. rewrite !map_app in Hg.
apply garr8_app in Hg as [Hg _]. apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [Hg _].
assert (HF1 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (firstn k l)).
{ rewrite <- (firstn_skipn k l) in HF. apply Forall_app in HF as [HF1 _]. exact HF1. }
rewrite length_map, (q1_concat_len _ HF1), length_firstn in Hg.
replace (Nat.min k (length l)) with k in Hg by lia.
unfold AENT. replace (G + 56 * Z.of_nat k) with (G + Z.of_nat (56 * k)) by lia. exact Hg.
Qed.
Lemma q1_entry_eof : forall M SA e, garr8 SEGS M SA (bzs (entry_bytes e)) -> (re_eof e = 0 \/ re_eof e = 1) ->
val_mem SEGS M (SA + 4) 4 (re_eof e).
Proof.
intros M SA e Hg He. unfold entry_bytes, bzs in Hg. rewrite !map_app in Hg.
apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [Hg _].
rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4 in Hg.
apply q1_garr8_le; [|cbn; lia].
unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4 in Hg.
rewrite unsigned_lit_small in Hg by lia. exact Hg.
Qed.
Lemma q1_env_agree_ewset : forall R E n w, env_agree 32 R E -> (32 <= n)%nat -> env_agree 32 R (ewset E n w).
Proof. intros R E n w [HA HD] Hn. split; [|exact HD]. intros k Hk. rewrite ew_ewset_other by lia. apply HA. exact Hk. Qed.
Lemma q1_pres : forall regs regs' r (b : bv 5), aregs_preserved regs regs' -> bv_unsigned b = r -> acallee_saved r ->
getr regs' b = getr regs b.
Proof. intros regs regs' r b H <- Hr. rewrite <- (Z_to_bv_bv_unsigned _ b). apply H. exact Hr. Qed.

Lemma q1_regs_ok_same : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr He r'. pose proof (Hr r') as Hr'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hr0; [exact Hr'|].
unfold sr_get in *. destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr'|].
rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr'].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact He.
Qed.
Lemma q1_alias : forall (E : env) G0 (i : Z) SA, ew E 22 = Z_to_bv 64 i -> ew E 32 = Z_to_bv 64 G0 -> ew E 33 = Z_to_bv 64 SA ->
SA = G0 + 56 * i -> 0 <= i <= 15 -> 0 <= G0 <= 2 ^ 50 ->
sv_denot E q1_SA = sv_denot E (SOff 33 0).
Proof.
intros E G0 i SA H22 H32 H33 HSA Hi HG. unfold q1_SA.
cbn [sv_denot]. rewrite H22, H32, H33, !Z.add_0_r, !Z_to_bv_bv_unsigned.
unfold alu64, mul_div, alu.
apply bv_eq. rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small i), (Z.mod_small 56), (Z.mod_small G0) by lia.
rewrite (Z.mod_small (i * 56)) by lia. f_equal. lia.
Qed.

Lemma q1_seat : forall (W : world SEGS) regs mem G0 SA eof sp (i : Z),
getr regs 23 = Z_to_bv 64 (VAL (A_HI 42)) -> bv_unsigned (getr regs 9) = sp -> getr regs 21 = w64 SHADOW_OFF ->
getr regs 22 = Z_to_bv 64 i -> 0 <= i <= 15 ->
SA = G0 + 56 * i -> 4096 <= G0 -> G0 + 896 <= alloc_ceiling -> alloc_ceiling <= sp -> G0 mod 16 = 0 -> eof = 0 \/ eof = 1 ->
0x10000 <= VAL (A_OBJ 5) -> VAL (A_OBJ 5) + 8 <= 0x5fc000 -> 2 ^ 46 <= sp -> sp + 96 <= 2 ^ 47 -> sp mod 32 = 0 ->
(SA + 8 <= VAL (A_OBJ 5) \/ VAL (A_OBJ 5) + 8 <= SA + 4) ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 5)) 8 G0 ->
val_mem SEGS (mrestrict (w_H W) mem) (SA + 4) 4 eof ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (q1_extra G0 SA eof))) q1_ss
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_rig_outer)) mem (seg_rom SEGS))).
Proof.
intros W regs mem G0 SA eof sp i H23 H9 H21 H22 Hi HSA HG1 HG2 HGsp HG3 Heof Hs1 Hs2 Hsp1 Hsp2 Hsp3 Hdj VG VE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_val_range (A_OBJ 5)) as HV5r.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (q1_extra G0 SA eof))).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 G0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 eof) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO5 : ew E (A_OBJ 5) = Z_to_bv 64 (VAL (A_OBJ 5))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EH42 : ew E (A_HI 42) = Z_to_bv 64 (VAL (A_HI 42))) by (subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (U5 : base_val E (Some (A_OBJ 5)) = VAL (A_OBJ 5)) by (cbn [base_val]; rewrite EO5; apply unsigned_lit_small; lia).
assert (U33 : base_val E (Some 33%nat) = SA) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; unfold q1_PHI in *; lia).
assert (U21 : bv_unsigned (ew E 21) = SB) by (rewrite (EL 21%nat 21%bv eq_refl), H21; unfold w64, SHADOW_OFF, SB; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = i) by (rewrite (EL 22%nat 22%bv eq_refl), H22; apply unsigned_lit_small; lia).
unfold q1_ss. apply pa_entry_st_ok_full.
- unfold q1_sr. apply q1_regs_ok_same; [apply regs_ok_Eimg_Ereg|].
  cbn [sv_denot]. rewrite EH42, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. exact H23.
- vm_compute. reflexivity.
- unfold q1_regions. repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U5.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 5)) 0 8 _ G0);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold q1_PHI in *; zside | zside |].
    rewrite Z.add_0_r. exact VG.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U33.
    split; [unfold q1_PHI in *; lia|]. split; [unfold q1_PHI in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ SA 4 4 _ eof);
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VE].
- apply pairwise_disjoint_of_extents.
  unfold q1_regions, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U5, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold q1_PHI in *. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [q1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EL 9%nat 9%bv eq_refl), H9, U21, U22, E32, E33, E34, !unsigned_lit_small by (unfold q1_PHI in *; lia).
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (SA mod 8 = 0).
    { rewrite HSA. pose proof (Z.div_mod G0 16 ltac:(lia)) as D. rewrite HG3, Z.add_0_r in D.
      replace (G0 + 56 * i) with ((2 * (G0 / 16) + 7 * i) * 8) by lia. apply Z_mod_mult. }
    unfold SB, q1_PHI in *. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
  + cbn [q1_facts f_alias alias_ok]. split; [|exact I].
    apply (q1_alias E G0 i SA); [rewrite (EL 22%nat 22%bv eq_refl); exact H22 | exact E32 | exact E33 | exact HSA | exact Hi | unfold q1_PHI in *; lia].
Qed.



Ltac q1_nw_tac :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]);
  destruct Hin.

Lemma q1_mul56 : forall (w : word) (z : Z), w = Z_to_bv 64 z -> 0 <= z <= 15 ->
mul_div M_MUL w (Z_to_bv 64 56) = w64 (56 * z).
Proof.
intros w z -> Hb. unfold mul_div, w64. apply bv_eq. rewrite bv_mul_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small z), (Z.mod_small 56) by lia. f_equal. lia.
Qed.

(* the run's own fake frame (1, fpos): in S1's frames, below the ceiling, outside the image *)
Lemma q1_frm : forall cx fpos ly1 S1 Hp1 W1 m1 md1 k1,
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


Lemma q1_achain : forall cx ly1 W1 m1,
GBASE B ARx MT RP MMAX RG cx -> g_saved cx W1 m1 -> ly_top ly1 = ly_top (gxly cx) ->
(forall a, gsp0 cx <= a < 2 ^ 64 -> aview SEGS (w_H W1) m1 a = aview SEGS (w_H (gxW cx)) (gxmem cx) a) ->
exists ch1, achain ly1 (aview SEGS (w_H W1) m1) (gsp1 cx) (gsp0 cx) ch1.
Proof.
intros cx ly1 W1 m1 HB HSV Htop Hk.
pose proof HB as (HPRE & H32 & _).
pose proof HPRE as (_ & _ & Hra & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (_ & _ & Hs3 & Hs4 & _ & Hs6 & _ & Hs8 & Hs9).
assert (WS : RIG_STK_x = 17232) by reflexivity.
fold (gsp0 cx) in Hs4, Hs8, Hch.
destruct (Z_lt_le_dec (gsp0 cx) (ly_top (gxly cx) - 16)) as [Hlt | Hge].
- exists ((gsp0 cx, raZ (gxregs cx), s0Z (gxregs cx)) :: gxch cx).
  apply (achain_ly_top (gxly cx)); [exact Htop|].
  apply (achain_push (gxly cx) (aview SEGS (w_H (gxW cx)) (gxmem cx)) _ (gsp0 cx) (s0Z (gxregs cx)) (raZ (gxregs cx)) (gxch cx) (gsp1 cx) Hch).
  + lia.
  + exact Hk.
  + replace (gsp0 cx - 8) with (gsp1 cx + 120 + 8 * Z.of_nat 12) by (unfold gsp1, RIG_FRAME; lia).
    apply rdword_of_val_mem; [exact (HSV 12%nat ltac:(lia)) | unfold raZ; pose proof (bv_unsigned_in_range 64 (getr (gxregs cx) 1)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R].
  + replace (gsp0 cx - 16) with (gsp1 cx + 120 + 8 * Z.of_nat 11) by (unfold gsp1, RIG_FRAME; lia).
    apply rdword_of_val_mem; [exact (HSV 11%nat ltac:(lia)) | unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr (gxregs cx) 8)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R].
  + exact Hra.
  + rewrite WS in Hs4. lia.
  + pose proof (Z.div_mod (gsp0 cx) 32 ltac:(lia)) as D. rewrite H32, Z.add_0_r in D. rewrite D.
    replace (32 * (gsp0 cx / 32)) with ((4 * (gsp0 cx / 32)) * 8) by ring. apply Z_mod_mult.
  + exact Hlt.
  + unfold gsp1, RIG_FRAME. lia.
- exists []. left. split; [right; left; rewrite Htop; exact Hge | reflexivity].
Qed.

Lemma q1_sp : forall cx, GBASE B ARx MT RP MMAX RG cx -> alloc_ceiling + 17232 <= gsp0 cx <= 2 ^ 47.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : RIG_STK_x = 17232) by reflexivity. rewrite WS in Hslo. unfold gsp0. lia.
Qed.

(* W7's W_drain_sa.v dr_sa_align_slot over alx_blocks (image A's tp_sa_align): a slot of the 16-aligned table is
   8-aligned *)
Lemma q1_sa_align : forall ly S Hp W mem md (G : Z) (i : nat),
ARx ly S Hp W mem md -> In (G, ATABLE) (ablocks B ly S) -> (G + AENT * Z.of_nat i) mod 8 = 0.
Proof.
intros ly S Hp W mem md G i HAR Hin.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md G ATABLE HAR Hin) as (H16 & _).
apply Z.mod_divide in H16; [|lia]. destruct H16 as (k & ->).
unfold AENT. apply Z.mod_divide; [lia|]. exists (2 * k + 7 * Z.of_nat i). lia.
Qed.

(* the held array's clause of aentry_ok, in the form W_rr_m_dcnt.v's count lemma takes it (image A's td_hk) *)
Lemma td_hk : forall ly S W mem e, aentry_ok B ly S W mem e -> re_hp e = 0 \/ re_kh e <> 0.
Proof.
intros ly S W mem e HE. unfold aentry_ok in HE.
destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHP & _).
destruct HHP as [(E0 & _)|(E0 & _ & _ & K8 & _)]; [left; lia | right; lia].
Qed.

Lemma top_p1 :
stmt_gout_kept B ARx MT RP MMAX RG -> stmt_top_rep_closed B ARx MT RP MMAX RG -> stmt_top_budget B ARx MT RP MMAX RG ->
stmt_live_kept B PST ARx MT RP MMAX RG -> stmt_top_drain_pre B ARx MT RP MMAX RG -> stmt_dr_inv_of B RG ->
stmt_top_room B ARx MT RP MMAX RG -> stmt_dr_fp_in B ARx MT RP MMAX RG -> stmt_top_rep_open B PST ARx MT RP MMAX RG ->
stmt_dr_bytes B -> stmt_dr_cnt -> stmt_live_drain B PST ARx MT RP MMAX RG ->
forall cx i W1 c1,
GBASE B ARx MT RP MMAX RG cx -> RGO B PST ARx MT RP MMAX RG cx i W1 c1 ->
(forall W2 c2, PD B PST ARx MT RP MMAX RG cx i W2 c2 -> SRr SEGS W2 c2 (gPOST B PST ARx MT RP RG cx)) ->
SRr SEGS W1 c1 (gPOST B PST ARx MT RP RG cx).
Proof.
intros LGK LRC LBU LLK LDP LDI LRM LFP LRO LDB LDC LLD cx i W1 c1 HB HRGO KPD.
destruct HRGO as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & cB & OB & capB & outB & spent &
  -> & HRB & R20 & R22 & R23 & Hi & HGL & HLS & HGO).
pose proof HGL as (fpos & Hp1 & HJ & HROM1 & HPK & HFR & HLK).
pose proof HFR as (HFa & HFLa & HF120 & HFs8 & HFs16 & HFs112 & HFs72 & HSV).
pose proof HRB as (Hsp1 & Hgp1 & Htp1 & H8 & H9 & H21).
pose proof HB as (HPRE & H32 & HCNT & RGP & H10 & RID & _).
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (q1_sp cx HB) as SPB.
pose proof HPRE as (_ & _ & _ & HGP0 & HTP0 & _).
assert (SP1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
assert (WSK : RIG_STK_x = 17232) by reflexivity.
assert (DSK : DRAIN_STK_x = 17008) by reflexivity.
assert (Hsp32 : gsp1 cx mod 32 = 0) by (rewrite SP1; rewrite Zminus_mod, H32; reflexivity).
pose proof (tj_AR B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
pose proof HJ as HJ0.
destruct (q1_frm cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ) as (_ & Hfin & HF4 & HFc & HFapp & HFni).
pose proof HGO as (Hile & Hlq & Hrel & Hrly & Hout & Hdone & Hdrs & Hgs & Hperm & HBUD).
pose proof Hrly as (RS1 & _ & _ & _ & _ & _ & Rlen & RSG & (tail & _ & _ & Rtab) & Rok & _).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 RSG) as (HG16 & HG4096 & HGc & HGapp & HGpres & _).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in HGc, HGapp, HGpres.
set (G0 := gxG0 cx) in *.
set (SA := gSA cx i) in *.
assert (HSA : SA = G0 + 56 * Z.of_nat i) by (unfold SA, gSA, AENT; lia).
assert (HLmq : length (map fst qd) = i) by (rewrite length_map; exact Hlq).
assert (Hilt : (i < length (gxes cx))%nat) by exact Hi.
assert (Hnth : nth i (map fst qd ++ skipn i (gxes cx)) relay_remove_b_c.no_entry = gnth cx i).
{ rewrite app_nth2 by lia. rewrite HLmq, Nat.sub_diag.
  rewrite (q1_skipn_cons (gxes cx) relay_remove_b_c.no_entry i Hilt). reflexivity. }
assert (HLtab : (i < length (map fst qd ++ skipn i (gxes cx)))%nat)
  by (rewrite length_app, HLmq, length_skipn; lia).
assert (Hok : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat)
  (map fst qd ++ skipn i (gxes cx))).
{ eapply Forall_impl; [|exact Rok]. intros e (_ & _ & Q1 & Q2 & _). split; assumption. }
pose proof (q1_table_entry _ _ _ _ i Rtab Hok HLtab) as HTE. rewrite Hnth in HTE.
assert (HEOK : aentry_ok B ly1 S1 W1 m1 (gnth cx i)).
{ rewrite Forall_forall in Rok. rewrite <- Hnth. apply Rok. apply nth_In. exact HLtab. }
pose proof HEOK as (Heof01 & _).
pose proof (q1_entry_eof _ _ _ HTE Heof01) as VE. fold SA in VE.
assert (Hi16 : (length (gxes cx) <= 16)%nat) by (rewrite length_app, HLmq, length_skipn in Rlen; lia).
assert (Hib : 0 <= Z.of_nat i <= 15) by lia.
assert (SRCimg : forall a, rg_src RG <= a < rg_src RG + 8 -> in_img SEGS a).
{ intros a Ha. refine (proj1 (RGIMG a _)). unfold rg_rng. right; right; left. exact Ha. }
assert (Hdj : SA + 8 <= VAL (A_OBJ 5) \/ VAL (A_OBJ 5) + 8 <= SA + 4).
{ destruct (Z_le_gt_dec (SA + 8) (VAL (A_OBJ 5))) as [HA|HA]; [left; lia|].
  destruct (Z_le_gt_dec (VAL (A_OBJ 5) + 8) (SA + 4)) as [HC|HC]; [right; lia|]. exfalso.
  set (a := Z.max (SA + 4) (VAL (A_OBJ 5))).
  assert (Hin1 : G0 <= a < G0 + 896) by (unfold a; unfold SA, gSA, AENT in *; lia).
  assert (Hin2 : rg_src RG <= a < rg_src RG + 8) by (rewrite RGSRC; unfold a; lia).
  refine (blk_img_x _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 G0 ATABLE a HAR1 RSG _ (SRCimg a Hin2)). rewrite RQT; lia. }
assert (VG : val_mem SEGS (mrestrict (w_H W1) m1) (VAL (A_OBJ 5)) 8 G0) by (rewrite <- RGSRC; exact RS1).
pose proof (pa_obj_img 5 ltac:(lia)) as HO5.
assert (HS := q1_seat W1 regs1 m1 G0 SA (re_eof (gnth cx i)) (gsp1 cx) (Z.of_nat i)
  ltac:(rewrite R23, HH42; reflexivity)
  ltac:(rewrite H9; unfold w64; apply unsigned_lit_small; lia)
  H21 R22 Hib HSA ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heof01
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsp32 Hdj VG VE).
remember (Eimg (Ereg regs1 (q1_extra G0 SA (re_eof (gnth cx i))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (q1_extra G0 SA (re_eof (gnth cx i)))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 G0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_eof (gnth cx i))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
clear HE.
assert (UG : U E (SOff 32 0) = G0) by (apply (U_atom E 32 G0 E32); unfold SA, gSA, AENT in *; lia).
assert (USA : U E (SOff 33 0) = SA) by (apply (U_atom E 33 SA E33); unfold SA, gSA, AENT in *; lia).
assert (SHOK : sh_ok SEGS q1_Bx q1_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 _ W1 m1 _ G0 ATABLE (SA + 4) 4 HAR1 RSG);
    [unfold SA, gSA, AENT; lia | rewrite RQT; unfold SA, gSA, AENT; lia].
  + unfold q1_Bx. rewrite (U_atom E 21 SHADOW_OFF ltac:(rewrite (EEo 21%nat 21%bv eq_refl); exact H21)) by (unfold SHADOW_OFF; lia). reflexivity.
  + rewrite USA. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp.
    unfold SA, gSA, AENT in *. lia. }
unfold cfg_at. change (w64 (BASE + A_rig_outer)) with (Z_to_bv 64 (BASE + A_rig_outer)).
paj_run_tok_x RUN HS HJ SHOK q1_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
psrr_branch_tok RUN BR HS SHOK q1_Bspan.
- (* the pointer-overflow trap at 0x82e3c: SA < G0 is false *)
  rewrite (trap_ptr_bltu E (SOff 32 0) (SOff 33 0) G0 SA UG USA ltac:(unfold SA, gSA, AENT in *; lia)) in Hc.
  discriminate Hc.
- rename Hc into Hcb.
  paj_run_tok_x RUN HS HJ SHOK q1_Bspan.
  { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_nil. }
  rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
  psrr_branch_tok RUN BR HS SHOK q1_Bspan.
  + (* s->eof <> 0: no drain, straight to the mid cut 0x82e6c *)
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (EX34 : ew Ex 34 = Z_to_bv 64 (re_eof (gnth cx i)))
        by (rewrite ?ew_ewset_other by lia; exact E34) end.
    rewrite (trap_br_ne _ (SOff 34 0) (SLit 0)) in Hc.
    rewrite (U_atom _ 34 (re_eof (gnth cx i)) EX34 ltac:(lia)), (U_lit _ 0 ltac:(lia)) in Hc.
    assert (Heofnz : re_eof (gnth cx i) <> 0)
      by (intros HE0; rewrite HE0 in Hc; cbn in Hc; discriminate Hc).
    assert (Hopen : (re_eof (gnth cx i) =? 0) = false) by (apply Z.eqb_neq; exact Heofnz).
    paj_run_to_tok_x RUNTO HS HJ SHOK q1_Bspan A_rig_pd.
    { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_nil. }
    rename ms into ms3, mat into mat3, HF into HF3, HFr into HFr3, HG into HG3.
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
    { intros a Ha.
      rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms2) (ms_mem ms3) HFr3 a Ha ltac:(q1_nw_tac)).
      rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha ltac:(q1_nw_tac)).
      exact (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms1) HFr1 a Ha ltac:(q1_nw_tac)). }
    assert (PRES : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a).
    { intros a Hp. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | exact Hp]. }
    destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms3) (with_vm_backing (m_vm_lazy md1) mat3 md1)
      (fun _ : Z => False) HB HJ0 HROM1 HPK HFR HLK HLS HJ) as [HGL3 HLS3].
    { intros a []. }
    { intros a Ha _. exact (KEEP a Ha). }
    { exact PRES. }
    pose proof (LGK cx i qd cB OB capB outB spent ly1 S1 Hp1 W1 m1 md1 (ms_mem ms3) fpos HB HAR1 Hfin
      ltac:(intros a Ha _; apply KEEP; lia) PRES HGO) as HGO3.
    pose proof (LRC cx i qd cB OB capB outB spent ly1 S1 W1 (ms_mem ms3) HB Hi Heofnz HGO3) as HTM3.
    pose proof HTM3 as (_ & _ & _ & HDRD & _).
    pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      Hcl & Hbr & Hdd & Hei & Hmx & Hnolen & Hblk).
    assert (Hcap0 : 0 <= capB) by (destruct Hblk as [(Hc0 & _) | (Hc0 & _)]; lia).
    pose proof (LBU cx i qd cB OB capB spent ly1 S1 ly1 S1 (gnth cx i) (fst (ghj cx i)) 0 [] cB OB capB
      HB Hi Hlq Hrel Hcl Hbr Hdd Hcap0 Hmx HBUD HDRD
      ltac:(rewrite Hopen; intros HX; discriminate HX)
      ltac:(intros _; destruct HBUD as (_ & _ & _ & _ & _ & HRM0 & _);
            split; [exact (mo_le_refl MT MLAW S1) | split; [lia | split; [exact HRM0 | reflexivity]]])) as HBU3.
    rewrite Hopen, Z.add_0_r in HBU3.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (EX22 : ew Ex 22 = Z_to_bv 64 (Z.of_nat i))
        by (rewrite ?ew_ewset_other by lia; rewrite (EEo 22%nat 22%bv eq_refl); exact R22);
      assert (HAEx : env_agree 32 (Ereg regs1 (q1_extra G0 SA (re_eof (gnth cx i)))) Ex)
        by (repeat first [exact HAE | apply q1_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ [2; 3; 4; 8; 9; 20; 21; 22]%bv HS HAEx
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS (18%bv : bv 5) P18. prreg HS (23%bv : bv 5) P23.
    change 322%nat with (A_HI 42) in P23.
    rewrite (img_env_atomP E (A_HI 42) HEI ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), HH42 in P23.
    rewrite (q1_mul56 (ew E 22) (Z.of_nat i) ltac:(rewrite (EEo 22%nat 22%bv eq_refl); exact R22) ltac:(lia)) in P18.
    pmkst HS.
    apply KPD. unfold PD.
    exists (ms_regs ms3), ly1, S1, (ms_mem ms3), (with_vm_backing (m_vm_lazy md1) mat3 md1), k1, F, FL, qd,
      cB, OB, capB, (gnth cx i), (fst (ghj cx i)), 0, [], cB, OB, capB, outB, spent.
    split; [unfold cfg_at; reflexivity|].
    split.
    { unfold gregs_base, spZ. rewrite !HK by (cbv; tauto). exact HRB. }
    split; [rewrite P18; unfold AENT; reflexivity|].
    split; [rewrite HK by (cbv; tauto); exact R20|].
    split; [rewrite HK by (cbv; tauto); exact R22|].
    split; [exact P23|].
    split; [exact HGL3|]. split; [exact HLS3|]. split; [exact HTM3 | exact HBU3].
  + (* s->eof = 0: the drain call at 0x82e68 *)
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (EX34 : ew Ex 34 = Z_to_bv 64 (re_eof (gnth cx i)))
        by (rewrite ?ew_ewset_other by lia; exact E34) end.
    rewrite (trap_br_ne _ (SOff 34 0) (SLit 0)) in Hc.
    rewrite (U_atom _ 34 (re_eof (gnth cx i)) EX34 ltac:(lia)), (U_lit _ 0 ltac:(lia)) in Hc.
    assert (Heof0 : re_eof (gnth cx i) = 0)
      by (destruct (Z.eqb_spec (re_eof (gnth cx i)) 0) as [HE0|HE0]; [exact HE0 | cbn in Hc; discriminate Hc]).
    assert (Hopen : (re_eof (gnth cx i) =? 0) = true) by (apply Z.eqb_eq; exact Heof0).
    paj_run_to_tok_x RUNTO HS HJ SHOK q1_Bspan AF_fr_drain.
    { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_nil. }
    rename ms into ms3, mat into mat3, HF into HF3, HFr into HFr3, HG into HG3.
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
    { intros a Ha.
      rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms2) (ms_mem ms3) HFr3 a Ha ltac:(q1_nw_tac)).
      rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha ltac:(q1_nw_tac)).
      exact (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms1) HFr1 a Ha ltac:(q1_nw_tac)). }
    assert (PRES : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a).
    { intros a Hp. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | exact Hp]. }
    destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms3) (with_vm_backing (m_vm_lazy md1) mat3 md1)
      (fun _ : Z => False) HB HJ0 HROM1 HPK HFR HLK HLS HJ) as [HGL3 HLS3].
    { intros a []. }
    { intros a Ha _. exact (KEEP a Ha). }
    { exact PRES. }
    pose proof (LGK cx i qd cB OB capB outB spent ly1 S1 Hp1 W1 m1 md1 (ms_mem ms3) fpos HB HAR1 Hfin
      ltac:(intros a Ha _; apply KEEP; lia) PRES HGO) as HGO3.
    pose proof (tj_AR B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR3.
    assert (ROM3 : rom_view SEGS W1 (ms_mem ms3)).
    { intros a Ha.
      assert (HI : 0x10000 <= a < 0x5fc000)
        by (destruct Ha as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
      rewrite KEEP by lia. exact (HROM1 a Ha). }
    pose proof (LDP cx i qd cB OB capB outB spent ly1 S1 _ W1 (ms_mem ms3) _ HB Hi Heof0 HGO3 HAR3) as
      (HTIN & HSA1 & HSA2 & HG8 & HAWR & HEOK3 & HSRC3 & (rest0 & HPERM0)).
    pose proof (LDI ly1 S1 W1 (ms_mem ms3) (gnth cx i) (fst (ghj cx i)) (snd (ghj cx i))
      (Z.of_nat (length OB)) capB HEOK3 HSRC3) as (HINV & HREST).
    pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      Hcl & Hbr & Hdd & Hei & Hmx & Hnolen & Hblk).
    assert (Hcap0 : 0 <= capB) by (destruct Hblk as [(Hc0 & _) | (Hc0 & _)]; lia).
    pose proof (LRM cx i qd cB OB capB spent ly1 S1 HB Hi Hlq Heof0 Hrel Hcl Hbr Hdd Hcap0 Hmx HINV HREST HBUD)
      as (RM1 & RM2 & RM3 & RM4 & RM5).
    pose proof HSRC3 as (HJ4 & HSRCAT & HOTH & HFD & HSKIP & HU & HPS1 & HPS2 & HPS3).
    assert (SV3 : g_saved cx W1 (ms_mem ms3)).
    { intros j Hj. unfold arm in *. eapply val_mem_kept; [|exact (HSV j Hj)].
      intros kk Hkk. apply KEEP. unfold gsp1, RIG_FRAME in *. lia. }
    destruct (q1_achain cx ly1 W1 (ms_mem ms3) HB SV3 ltac:(eapply ajgx_ly_top_x; exact HJ0)
      ltac:(intros a Ha; eapply ajgx_keep_high_x; [exact HGRIG | exact HJ | lia | unfold gsp1, RIG_FRAME in *; try lia])) as (ch1 & HCH).
    prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ [2; 3; 4; 8; 9; 20; 21; 22]%bv HS
      ltac:(lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
        (repeat first [exact HAE | apply q1_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS (18%bv : bv 5) P18. prreg HS (23%bv : bv 5) P23.
    change 322%nat with (A_HI 42) in P23.
    rewrite (img_env_atomP E (A_HI 42) HEI ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), HH42 in P23.
    rewrite (q1_mul56 (ew E 22) (Z.of_nat i) ltac:(rewrite (EEo 22%nat 22%bv eq_refl); exact R22) ltac:(lia)) in P18.
    pmkst HS.
    assert (Q10' : getr (ms_regs ms3) 10 = w64 SA) by (rewrite Q10, E33; reflexivity).
    pose proof HGO3 as (_ & _ & _ & _ & Hout3 & _).
    destruct HGL3 as (fpos3 & Hp3 & HJ3 & ROM3' & HPK3 & HFR3 & HLK3).
    pose proof HFR3 as (HFa3 & HFLa3 & HF1203 & HFs83 & HFs163 & HFs1123 & HFs723 & HSV3).
    assert (HSPc : spZ (ms_regs ms3) = gsp0 cx + (-224))
      by (unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); fold (spZ regs1); rewrite Hsp1; unfold gsp1, RIG_FRAME; lia).
    assert (HS0c : s0Z (ms_regs ms3) = gsp0 cx)
      by (unfold s0Z; rewrite (HK 8%bv ltac:(cbv; tauto)), H8; unfold w64; apply unsigned_lit_small; lia).
    eapply SRr_bind.
    { eapply (gx_callS_x B PST ARx LAWS (G_RIG B RG) W1 (ms_regs ms3) (ms_mem ms3) _ RIG_STK_x (gsp0 cx) (gFP cx)
        (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos3)] ly1 S1 Hp3 _ k1
        DRAIN_STK_x (dr_fp SA (gnth cx i) (fst (ghj cx i)) capB outB) (-224) (Z_to_bv 64 (BASE + 2856)) ch1
        (fun ly2 S2 W2 regs2 mem2 md2 => exists Hpd k2,
           ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (spZ (ms_regs ms3))
             (dr_fp SA (gnth cx i) (fst (ghj cx i)) capB outB) ly1 S1 Hp3 W1 (ms_mem ms3)
             (with_vm_backing (m_vm_lazy md1) mat3 md1) [] ly2 S2 Hpd W2 mem2 md2 k2 /\
           apres_kept B W1 (ms_mem ms3) W2 mem2 /\
           DRK B MT RG cx i cB OB capB outB ly1 S1 W1 (ms_mem ms3) ly2 S2 W2 mem2 /\
           rp_RM RP S2 (dr_kr cx i cB (Z.of_nat (length OB)) capB))
        HGRIG HJ3).
      - exact HSPc.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - rewrite (HK 3%bv ltac:(cbv; tauto)). rewrite Hgp1. exact HGP0.
      - rewrite (HK 4%bv ltac:(cbv; tauto)). rewrite Htp1. exact HTP0.
      - exact Q1.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - rewrite unsigned_lit_small by lia. lia.
      - rewrite HS0c. replace (gsp0 cx + -224) with (gsp1 cx) by (unfold gsp1, RIG_FRAME; lia). exact HCH.
      - intros HPRE1. eapply SRr_mono.
        { (* dr_spec_x's entry alignment SA mod 8 = 0: a slot of the 16-aligned table (q1_sa_align, W7's W_drain_sa.v
             over alx_blocks); the room round: drain's room at dr_kr and its count premise (top_room) *)
          eapply (DRAIN W1 ly1 S1 Hp3 (ms_regs ms3) (ms_mem ms3) _ ch1 G0 SA (gnth cx i) (snd (ghj cx i))
            (fst (ghj cx i)) cB OB (gxmx cx) (Z.of_nat (length OB)) capB outB HPRE1 Q10' HTIN HSA1 HSA2
            (q1_sa_align ly1 S1 _ W1 (ms_mem ms3) _ (gxG0 cx) i HAR3 HTIN)
            HG8 HAWR HEOK3 HJ4 HSRCAT HOTH HFD HSKIP HU Hout3 ROM3 (ex_intro _ rest0 HPERM0)
            HPS1 HPS2 HPS3 RM1 RM2 RM3 _ RM4 RM5). }
        cbv beta. intros W2 c2 _ Hp.
        destruct Hp as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & e' & h' & out' & ev' & LB & rest &
          Hcfg & HJD & HPR & HAPK & HMO & HRMd & HPa & HPb & HRest).
        destruct HRest as (Dg8 & Dawr & Deok & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 &
          Dsrc & Dkept & D24 & D25 & D26 & D27 & D28 & D29 & D30 & D31 & D32 & D33 & D34 & D35 & D36 & D37 &
          D38 & D39 & D40 & Dout).
        assert (HDREL : dr_rel cB (gxmx cx) (Z.of_nat (length OB)) capB (gnth cx i) (fst (ghj cx i)) e' h' LB)
          by (unfold dr_rel; cbv zeta; repeat apply conj; assumption).
        assert (HDRK : DRK B MT RG cx i cB OB capB outB ly1 S1 W1 (ms_mem ms3) ly2 S2 W2 mem2).
        { unfold DRK. cbv zeta. exists e', h', out', ev', LB, rest.
          split; [exact HAPK|]. split; [exact HMO|]. split; [exact HPa|]. split; [exact HPb|].
          split; [exact Dg8|]. split; [exact Dawr|]. split; [exact Deok|]. split; [exact HDREL|].
          split; [exact Dsrc|]. split; [exact Dkept | exact Dout]. }
        exists ly2, S2, Hp2, regs2, mem2, md2, k2.
        split; [rewrite Hcfg, Q1; reflexivity|].
        split; [ltac:(eapply rig_lift_DR; exact HJD)|].
        split; [exact HPR|].
        exists Hp2, k2. split; [exact HJD|]. split; [exact HAPK|]. split; [exact HDRK | exact HRMd].
      - intros a Ha. exact (LFP cx i qd cB OB capB outB spent ly1 S1 _ W1 (ms_mem ms3) _ HB Hi Heof0 HGO3 HAR3 a Ha). }
    cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & -> & HJC & HJE & HPR2 &
      (Hpd & k2 & HJD & HAPK & HDRK & HRMd)).
    replace (spZ (ms_regs ms3)) with (gsp1 cx) in HJD by (rewrite HSPc; unfold gsp1, RIG_FRAME; lia).
    pose proof HDRK as (e' & h' & out' & ev' & LB & rest & HAPK' & HMO & HPa & HPb & Dg8 & Dawr & Deok &
      HDREL & Dsrc & Dkept & Dout).
    assert (Hfpb : forall a, inFP (dr_fp SA (gnth cx i) (fst (ghj cx i)) capB outB) a ->
      exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n).
    { intros a Ha.
      destruct (LFP cx i qd cB OB capB outB spent ly1 S1 _ W1 (ms_mem ms3) _ HB Hi Heof0 HGO3 HAR3 a Ha)
        as [(_ & Hb) | (b & n & Hin & _ & Hr)]; [exact Hb | exists b, n; split; [exact Hin | exact Hr]]. }
    pose proof (LDB ly1 S1 W1 (ms_mem ms3) ly2 S2 cB (gxmx cx) (Z.of_nat (length OB)) capB outB out'
      (gnth cx i) (fst (ghj cx i)) e' h' LB rest (gslot RG cx i) HEOK3 HSRCAT Hcap0 Hmx ltac:(lia)
      HINV HREST HPa HPb HDREL) as HBY.
    pose proof (LRO cx i qd cB OB capB outB spent ly1 S1 _ W1 (ms_mem ms3) _ (gsp1 cx)
      ly2 S2 Hpd W2 mem2 md2 k2 HB Hi Heof0 HGO3 HAR3 HJD ltac:(unfold gsp1, RIG_FRAME; lia) HDRK)
      as (e1 & h1 & ev1 & LB1 & out1 & HTM2).
    cbv zeta in HTM2.
    pose proof HTM2 as (_ & _ & _ & HDRD & _).
    (* the room round's counts: over drain's blocks the counts move by drain's net count (stmt_dr_cnt); the blocks
       drain does not own (rest) are the same on both sides *)
    assert (HCNT3 : forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly2 S2)) =
      Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
      tr_netP P (dr_tr cB (gxmx cx) (Z.of_nat (length OB)) capB (gnth cx i) (fst (ghj cx i)))).
    { intros P.
      pose proof (LDC cB (gxmx cx) (Z.of_nat (length OB)) capB outB out' (gnth cx i) (fst (ghj cx i)) e' h' LB P
        HINV HREST (td_hk _ _ _ _ _ HEOK3) (td_hk _ _ _ _ _ Deok) Hcap0 HDREL) as ECN. cbv zeta in ECN.
      rewrite (ReplyCnt.acnt_perm P _ _ HPb), (ReplyCnt.acnt_perm P _ _ HPa), !ReplyCnt.acnt_app.
      rewrite !ReplyCnt.acnt_app in ECN. lia. }
    pose proof (LBU cx i qd cB OB capB spent ly1 S1 ly2 S2 e1 h1 ev1 LB1
      (dr_ctl cB (fst (ghj cx i)) ev1)
      (if dr_live cB (fst (ghj cx i)) then OB ++ LB1 else OB)
      (if dr_live cB (fst (ghj cx i))
       then drain_b_c.ds_ocap (dr_fin cB (gxmx cx) (Z.of_nat (length OB)) capB (gnth cx i) (fst (ghj cx i)))
       else capB)
      HB Hi Hlq Hrel Hcl Hbr Hdd Hcap0 Hmx HBUD HDRD
      ltac:(intros _; split; [exact HINV | split; [exact HREST | split; [exact HMO |
        split; [exact HBY | split; [exact HRMd | exact HCNT3]]]]])
      ltac:(rewrite Hopen; intros HX; discriminate HX)) as HBU2.
    rewrite Hopen in HBU2.
    destruct (LLD cx fpos3 F FL ly1 S1 Hp3 W1 (ms_mem ms3) _ k1 SA (gnth cx i) (fst (ghj cx i)) capB outB
      ly2 S2 Hpd W2 mem2 md2 k2 Hp2 (k1 + kk) HB HJ3 ROM3' HPK3 HFR3 HLK3 HLS3 HJD Hfpb HAPK HJC) as [HGL2 HLS2].
    assert (GR : forall (r : bv 5) n, bv_unsigned r = n -> acallee_saved n -> getr regs2 r = getr (ms_regs ms3) r)
      by (intros r n Hn Hc'; exact (q1_pres _ _ n r HPR2 Hn Hc')).
    apply KPD. unfold PD.
    exists regs2, ly2, S2, mem2, md2, (k1 + kk)%Z, F, FL, qd, cB, OB, capB, e1, h1, ev1, LB1,
      (dr_ctl cB (fst (ghj cx i)) ev1),
      (if dr_live cB (fst (ghj cx i)) then OB ++ LB1 else OB),
      (if dr_live cB (fst (ghj cx i))
       then drain_b_c.ds_ocap (dr_fin cB (gxmx cx) (Z.of_nat (length OB)) capB (gnth cx i) (fst (ghj cx i)))
       else capB), out1,
      (spent + dr_cost MT cB (gxmx cx) (Z.of_nat (length OB)) capB (gnth cx i) (fst (ghj cx i))).
    split; [unfold cfg_at, A_rig_pd, AF_fr_relay_instance_gone; reflexivity|].
    split.
    { unfold gregs_base, spZ.
      rewrite (GR 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia)), (HK 2%bv ltac:(cbv; tauto)).
      rewrite (GR 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia)), (HK 3%bv ltac:(cbv; tauto)).
      rewrite (GR 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia)), (HK 4%bv ltac:(cbv; tauto)).
      rewrite (GR 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia)), (HK 8%bv ltac:(cbv; tauto)).
      rewrite (GR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia)), (HK 9%bv ltac:(cbv; tauto)).
      rewrite (GR 21%bv 21 eq_refl ltac:(unfold acallee_saved; lia)), (HK 21%bv ltac:(cbv; tauto)).
      exact HRB. }
    split; [rewrite (GR 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia)), P18; unfold AENT; reflexivity|].
    split; [rewrite (GR 20%bv 20 eq_refl ltac:(unfold acallee_saved; lia)), (HK 20%bv ltac:(cbv; tauto)); exact R20|].
    split; [rewrite (GR 22%bv 22 eq_refl ltac:(unfold acallee_saved; lia)), (HK 22%bv ltac:(cbv; tauto)); exact R22|].
    split; [rewrite (GR 23%bv 23 eq_refl ltac:(unfold acallee_saved; lia)); exact P23|].
    split; [exact HGL2|]. split; [exact HLS2|]. split; [exact HTM2 | exact HBU2].
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): TOP's first half at a world relation R.  Each X_xR is X above with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the cx file's carriers (GLIVE, RGO, RGI, RGE, gPOST)
   and W_rig_top_defs.v's journal statements -> their R twins, the runs and the branch -> their SRrG forms (paj_run_x_xG / paj_run_to_x_xG, paj_branch_xR), the binds -> SRrG_bind SEGS R R_trans, drain -> DRAIN_R : dr_spec_xR.  Every other token is X's.  The hypothesis list is
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
(* :384 q1_frm *)
Lemma q1_frm_xR : forall cx fpos ly1 S1 Hp1 W1 m1 md1 k1,
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
(* :460 top_p1 *)
Lemma top_p1_xR :
stmt_gout_kept B ARx MT RP MMAX RG -> stmt_top_rep_closed B ARx MT RP MMAX RG -> stmt_top_budget B ARx MT RP MMAX RG ->
stmt_live_kept_xR B PST ARx MT RP MMAX RG R -> stmt_top_drain_pre B ARx MT RP MMAX RG -> stmt_dr_inv_of B RG ->
stmt_top_room B ARx MT RP MMAX RG -> stmt_dr_fp_in B ARx MT RP MMAX RG -> stmt_top_rep_open_xR B PST ARx MT RP MMAX RG R ->
stmt_dr_bytes B -> stmt_dr_cnt -> stmt_live_drain_xR B PST ARx MT RP MMAX RG R ->
forall cx i W1 c1,
GBASE B ARx MT RP MMAX RG cx -> RGO_xR B PST ARx MT RP MMAX RG R cx i W1 c1 ->
(forall W2 c2, PD_xR B PST ARx MT RP MMAX RG R cx i W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR B PST ARx MT RP RG R cx)) ->
SRrG SEGS R W1 c1 (gPOST_xR B PST ARx MT RP RG R cx).
Proof.
intros LGK LRC LBU LLK LDP LDI LRM LFP LRO LDB LDC LLD cx i W1 c1 HB HRGO KPD.
destruct HRGO as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & cB & OB & capB & outB & spent &
  -> & HRB & R20 & R22 & R23 & Hi & HGL & HLS & HGO).
pose proof HGL as (fpos & Hp1 & HJ & HROM1 & HPK & HFR & HLK).
pose proof HFR as (HFa & HFLa & HF120 & HFs8 & HFs16 & HFs112 & HFs72 & HSV).
pose proof HRB as (Hsp1 & Hgp1 & Htp1 & H8 & H9 & H21).
pose proof HB as (HPRE & H32 & HCNT & RGP & H10 & RID & _).
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (q1_sp cx HB) as SPB.
pose proof HPRE as (_ & _ & _ & HGP0 & HTP0 & _).
assert (SP1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
assert (WSK : RIG_STK_x = 17232) by reflexivity.
assert (DSK : DRAIN_STK_x = 17008) by reflexivity.
assert (Hsp32 : gsp1 cx mod 32 = 0) by (rewrite SP1; rewrite Zminus_mod, H32; reflexivity).
pose proof (tj_AR_xR B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
pose proof HJ as HJ0.
destruct (q1_frm_xR cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ) as (_ & Hfin & HF4 & HFc & HFapp & HFni).
pose proof HGO as (Hile & Hlq & Hrel & Hrly & Hout & Hdone & Hdrs & Hgs & Hperm & HBUD).
pose proof Hrly as (RS1 & _ & _ & _ & _ & _ & Rlen & RSG & (tail & _ & _ & Rtab) & Rok & _).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 RSG) as (HG16 & HG4096 & HGc & HGapp & HGpres & _).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in HGc, HGapp, HGpres.
set (G0 := gxG0 cx) in *.
set (SA := gSA cx i) in *.
assert (HSA : SA = G0 + 56 * Z.of_nat i) by (unfold SA, gSA, AENT; lia).
assert (HLmq : length (map fst qd) = i) by (rewrite length_map; exact Hlq).
assert (Hilt : (i < length (gxes cx))%nat) by exact Hi.
assert (Hnth : nth i (map fst qd ++ skipn i (gxes cx)) relay_remove_b_c.no_entry = gnth cx i).
{ rewrite app_nth2 by lia. rewrite HLmq, Nat.sub_diag.
  rewrite (q1_skipn_cons (gxes cx) relay_remove_b_c.no_entry i Hilt). reflexivity. }
assert (HLtab : (i < length (map fst qd ++ skipn i (gxes cx)))%nat)
  by (rewrite length_app, HLmq, length_skipn; lia).
assert (Hok : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat)
  (map fst qd ++ skipn i (gxes cx))).
{ eapply Forall_impl; [|exact Rok]. intros e (_ & _ & Q1 & Q2 & _). split; assumption. }
pose proof (q1_table_entry _ _ _ _ i Rtab Hok HLtab) as HTE. rewrite Hnth in HTE.
assert (HEOK : aentry_ok B ly1 S1 W1 m1 (gnth cx i)).
{ rewrite Forall_forall in Rok. rewrite <- Hnth. apply Rok. apply nth_In. exact HLtab. }
pose proof HEOK as (Heof01 & _).
pose proof (q1_entry_eof _ _ _ HTE Heof01) as VE. fold SA in VE.
assert (Hi16 : (length (gxes cx) <= 16)%nat) by (rewrite length_app, HLmq, length_skipn in Rlen; lia).
assert (Hib : 0 <= Z.of_nat i <= 15) by lia.
assert (SRCimg : forall a, rg_src RG <= a < rg_src RG + 8 -> in_img SEGS a).
{ intros a Ha. refine (proj1 (RGIMG a _)). unfold rg_rng. right; right; left. exact Ha. }
assert (Hdj : SA + 8 <= VAL (A_OBJ 5) \/ VAL (A_OBJ 5) + 8 <= SA + 4).
{ destruct (Z_le_gt_dec (SA + 8) (VAL (A_OBJ 5))) as [HA|HA]; [left; lia|].
  destruct (Z_le_gt_dec (VAL (A_OBJ 5) + 8) (SA + 4)) as [HC|HC]; [right; lia|]. exfalso.
  set (a := Z.max (SA + 4) (VAL (A_OBJ 5))).
  assert (Hin1 : G0 <= a < G0 + 896) by (unfold a; unfold SA, gSA, AENT in *; lia).
  assert (Hin2 : rg_src RG <= a < rg_src RG + 8) by (rewrite RGSRC; unfold a; lia).
  refine (blk_img_x _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 G0 ATABLE a HAR1 RSG _ (SRCimg a Hin2)). rewrite RQT; lia. }
assert (VG : val_mem SEGS (mrestrict (w_H W1) m1) (VAL (A_OBJ 5)) 8 G0) by (rewrite <- RGSRC; exact RS1).
pose proof (pa_obj_img 5 ltac:(lia)) as HO5.
assert (HS := q1_seat W1 regs1 m1 G0 SA (re_eof (gnth cx i)) (gsp1 cx) (Z.of_nat i)
  ltac:(rewrite R23, HH42; reflexivity)
  ltac:(rewrite H9; unfold w64; apply unsigned_lit_small; lia)
  H21 R22 Hib HSA ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heof01
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsp32 Hdj VG VE).
remember (Eimg (Ereg regs1 (q1_extra G0 SA (re_eof (gnth cx i))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (q1_extra G0 SA (re_eof (gnth cx i)))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 G0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_eof (gnth cx i))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
clear HE.
assert (UG : U E (SOff 32 0) = G0) by (apply (U_atom E 32 G0 E32); unfold SA, gSA, AENT in *; lia).
assert (USA : U E (SOff 33 0) = SA) by (apply (U_atom E 33 SA E33); unfold SA, gSA, AENT in *; lia).
assert (SHOK : sh_ok SEGS q1_Bx q1_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 _ W1 m1 _ G0 ATABLE (SA + 4) 4 HAR1 RSG);
    [unfold SA, gSA, AENT; lia | rewrite RQT; unfold SA, gSA, AENT; lia].
  + unfold q1_Bx. rewrite (U_atom E 21 SHADOW_OFF ltac:(rewrite (EEo 21%nat 21%bv eq_refl); exact H21)) by (unfold SHADOW_OFF; lia). reflexivity.
  + rewrite USA. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp.
    unfold SA, gSA, AENT in *. lia. }
unfold cfg_at. change (w64 (BASE + A_rig_outer)) with (Z_to_bv 64 (BASE + A_rig_outer)).
paj_run_tok_xR RUNG HS HJ SHOK q1_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_nil. }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
psrr_branch_tok RUNG BRR HS SHOK q1_Bspan.
- (* the pointer-overflow trap at 0x82e3c: SA < G0 is false *)
  rewrite (trap_ptr_bltu E (SOff 32 0) (SOff 33 0) G0 SA UG USA ltac:(unfold SA, gSA, AENT in *; lia)) in Hc.
  discriminate Hc.
- rename Hc into Hcb.
  paj_run_tok_xR RUNG HS HJ SHOK q1_Bspan.
  { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_nil. }
  rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
  psrr_branch_tok RUNG BRR HS SHOK q1_Bspan.
  + (* s->eof <> 0: no drain, straight to the mid cut 0x82e6c *)
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (EX34 : ew Ex 34 = Z_to_bv 64 (re_eof (gnth cx i)))
        by (rewrite ?ew_ewset_other by lia; exact E34) end.
    rewrite (trap_br_ne _ (SOff 34 0) (SLit 0)) in Hc.
    rewrite (U_atom _ 34 (re_eof (gnth cx i)) EX34 ltac:(lia)), (U_lit _ 0 ltac:(lia)) in Hc.
    assert (Heofnz : re_eof (gnth cx i) <> 0)
      by (intros HE0; rewrite HE0 in Hc; cbn in Hc; discriminate Hc).
    assert (Hopen : (re_eof (gnth cx i) =? 0) = false) by (apply Z.eqb_neq; exact Heofnz).
    paj_run_to_tok_xR RUNTOG HS HJ SHOK q1_Bspan A_rig_pd.
    { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_nil. }
    rename ms into ms3, mat into mat3, HF into HF3, HFr into HFr3, HG into HG3.
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
    { intros a Ha.
      rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms2) (ms_mem ms3) HFr3 a Ha ltac:(q1_nw_tac)).
      rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha ltac:(q1_nw_tac)).
      exact (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms1) HFr1 a Ha ltac:(q1_nw_tac)). }
    assert (PRES : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a).
    { intros a Hp. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | exact Hp]. }
    destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms3) (with_vm_backing (m_vm_lazy md1) mat3 md1)
      (fun _ : Z => False) HB HJ0 HROM1 HPK HFR HLK HLS HJ) as [HGL3 HLS3].
    { intros a []. }
    { intros a Ha _. exact (KEEP a Ha). }
    { exact PRES. }
    pose proof (LGK cx i qd cB OB capB outB spent ly1 S1 Hp1 W1 m1 md1 (ms_mem ms3) fpos HB HAR1 Hfin
      ltac:(intros a Ha _; apply KEEP; lia) PRES HGO) as HGO3.
    pose proof (LRC cx i qd cB OB capB outB spent ly1 S1 W1 (ms_mem ms3) HB Hi Heofnz HGO3) as HTM3.
    pose proof HTM3 as (_ & _ & _ & HDRD & _).
    pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      Hcl & Hbr & Hdd & Hei & Hmx & Hnolen & Hblk).
    assert (Hcap0 : 0 <= capB) by (destruct Hblk as [(Hc0 & _) | (Hc0 & _)]; lia).
    pose proof (LBU cx i qd cB OB capB spent ly1 S1 ly1 S1 (gnth cx i) (fst (ghj cx i)) 0 [] cB OB capB
      HB Hi Hlq Hrel Hcl Hbr Hdd Hcap0 Hmx HBUD HDRD
      ltac:(rewrite Hopen; intros HX; discriminate HX)
      ltac:(intros _; destruct HBUD as (_ & _ & _ & _ & _ & HRM0 & _);
            split; [exact (mo_le_refl MT MLAW S1) | split; [lia | split; [exact HRM0 | reflexivity]]])) as HBU3.
    rewrite Hopen, Z.add_0_r in HBU3.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (EX22 : ew Ex 22 = Z_to_bv 64 (Z.of_nat i))
        by (rewrite ?ew_ewset_other by lia; rewrite (EEo 22%nat 22%bv eq_refl); exact R22);
      assert (HAEx : env_agree 32 (Ereg regs1 (q1_extra G0 SA (re_eof (gnth cx i)))) Ex)
        by (repeat first [exact HAE | apply q1_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ [2; 3; 4; 8; 9; 20; 21; 22]%bv HS HAEx
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS (18%bv : bv 5) P18. prreg HS (23%bv : bv 5) P23.
    change 322%nat with (A_HI 42) in P23.
    rewrite (img_env_atomP E (A_HI 42) HEI ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), HH42 in P23.
    rewrite (q1_mul56 (ew E 22) (Z.of_nat i) ltac:(rewrite (EEo 22%nat 22%bv eq_refl); exact R22) ltac:(lia)) in P18.
    pmkst HS.
    apply KPD. unfold PD_xR.
    exists (ms_regs ms3), ly1, S1, (ms_mem ms3), (with_vm_backing (m_vm_lazy md1) mat3 md1), k1, F, FL, qd,
      cB, OB, capB, (gnth cx i), (fst (ghj cx i)), 0, [], cB, OB, capB, outB, spent.
    split; [unfold cfg_at; reflexivity|].
    split.
    { unfold gregs_base, spZ. rewrite !HK by (cbv; tauto). exact HRB. }
    split; [rewrite P18; unfold AENT; reflexivity|].
    split; [rewrite HK by (cbv; tauto); exact R20|].
    split; [rewrite HK by (cbv; tauto); exact R22|].
    split; [exact P23|].
    split; [exact HGL3|]. split; [exact HLS3|]. split; [exact HTM3 | exact HBU3].
  + (* s->eof = 0: the drain call at 0x82e68 *)
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (EX34 : ew Ex 34 = Z_to_bv 64 (re_eof (gnth cx i)))
        by (rewrite ?ew_ewset_other by lia; exact E34) end.
    rewrite (trap_br_ne _ (SOff 34 0) (SLit 0)) in Hc.
    rewrite (U_atom _ 34 (re_eof (gnth cx i)) EX34 ltac:(lia)), (U_lit _ 0 ltac:(lia)) in Hc.
    assert (Heof0 : re_eof (gnth cx i) = 0)
      by (destruct (Z.eqb_spec (re_eof (gnth cx i)) 0) as [HE0|HE0]; [exact HE0 | cbn in Hc; discriminate Hc]).
    assert (Hopen : (re_eof (gnth cx i) =? 0) = true) by (apply Z.eqb_eq; exact Heof0).
    paj_run_to_tok_xR RUNTOG HS HJ SHOK q1_Bspan AF_fr_drain.
    { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_nil. }
    rename ms into ms3, mat into mat3, HF into HF3, HFr into HFr3, HG into HG3.
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
    { intros a Ha.
      rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms2) (ms_mem ms3) HFr3 a Ha ltac:(q1_nw_tac)).
      rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha ltac:(q1_nw_tac)).
      exact (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms1) HFr1 a Ha ltac:(q1_nw_tac)). }
    assert (PRES : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a).
    { intros a Hp. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | exact Hp]. }
    destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms3) (with_vm_backing (m_vm_lazy md1) mat3 md1)
      (fun _ : Z => False) HB HJ0 HROM1 HPK HFR HLK HLS HJ) as [HGL3 HLS3].
    { intros a []. }
    { intros a Ha _. exact (KEEP a Ha). }
    { exact PRES. }
    pose proof (LGK cx i qd cB OB capB outB spent ly1 S1 Hp1 W1 m1 md1 (ms_mem ms3) fpos HB HAR1 Hfin
      ltac:(intros a Ha _; apply KEEP; lia) PRES HGO) as HGO3.
    pose proof (tj_AR_xR B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR3.
    assert (ROM3 : rom_view SEGS W1 (ms_mem ms3)).
    { intros a Ha.
      assert (HI : 0x10000 <= a < 0x5fc000)
        by (destruct Ha as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
      rewrite KEEP by lia. exact (HROM1 a Ha). }
    pose proof (LDP cx i qd cB OB capB outB spent ly1 S1 _ W1 (ms_mem ms3) _ HB Hi Heof0 HGO3 HAR3) as
      (HTIN & HSA1 & HSA2 & HG8 & HAWR & HEOK3 & HSRC3 & (rest0 & HPERM0)).
    pose proof (LDI ly1 S1 W1 (ms_mem ms3) (gnth cx i) (fst (ghj cx i)) (snd (ghj cx i))
      (Z.of_nat (length OB)) capB HEOK3 HSRC3) as (HINV & HREST).
    pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      Hcl & Hbr & Hdd & Hei & Hmx & Hnolen & Hblk).
    assert (Hcap0 : 0 <= capB) by (destruct Hblk as [(Hc0 & _) | (Hc0 & _)]; lia).
    pose proof (LRM cx i qd cB OB capB spent ly1 S1 HB Hi Hlq Heof0 Hrel Hcl Hbr Hdd Hcap0 Hmx HINV HREST HBUD)
      as (RM1 & RM2 & RM3 & RM4 & RM5).
    pose proof HSRC3 as (HJ4 & HSRCAT & HOTH & HFD & HSKIP & HU & HPS1 & HPS2 & HPS3).
    assert (SV3 : g_saved cx W1 (ms_mem ms3)).
    { intros j Hj. unfold arm in *. eapply val_mem_kept; [|exact (HSV j Hj)].
      intros kk Hkk. apply KEEP. unfold gsp1, RIG_FRAME in *. lia. }
    destruct (q1_achain cx ly1 W1 (ms_mem ms3) HB SV3 ltac:(eapply ajgx_ly_top_xR; exact HJ0)
      ltac:(intros a Ha; eapply ajgx_keep_high_xR; [exact HGRIG | exact HJ | lia | unfold gsp1, RIG_FRAME in *; try lia])) as (ch1 & HCH).
    prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ [2; 3; 4; 8; 9; 20; 21; 22]%bv HS
      ltac:(lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
        (repeat first [exact HAE | apply q1_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS (18%bv : bv 5) P18. prreg HS (23%bv : bv 5) P23.
    change 322%nat with (A_HI 42) in P23.
    rewrite (img_env_atomP E (A_HI 42) HEI ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), HH42 in P23.
    rewrite (q1_mul56 (ew E 22) (Z.of_nat i) ltac:(rewrite (EEo 22%nat 22%bv eq_refl); exact R22) ltac:(lia)) in P18.
    pmkst HS.
    assert (Q10' : getr (ms_regs ms3) 10 = w64 SA) by (rewrite Q10, E33; reflexivity).
    pose proof HGO3 as (_ & _ & _ & _ & Hout3 & _).
    destruct HGL3 as (fpos3 & Hp3 & HJ3 & ROM3' & HPK3 & HFR3 & HLK3).
    pose proof HFR3 as (HFa3 & HFLa3 & HF1203 & HFs83 & HFs163 & HFs1123 & HFs723 & HSV3).
    assert (HSPc : spZ (ms_regs ms3) = gsp0 cx + (-224))
      by (unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); fold (spZ regs1); rewrite Hsp1; unfold gsp1, RIG_FRAME; lia).
    assert (HS0c : s0Z (ms_regs ms3) = gsp0 cx)
      by (unfold s0Z; rewrite (HK 8%bv ltac:(cbv; tauto)), H8; unfold w64; apply unsigned_lit_small; lia).
    eapply (SRrG_bind SEGS R R_trans).
    { eapply (gx_callS_xR B PST ARx LAWS R R_trans (G_RIG B RG) W1 (ms_regs ms3) (ms_mem ms3) _ RIG_STK_x (gsp0 cx) (gFP cx)
        (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos3)] ly1 S1 Hp3 _ k1
        DRAIN_STK_x (dr_fp SA (gnth cx i) (fst (ghj cx i)) capB outB) (-224) (Z_to_bv 64 (BASE + 2856)) ch1
        (fun ly2 S2 W2 regs2 mem2 md2 => exists Hpd k2,
           ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (spZ (ms_regs ms3))
             (dr_fp SA (gnth cx i) (fst (ghj cx i)) capB outB) ly1 S1 Hp3 W1 (ms_mem ms3)
             (with_vm_backing (m_vm_lazy md1) mat3 md1) [] ly2 S2 Hpd W2 mem2 md2 k2 /\
           apres_kept B W1 (ms_mem ms3) W2 mem2 /\
           DRK B MT RG cx i cB OB capB outB ly1 S1 W1 (ms_mem ms3) ly2 S2 W2 mem2 /\
           rp_RM RP S2 (dr_kr cx i cB (Z.of_nat (length OB)) capB))
        HGRIG HJ3).
      - exact HSPc.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - rewrite (HK 3%bv ltac:(cbv; tauto)). rewrite Hgp1. exact HGP0.
      - rewrite (HK 4%bv ltac:(cbv; tauto)). rewrite Htp1. exact HTP0.
      - exact Q1.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - rewrite unsigned_lit_small by lia. lia.
      - rewrite HS0c. replace (gsp0 cx + -224) with (gsp1 cx) by (unfold gsp1, RIG_FRAME; lia). exact HCH.
      - intros HPRE1. eapply SRrG_mono.
        { (* dr_spec_x's entry alignment SA mod 8 = 0: a slot of the 16-aligned table (q1_sa_align, W7's W_drain_sa.v
             over alx_blocks); the room round: drain's room at dr_kr and its count premise (top_room) *)
          eapply (DRAIN_R W1 ly1 S1 Hp3 (ms_regs ms3) (ms_mem ms3) _ ch1 G0 SA (gnth cx i) (snd (ghj cx i))
            (fst (ghj cx i)) cB OB (gxmx cx) (Z.of_nat (length OB)) capB outB HPRE1 Q10' HTIN HSA1 HSA2
            (q1_sa_align ly1 S1 _ W1 (ms_mem ms3) _ (gxG0 cx) i HAR3 HTIN)
            HG8 HAWR HEOK3 HJ4 HSRCAT HOTH HFD HSKIP HU Hout3 ROM3 (ex_intro _ rest0 HPERM0)
            HPS1 HPS2 HPS3 RM1 RM2 RM3 _ RM4 RM5). }
        cbv beta. intros W2 c2 _ Hp.
        destruct Hp as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & e' & h' & out' & ev' & LB & rest &
          Hcfg & HJD & HPR & HAPK & HMO & HRMd & HPa & HPb & HRest).
        destruct HRest as (Dg8 & Dawr & Deok & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 &
          Dsrc & Dkept & D24 & D25 & D26 & D27 & D28 & D29 & D30 & D31 & D32 & D33 & D34 & D35 & D36 & D37 &
          D38 & D39 & D40 & Dout).
        assert (HDREL : dr_rel cB (gxmx cx) (Z.of_nat (length OB)) capB (gnth cx i) (fst (ghj cx i)) e' h' LB)
          by (unfold dr_rel; cbv zeta; repeat apply conj; assumption).
        assert (HDRK : DRK B MT RG cx i cB OB capB outB ly1 S1 W1 (ms_mem ms3) ly2 S2 W2 mem2).
        { unfold DRK. cbv zeta. exists e', h', out', ev', LB, rest.
          split; [exact HAPK|]. split; [exact HMO|]. split; [exact HPa|]. split; [exact HPb|].
          split; [exact Dg8|]. split; [exact Dawr|]. split; [exact Deok|]. split; [exact HDREL|].
          split; [exact Dsrc|]. split; [exact Dkept | exact Dout]. }
        exists ly2, S2, Hp2, regs2, mem2, md2, k2.
        split; [rewrite Hcfg, Q1; reflexivity|].
        split; [ltac:(eapply rig_lift_DR_xR; exact HJD)|].
        split; [exact HPR|].
        exists Hp2, k2. split; [exact HJD|]. split; [exact HAPK|]. split; [exact HDRK | exact HRMd].
      - intros a Ha. exact (LFP cx i qd cB OB capB outB spent ly1 S1 _ W1 (ms_mem ms3) _ HB Hi Heof0 HGO3 HAR3 a Ha). }
    cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & -> & HJC & HJE & HPR2 &
      (Hpd & k2 & HJD & HAPK & HDRK & HRMd)).
    replace (spZ (ms_regs ms3)) with (gsp1 cx) in HJD by (rewrite HSPc; unfold gsp1, RIG_FRAME; lia).
    pose proof HDRK as (e' & h' & out' & ev' & LB & rest & HAPK' & HMO & HPa & HPb & Dg8 & Dawr & Deok &
      HDREL & Dsrc & Dkept & Dout).
    assert (Hfpb : forall a, inFP (dr_fp SA (gnth cx i) (fst (ghj cx i)) capB outB) a ->
      exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n).
    { intros a Ha.
      destruct (LFP cx i qd cB OB capB outB spent ly1 S1 _ W1 (ms_mem ms3) _ HB Hi Heof0 HGO3 HAR3 a Ha)
        as [(_ & Hb) | (b & n & Hin & _ & Hr)]; [exact Hb | exists b, n; split; [exact Hin | exact Hr]]. }
    pose proof (LDB ly1 S1 W1 (ms_mem ms3) ly2 S2 cB (gxmx cx) (Z.of_nat (length OB)) capB outB out'
      (gnth cx i) (fst (ghj cx i)) e' h' LB rest (gslot RG cx i) HEOK3 HSRCAT Hcap0 Hmx ltac:(lia)
      HINV HREST HPa HPb HDREL) as HBY.
    pose proof (LRO cx i qd cB OB capB outB spent ly1 S1 _ W1 (ms_mem ms3) _ (gsp1 cx)
      ly2 S2 Hpd W2 mem2 md2 k2 HB Hi Heof0 HGO3 HAR3 HJD ltac:(unfold gsp1, RIG_FRAME; lia) HDRK)
      as (e1 & h1 & ev1 & LB1 & out1 & HTM2).
    cbv zeta in HTM2.
    pose proof HTM2 as (_ & _ & _ & HDRD & _).
    (* the room round's counts: over drain's blocks the counts move by drain's net count (stmt_dr_cnt); the blocks
       drain does not own (rest) are the same on both sides *)
    assert (HCNT3 : forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly2 S2)) =
      Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
      tr_netP P (dr_tr cB (gxmx cx) (Z.of_nat (length OB)) capB (gnth cx i) (fst (ghj cx i)))).
    { intros P.
      pose proof (LDC cB (gxmx cx) (Z.of_nat (length OB)) capB outB out' (gnth cx i) (fst (ghj cx i)) e' h' LB P
        HINV HREST (td_hk _ _ _ _ _ HEOK3) (td_hk _ _ _ _ _ Deok) Hcap0 HDREL) as ECN. cbv zeta in ECN.
      rewrite (ReplyCnt.acnt_perm P _ _ HPb), (ReplyCnt.acnt_perm P _ _ HPa), !ReplyCnt.acnt_app.
      rewrite !ReplyCnt.acnt_app in ECN. lia. }
    pose proof (LBU cx i qd cB OB capB spent ly1 S1 ly2 S2 e1 h1 ev1 LB1
      (dr_ctl cB (fst (ghj cx i)) ev1)
      (if dr_live cB (fst (ghj cx i)) then OB ++ LB1 else OB)
      (if dr_live cB (fst (ghj cx i))
       then drain_b_c.ds_ocap (dr_fin cB (gxmx cx) (Z.of_nat (length OB)) capB (gnth cx i) (fst (ghj cx i)))
       else capB)
      HB Hi Hlq Hrel Hcl Hbr Hdd Hcap0 Hmx HBUD HDRD
      ltac:(intros _; split; [exact HINV | split; [exact HREST | split; [exact HMO |
        split; [exact HBY | split; [exact HRMd | exact HCNT3]]]]])
      ltac:(rewrite Hopen; intros HX; discriminate HX)) as HBU2.
    rewrite Hopen in HBU2.
    destruct (LLD cx fpos3 F FL ly1 S1 Hp3 W1 (ms_mem ms3) _ k1 SA (gnth cx i) (fst (ghj cx i)) capB outB
      ly2 S2 Hpd W2 mem2 md2 k2 Hp2 (k1 + kk) HB HJ3 ROM3' HPK3 HFR3 HLK3 HLS3 HJD Hfpb HAPK HJC) as [HGL2 HLS2].
    assert (GR : forall (r : bv 5) n, bv_unsigned r = n -> acallee_saved n -> getr regs2 r = getr (ms_regs ms3) r)
      by (intros r n Hn Hc'; exact (q1_pres _ _ n r HPR2 Hn Hc')).
    apply KPD. unfold PD_xR.
    exists regs2, ly2, S2, mem2, md2, (k1 + kk)%Z, F, FL, qd, cB, OB, capB, e1, h1, ev1, LB1,
      (dr_ctl cB (fst (ghj cx i)) ev1),
      (if dr_live cB (fst (ghj cx i)) then OB ++ LB1 else OB),
      (if dr_live cB (fst (ghj cx i))
       then drain_b_c.ds_ocap (dr_fin cB (gxmx cx) (Z.of_nat (length OB)) capB (gnth cx i) (fst (ghj cx i)))
       else capB), out1,
      (spent + dr_cost MT cB (gxmx cx) (Z.of_nat (length OB)) capB (gnth cx i) (fst (ghj cx i))).
    split; [unfold cfg_at, A_rig_pd, AF_fr_relay_instance_gone; reflexivity|].
    split.
    { unfold gregs_base, spZ.
      rewrite (GR 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia)), (HK 2%bv ltac:(cbv; tauto)).
      rewrite (GR 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia)), (HK 3%bv ltac:(cbv; tauto)).
      rewrite (GR 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia)), (HK 4%bv ltac:(cbv; tauto)).
      rewrite (GR 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia)), (HK 8%bv ltac:(cbv; tauto)).
      rewrite (GR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia)), (HK 9%bv ltac:(cbv; tauto)).
      rewrite (GR 21%bv 21 eq_refl ltac:(unfold acallee_saved; lia)), (HK 21%bv ltac:(cbv; tauto)).
      exact HRB. }
    split; [rewrite (GR 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia)), P18; unfold AENT; reflexivity|].
    split; [rewrite (GR 20%bv 20 eq_refl ltac:(unfold acallee_saved; lia)), (HK 20%bv ltac:(cbv; tauto)); exact R20|].
    split; [rewrite (GR 22%bv 22 eq_refl ltac:(unfold acallee_saved; lia)), (HK 22%bv ltac:(cbv; tauto)); exact R22|].
    split; [rewrite (GR 23%bv 23 eq_refl ltac:(unfold acallee_saved; lia)); exact P23|].
    split; [exact HGL2|]. split; [exact HLS2|]. split; [exact HTM2 | exact HBU2].
Qed.
End wR.

End c.
End b.
End a.
