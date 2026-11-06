(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment TOP of the IMAGE-B walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan-ubsan 0x82e1c .. 0x82f08 / 0x830c4), against the frozen segment interface
   lib/B/W_relay_instance_gone_cx.v (rig_top_stmt): the shared definitions and the statements of TOP's lemma tracks.
   The Section header is that file's, verbatim.  Proof SHAPE from k3's image-A TOP (a working branch
   80fffa8e840, lib/A/W_rig_top_defs.v); the instruction runs are image B's (fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record) 86226-86284).
   Proves no function (kind: segment lemma).
   C3 (the peak form; the image-A twin's re-fit of lib/A/W_rig_top.v, mirrored): drain's room is the peak of its
   trace, a prefix of the remaining trace (stmt_top_room); drain's live bytes are bounded in the NET form,
   blocks_bytes S' <= blocks_bytes S + tr_net (dr_tr ..) (stmt_dr_bytes, stmt_top_budget).
   ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record); the image-A twin is the RIG_x round of
   lib/A/W_rig_top.v, commit f4cd818e98d): over any allocator relation ARx with its laws and the room record RP, at
   W_relay_instance_gone_cx.v's generic Section c (its list copied verbatim, in every TOP file).  Every journal is
   ajournal_gx_x with its head sets, at the kit's RIG_STK_x / DRAIN_STK_x; the laws are AR_laws_x's; the journal
   helpers copied from W_gesture_end.v are their _x twins.  THE ROOM at the drain call: dr_kr and gtop_bud's layout
   (stmt_top_room / stmt_top_budget); THE COUNTS: stmt_dr_cnt, lib/B/W_rr_m_dcnt.v rmc_dr_cnt's text. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
(* tr_netP and its laws: part I0 of lib/B/W_rr_m_dcnt.v, A's lib/A/W_tr_cnt.v names *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rr_m_dcnt.
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

(* ---- Walk helpers, copied from lib/B/W_gesture_end.v (W4's, Qed on bint; that file does not build on this branch:
   its W_ge_room.v predates the kit's ge_room); the journal helpers over ajournal_gx_x, as image A's
   lib/A/W_gestures_end.v gse_callS_x / gse_keep_img_x / gse_keep_high_x / gse_nodup_x (commit f4cd818e98d) state and
   prove them. ---- *)
Lemma ge_garr8_aview : forall H mem a l j, garr8 SEGS (mrestrict H mem) a l -> (j < length l)%nat ->
aview SEGS H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof. intros H mem a l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. exact (aview_of_val_mem1 SEGS H mem _ _ Hv Hr). Qed.
Lemma ge_garr8_kept : forall H H' (m m' : word -> option byte) a l, garr8 SEGS (mrestrict H m) a l ->
(forall b, a <= b < a + Z.of_nat (length l) -> aview SEGS H' m' b = aview SEGS H m b) -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hg Hk. apply (garr8_frame SEGS _ _ a l Hg). intros b Hb. apply (mbyte_of_aview SEGS). exact (Hk b Hb).
Qed.
(* A call to a program function inside a walk: the donor's cl_callS (YC85.v:383) over ajournal_gx_x with no
   out-parameter.  The callee's contract is applied at its entry (its afn_pre_x from the caller's journal), and its
   journal is composed into the caller's (W_journal_x.v ajournal_gx_sub_x); o = 0 is a tail call. *)
Lemma gx_callS_x : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1
(o : Z) raw ch1 (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
gx_ok SEGS B G ->
ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK1 (spZ regsc) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros G W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 K
HGx HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee.
  pose proof HJ as HJin. apply ajournal_gx_inner_x in HJin. destruct HJin as (memS & HJi & _).
  rewrite !Z.add_0_r in HJi.
  eapply (afn_pre_x_at SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memc mdc k regsc STK1 o ch1 HJi);
  try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HPr & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [reflexivity|].
rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HPr | exact HK]]].
change own with ([] ++ own).
eapply (ajournal_gx_sub_x SEGS B PST ARx LAWS pa_segs_low);
[exact HJ | exact HJ1 | lia | lia | lia | | exact HGx | exact HF].
intros a (r & Hr & _). destruct Hr.
Qed.
(* The caller's own window stays present through its journal. *)
Lemma ajgx_pres_x : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (HS0 & HX0 & (memS & HJi & _) & _) a Ha.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. lia.
Qed.
(* A callee's journal keeps every byte above alloc_ceiling outside its window (G lies in the image). *)
Lemma ajgx_keep_high_x : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
gx_ok SEGS B G -> ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
pose proof asan_consts as (C1 & _).
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
pose proof (inG_low SEGS B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* A journal keeps the image bytes outside G, the allocator's statics, errno and the program statics PST. *)
Lemma ajgx_keep_img_x : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a -> ~ inG G a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _)
  a Hi Ho He Hq Hf Hg.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hq Hf).
pose proof (pa_segs_low a Hi) as HL.
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
Lemma fp_spares_blocks : forall bl a, (forall b, In b bl -> 4096 <= fst b) -> fp_spares (ablocks_fp bl) a.
Proof.
intros bl a Hb Ho. exfalso. destruct Ho as (r & Hr & H0).
unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hin). cbn [fst snd] in H0. pose proof (Hb b Hin). lia.
Qed.

(* The live blocks are pairwise distinct (their extents are pairwise disjoint and non-empty: BLKN). *)
Lemma ablocks_nodup_x : forall ly S Hp W mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp W mem md HAR. destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hpw _].
apply pairwise_app_l in Hpw as [Hpw _].
assert (Hpos : Forall (fun b => 0 < req_size (snd b)) (ablocks B ly S)).
{ apply Forall_forall. intros [p n] Hin. pose proof (BLKN ly S Hp W mem md p n HAR Hin) as Hn.
  cbn [snd]. pose proof (req_size_pos n ltac:(lia)). lia. }
induction (ablocks B ly S) as [|b l IH]; [apply List.NoDup_nil|].
cbn [map pairwise] in Hpw. destruct Hpw as [Hf Hpw]. inversion Hpos as [|? ? Hb Hl]; subst.
apply List.NoDup_cons; [|exact (IH Hpw Hl)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
(* A journal keeps the top of the stack layout. *)
Lemma ajgx_ly_top_x : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ly_top ly' = ly_top ly.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET.
Qed.
(* The state at a journal's end is an ARx state (ajournal_gx_AR_x with the arguments inferred). *)
Lemma tj_AR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ARx ly' S' Hp' W' mem' md'.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (ajournal_gx_AR_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.

(* apres_kept (W_contract.v) composes, and holds over any step that keeps every present byte present. *)
Lemma apk_trans : forall W1 (m1 : word -> option byte) W2 m2 W3 m3,
apres_kept B W1 m1 W2 m2 -> apres_kept B W2 m2 W3 m3 -> apres_kept B W1 m1 W3 m3.
Proof. intros W1 m1 W2 m2 W3 m3 H1 H2 a Hi Ho He Hp. exact (H2 a Hi Ho He (H1 a Hi Ho He Hp)). Qed.
Lemma apk_of_pres : forall W (m m' : word -> option byte),
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) -> apres_kept B W m W m'.
Proof. intros W m m' H a _ _ _ Hp. exact (H a Hp). Qed.

(* ======================================================================================================
   Shared definitions of segment TOP.
   ====================================================================================================== *)
Definition A_rig_pd : Z := AF_fr_relay_instance_gone + 0x1cc.    (* 0x82e6c, after the drain step (both eof arms) *)

(* What TOP keeps of entry i's drain (drain's post, dr_post_x, at the callee's final state ly2 S2 W2 m2): the
   conjuncts the walk uses, named.  rest is dr_post_x's: the live blocks drain does not own. *)
Definition DRK (cx : gcx) (i : nat) (c2 : ctl) (O2 : list byte) (cap2 out2 : Z)
  (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte)
  (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (m2 : word -> option byte) : Prop :=
let e := gnth cx i in
let h := fst (ghj cx i) in
let no := Z.of_nat (length O2) in
let fin := dr_fin c2 (gxmx cx) no cap2 e h in
let live := dr_live c2 h in
let cap' := if live then drain_b_c.ds_ocap fin else cap2 in
exists (e' : rentry) (h' : hsrc) (out' ev' : Z) (LB : list byte) (rest : list (Z * Z)),
apres_kept B W1 m1 W2 m2 /\
mo_le MT S1 S2 (dr_cost MT c2 (gxmx cx) no cap2 e h) /\
Permutation (ablocks B ly1 S1) (aentry_blks e ++ asrc_blks h ++ aout_blks cap2 out2 ++ rest) /\
Permutation (ablocks B ly2 S2) (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) /\
garr8 SEGS (arm W2 m2) (gSA cx i) (bzs (entry_bytes e')) /\ awr W2 m2 (gSA cx i) AENT /\
aentry_ok B ly2 S2 W2 m2 e' /\
dr_rel c2 (gxmx cx) no cap2 e h e' h' LB /\
asrc_at B ly2 S2 W2 m2 (gslot RG cx i) h' /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (gslot RG cx i <= a < gslot RG cx i + ASRC) -> abyte_kept W1 m1 W2 m2 a) /\
aout_at B RG ly2 S2 W2 m2 (dr_ctl c2 h ev') (if live then O2 ++ LB else O2) (gxmx cx) (if live then no + dr_tot h else no)
  cap' out'.

(* GTOPM: inside entry i after its drain step (drained when open: gdrained), before its keys; GIN's facts at
   n = 0, ks = re_keys e1, Ed = [] less the prefix, its shadow, the measure and the budget. *)
Definition GTOPM (cx : gcx) (i : nat) (qd : list (rentry * hsrc)) (cB : ctl) (OB : list byte) (capB : Z)
  (e1 : rentry) (h1 : hsrc) (ev : Z) (LB : list byte) (c1 : ctl) (O1 : list byte) (cap1 out1 : Z)
  (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
let e := gnth cx i in
let h := fst (ghj cx i) in
let open := re_eof e =? 0 in
(i < length (gxes cx))%nat /\ length qd = i /\
rig_rel (gpre cx) (gxmx cx) (gxc cx) (gxO cx) (gxcap cx) (firstn i (gps cx)) qd cB OB capB /\
gdrained cx cB OB capB e h e1 h1 ev LB c1 O1 cap1 /\
arelay_at B RG ly1 S1 W1 m1 (gxG0 cx) (map fst qd ++ e1 :: skipn (S i) (gxes cx)) /\
aout_at B RG ly1 S1 W1 m1 c1 O1 (gxmx cx) (Z.of_nat (length O1)) cap1 out1 /\
(forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
   asrc_at B ly1 S1 W1 m1 (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
(open = true -> asrc_at B ly1 S1 W1 m1 (gslot RG cx i) h1) /\
Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly1 S1 W1 m1 (fst p) (fst (snd p)) (snd (snd p)))
  (skipn (S i) (gps cx)) /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
   (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
   abyte_kept (gxW cx) (gxmem cx) W1 m1 a) /\
Permutation (ablocks B ly1 S1)
  ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ e1 :: skipn (S i) (gxes cx))) ++
   gdone_srcs (firstn i (gps cx)) qd ++ (if open then asrc_blks h1 else []) ++ rig_srcs (skipn (S i) (gps cx)) ++
   aout_blks cap1 out1 ++ gxrest cx).

(* the budget after the drain step: entry i's key run, then the entries after it *)
Definition gtop_bud (cx : gcx) (e1 : rentry) (c1 : ctl) (O1 : list byte) (cap1 : Z) (i : nat) (ly1 : alayout)
  (S1 : astate) (spent : Z) : Prop :=
let Er := fst (geik (gpre cx) (re_keys e1)) in
let '(_, O3, cap3) := sl_sends (gxmx cx) c1 O1 cap1 (ge_bytes Er) in
gbud B MT RP MMAX cx ly1 S1 spent (gkrest cx (Z.of_nat (length O1)) cap1 Er ++ grest cx (S i) (Z.of_nat (length O3)) cap3).

(* THE ROOM drain leaves (dr_spec_x's kr at TOP's call): the MT_rk count of the requests after entry i's drain (the
   rest of grest i) on top of the entry's budget gxkr *)
Definition dr_kr (cx : gcx) (i : nat) (c2 : ctl) (no2 cap2 : Z) : nat :=
(Z.to_nat (tr_cost MT_rk (grest cx i no2 cap2) - dr_cost MT_rk c2 (gxmx cx) no2 cap2 (gnth cx i) (fst (ghj cx i))) +
 gxkr cx)%nat.

(* ---------------------------------------------------------------- statements of TOP's lemma tracks *)

(* B1. drain's model invariant at entry i's drain, from the relay entry and the harness source (W_contract.v
   dr_src_ok, W_rep.v aentry_ok): the premises of lib/Prog/relay_instance_gone_b_lem.v rig_drain_model. *)
Definition stmt_dr_inv_of : Prop :=
forall ly S W mem e h j no cap,
aentry_ok B ly S W mem e -> dr_src_ok B RG ly S W mem e h j ->
relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) /\
relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h).

(* B2. drain's room at entry i (dr_spec_x's budget premises: the meter, and the room round's room and count), from
   GOUT i's budget. *)
Definition stmt_top_room : Prop :=
forall cx i qd c2 O2 cap2 spent ly1 S1,
let e := gnth cx i in let h := fst (ghj cx i) in let no2 := Z.of_nat (length O2) in
GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> length qd = i -> re_eof e = 0 ->
rig_rel (gpre cx) (gxmx cx) (gxc cx) (gxO cx) (gxcap cx) (firstn i (gps cx)) qd c2 O2 cap2 ->
(ct_cl c2 = 3 \/ ct_cl c2 = -1) -> (ct_br c2 = 0 \/ ct_br c2 = 1) -> (ct_dd c2 = 0 \/ ct_dd c2 = 1) ->
0 <= cap2 -> 0 <= gxmx cx <= 255 ->
relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no2 cap2 e h) ->
relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no2 cap2 e h) = bzs (pending_stream h) ->
gbud B MT RP MMAX cx ly1 S1 spent (grest cx i no2 cap2) ->
tr_max (dr_tr c2 (gxmx cx) no2 cap2 e h) < MMAX /\
blocks_bytes S1 + tr_peak (dr_tr c2 (gxmx cx) no2 cap2 e h) <= LIVE_MAX /\
mo_ok MT S1 (dr_cost MT c2 (gxmx cx) no2 cap2 e h) /\
rp_RM RP S1 (Z.to_nat (dr_cost MT_rk c2 (gxmx cx) no2 cap2 e h) + dr_kr cx i c2 no2 cap2) /\
cnt_ok_pk RP (dr_pk c2 (gxmx cx) no2 cap2 e h) (ablocks B ly1 S1).

(* B3. the budget across the drain step: GOUT i's budget, the drain's charge, room and count change (open) or
   nothing (not open), gives the budget of entry i's key run followed by the entries after it (gtop_bud). *)
Definition stmt_top_budget : Prop :=
forall cx i qd c2 O2 cap2 spent ly1 S1 ly2 S2 e1 h1 ev LB c1 O1 cap1,
let e := gnth cx i in let h := fst (ghj cx i) in let no2 := Z.of_nat (length O2) in
let open := re_eof e =? 0 in
GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> length qd = i ->
rig_rel (gpre cx) (gxmx cx) (gxc cx) (gxO cx) (gxcap cx) (firstn i (gps cx)) qd c2 O2 cap2 ->
(ct_cl c2 = 3 \/ ct_cl c2 = -1) -> (ct_br c2 = 0 \/ ct_br c2 = 1) -> (ct_dd c2 = 0 \/ ct_dd c2 = 1) ->
0 <= cap2 -> 0 <= gxmx cx <= 255 ->
gbud B MT RP MMAX cx ly1 S1 spent (grest cx i no2 cap2) ->
gdrained cx c2 O2 cap2 e h e1 h1 ev LB c1 O1 cap1 ->
(open = true ->
  relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no2 cap2 e h) /\
  relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no2 cap2 e h) = bzs (pending_stream h) /\
  mo_le MT S1 S2 (dr_cost MT c2 (gxmx cx) no2 cap2 e h) /\
  blocks_bytes S2 <= blocks_bytes S1 + tr_net (dr_tr c2 (gxmx cx) no2 cap2 e h) /\
  rp_RM RP S2 (dr_kr cx i c2 no2 cap2) /\
  (forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly2 S2)) =
     Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) + tr_netP P (dr_tr c2 (gxmx cx) no2 cap2 e h))) ->
(open = false -> mo_le MT S1 S2 0 /\ blocks_bytes S2 <= blocks_bytes S1 /\
  rp_RM RP S2 (Z.to_nat (tr_cost MT_rk (grest cx i no2 cap2)) + gxkr cx) /\ ablocks B ly2 S2 = ablocks B ly1 S1) ->
gtop_bud cx e1 c1 O1 cap1 i ly2 S2 (spent + (if open then dr_cost MT c2 (gxmx cx) no2 cap2 e h else 0)).

(* D. drain's live bytes: what drain leaves of its entry, source and output (DRK's Permutations, dr_rel, the
   output capacity) holds at most its request trace's net change (tr_net, C3) more than it found. *)
Definition stmt_dr_bytes : Prop :=
forall ly S W mem ly' S' c mx no cap out out' e h e' h' LB rest HA,
let fin := dr_fin c mx no cap e h in
let cap' := if dr_live c h then drain_b_c.ds_ocap fin else cap in
aentry_ok B ly S W mem e -> asrc_at B ly S W mem HA h -> 0 <= cap -> 0 <= mx <= 255 -> 0 <= no ->
relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) ->
relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h) ->
Permutation (ablocks B ly S) (aentry_blks e ++ asrc_blks h ++ aout_blks cap out ++ rest) ->
Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) ->
dr_rel c mx no cap e h e' h' LB ->
blocks_bytes S' <= blocks_bytes S + tr_net (dr_tr c mx no cap e h).

(* D'. drain's live counts (the room round): over the blocks drain's post names, the count of the blocks whose size
   satisfies P moves by exactly the net count tr_netP P of drain's trace.  The RR family's model lemma, its text:
   lib/B/W_rr_m_dcnt.v rmc_dr_cnt (image A's lib/A/W_rr_m_dcnt.v); TOP takes it as this statement and rig_top_proof
   plugs rmc_dr_cnt in. *)
Definition stmt_dr_cnt : Prop :=
forall c mx no cap out out' e h e' h' LB (P : Z -> bool),
let fin := dr_fin c mx no cap e h in
let cap' := if dr_live c h then drain_b_c.ds_ocap fin else cap in
relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) ->
relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h) ->
(re_hp e = 0 \/ re_kh e <> 0) -> (re_hp e' = 0 \/ re_kh e' <> 0) -> 0 <= cap ->
dr_rel c mx no cap e h e' h' LB ->
Z.of_nat (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out')) =
Z.of_nat (ReplyCnt.acnt P (aentry_blks e ++ asrc_blks h ++ aout_blks cap out)) + tr_netP P (dr_tr c mx no cap e h).

(* C1. the relay after entry i's drain (open entry): GOUT i at the drain's entry state, drain's journal and DRK
   give GTOPM at drain's final state. *)
Definition stmt_top_rep_open : Prop :=
forall cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 sp1 ly2 S2 Hp2 W2 m2 md2 k2,
let e := gnth cx i in let h := fst (ghj cx i) in
GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> re_eof e = 0 ->
GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
ARx ly1 S1 Hp1 W1 m1 md1 ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x sp1 (dr_fp (gSA cx i) e h cap2 out2)
  ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k2 ->
alloc_ceiling <= sp1 - DRAIN_STK_x ->
DRK cx i c2 O2 cap2 out2 ly1 S1 W1 m1 ly2 S2 W2 m2 ->
exists e1 h1 ev LB out1,
let no2 := Z.of_nat (length O2) in
let live := dr_live c2 h in
let c1 := dr_ctl c2 h ev in
let O1 := if live then O2 ++ LB else O2 in
let cap1 := if live then drain_b_c.ds_ocap (dr_fin c2 (gxmx cx) no2 cap2 e h) else cap2 in
GTOPM cx i qd c2 O2 cap2 e1 h1 ev LB c1 O1 cap1 out1 ly2 S2 W2 m2.

(* C2. the same step for an entry already closed (no drain): GOUT i gives GTOPM at the same state. *)
Definition stmt_top_rep_closed : Prop :=
forall cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1,
GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> re_eof (gnth cx i) <> 0 ->
GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
GTOPM cx i qd c2 O2 cap2 (gnth cx i) (fst (ghj cx i)) 0 [] c2 O2 cap2 out2 ly1 S1 W1 m1.

(* C3. GOUT and GTOPM survive a memory change that keeps every byte below alloc_ceiling outside the fake frame
   (1, fpos) and its shadow (in_frames), and keeps present bytes present: the walk's stores to the stack and to
   F's shadow, snprintf's write into F + 32 .. F + 80, and the runtime calls' scratch. *)
Definition stmt_gout_kept : Prop :=
forall cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 m1' fpos,
GBASE B ARx MT RP MMAX RG cx ->
ARx ly1 S1 Hp1 W1 m1 md1 -> In (1, fpos) (frames S1) ->
(forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a -> aview SEGS (w_H W1) m1' a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m1' a) ->
GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1'.
Definition stmt_gtopm_kept : Prop :=
forall cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 m1' fpos,
GBASE B ARx MT RP MMAX RG cx ->
ARx ly1 S1 Hp1 W1 m1 md1 -> In (1, fpos) (frames S1) ->
(forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a -> aview SEGS (w_H W1) m1' a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m1' a) ->
GTOPM cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 ly1 S1 W1 m1 ->
GTOPM cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 ly1 S1 W1 m1'.

(* C4. what drain's contract asks of entry i (open) at TOP's call, from GOUT i (dr_spec's memory premises). *)
Definition stmt_top_drain_pre : Prop :=
forall cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1,
let e := gnth cx i in let h := fst (ghj cx i) in let j := snd (ghj cx i) in
GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> re_eof e = 0 ->
GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
ARx ly1 S1 Hp1 W1 m1 md1 ->
In (gxG0 cx, ATABLE) (ablocks B ly1 S1) /\ gxG0 cx <= gSA cx i /\ gSA cx i + AENT <= gxG0 cx + ATABLE /\
garr8 SEGS (arm W1 m1) (gSA cx i) (bzs (entry_bytes e)) /\ awr W1 m1 (gSA cx i) AENT /\
aentry_ok B ly1 S1 W1 m1 e /\ dr_src_ok B RG ly1 S1 W1 m1 e h j /\
(exists rest, Permutation (ablocks B ly1 S1) ((gxG0 cx, ATABLE) :: aentry_blks e ++ asrc_blks h ++ aout_blks cap2 out2 ++ rest)).

(* C5. drain's footprint lies in TOP's (gx_callS_x's footprint premise at the drain call): every byte drain may write
   is a byte of the journal's footprint that is in a live block now, or a byte of a block made since the entry. *)
Definition stmt_dr_fp_in : Prop :=
forall cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1,
let e := gnth cx i in let h := fst (ghj cx i) in
GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> re_eof e = 0 ->
GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
ARx ly1 S1 Hp1 W1 m1 md1 ->
forall a, inFP (dr_fp (gSA cx i) e h cap2 out2) a ->
(inFP (gFP cx) a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
in_tmp_block (ablocks B (gxly cx) (gxS cx)) (ablocks B ly1 S1) a.

(* L1. GLIVE and the loop's frame slots survive a stretch of the walk that writes only (P) the scratch below sp,
   the slot 80(sp) (i, 0x82e84), the prefix buffer F + 32 .. F + 80 and F's shadow, keeps present bytes present and
   carries the journal (the run's own journal at the new memory). *)
Definition stmt_live_kept : Prop :=
forall cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 Hp2 m2 md2 (P : Z -> Prop),
GBASE B ARx MT RP MMAX RG cx ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
rom_view SEGS W1 m1 -> apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 ->
alock_at RG W1 m1 true -> g_lslots RG cx F W1 m1 ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp2 W1 m2 md2 k1 ->
(forall a, P a -> (gsp1 cx - 3 * ESTACK <= a < gsp1 cx) \/ (gsp1 cx + 80 <= a < gsp1 cx + 88) \/
   (F + 32 <= a < F + 80) \/ (shadow_addr F <= a < shadow_addr F + 16)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
GLIVE B PST ARx RG cx F FL ly1 S1 W1 m2 md2 k1 /\ g_lslots RG cx F W1 m2.

(* L2. GLIVE and the loop's frame slots across the drain call at 0x82e68: the caller's journal at the call, drain's
   journal (at G_DR, from sp = gsp1, footprint dr_fp: block bytes only), drain's apres_kept and the composed journal
   (gx_callS_x's) give GLIVE at drain's final state. *)
Definition stmt_live_drain : Prop :=
forall cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 SA e h cap out ly2 S2 Hp2 W2 m2 md2 k2 Hp3 k3,
GBASE B ARx MT RP MMAX RG cx ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
rom_view SEGS W1 m1 -> apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 ->
alock_at RG W1 m1 true -> g_lslots RG cx F W1 m1 ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (gsp1 cx) (dr_fp SA e h cap out)
  ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k2 ->
(forall a, inFP (dr_fp SA e h cap out) a -> exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) ->
apres_kept B W1 m1 W2 m2 ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly2 S2 Hp3 W2 m2 md2 k3 ->
GLIVE B PST ARx RG cx F FL ly2 S2 W2 m2 md2 k3 /\ g_lslots RG cx F W2 m2.

(* G1. entry i's key loop starts (nheld = S r > 0): GTOPM, the budget after the drain step, the prefix and its zero
   shadow in the fake frame give GIN at n = 0, ks = re_keys e1, nothing ended (Ed = []), the stream (c1, O1, cap1). *)
Definition stmt_gin_top : Prop :=
forall cx i r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 spent ly1 S1 W1 m1,
GBASE B ARx MT RP MMAX RG cx ->
GTOPM cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 ly1 S1 W1 m1 ->
gtop_bud cx e1 c1 O1 cap1 i ly1 S1 spent ->
re_nheld e1 = Z.of_nat (S r) ->
garr8 SEGS (arm W1 m1) (F + 32) (gpre cx ++ [0]) ->
garr8 SEGS (arm W1 m1) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0] ->
exists ks f, GIN B MT RP MMAX RG cx i 0 r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks [] f c1 O1 cap1 out1 spent ly1 S1 W1 m1.

(* G2. entry i holds no key (nheld <= 0): GTOPM and the budget give GOUT (S i). *)
Definition stmt_gout_top : Prop :=
forall cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 spent ly1 S1 W1 m1,
GBASE B ARx MT RP MMAX RG cx ->
GTOPM cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 ly1 S1 W1 m1 ->
gtop_bud cx e1 c1 O1 cap1 i ly1 S1 spent ->
re_nheld e1 <= 0 ->
exists qd', GOUT B MT RP MMAX RG cx (S i) qd' c1 O1 cap1 out1 spent ly1 S1 W1 m1.

(* ---- the two runtime calls of TOP: snprintf (F + 32, 48, "%s %d ", "param_gesture", id) at 0x82eb8 and
   strlen (F + 32) at 0x82ec0, over the walk's journal (own = [(1, fpos)], the fake frame F). ---- *)
Definition TP_FMT : list Z := [37; 115; 32; 37; 100; 32].

(* S1. the snprintf call at 0x82eb8.  The two literals ("%s %d ", A_OBJ 17; "param_gesture", A_OBJ 18) come from the
   Section's HLIT17 / HLIT18; the guard (the GOT word, a fact of every ARx state, and the canary's bytes, image bytes) is the
   caller's premise, as the cx file's header states it. *)
Definition stmt_snp_call : Prop :=
forall W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F id idv (Post : world SEGS -> config -> Prop),
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 - 224 -> sp0 mod 16 = 0 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 (F + 32) -> getr regsT 11 = w64 48 -> getr regsT 12 = w64 (VAL (A_OBJ 17)) ->
getr regsT 13 = w64 (VAL (A_OBJ 18)) -> getr regsT 14 = w64 idv -> idv mod 2 ^ 32 = id mod 2 ^ 32 -> - 2 ^ 31 <= id < 2 ^ 31 ->
frame_addr lyc 1 fpos = F ->
(forall o, 4 <= o < 10 -> aview SEGS (w_H W) memT (shadow_addr F + o) = Some 0) ->
rom_view SEGS W memT ->
aguard_ok W memT FR_GOT_GUARD FR_GUARD ->
(forall regs2 mem2 md2,
   ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W mem2 md2 k ->
   aregs_preserved regsT regs2 ->
   getr regs2 10 = w64 (Z.of_nat (length (relay_instance_gone_b_c.instance_prefix id))) ->
   garr8 SEGS (arm W mem2) (F + 32) (relay_instance_gone_b_c.instance_prefix id ++ [0]) ->
   (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 80) -> ~ (sp0 - 224 - 3 * ESTACK <= a < sp0 - 224) ->
      aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
   (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
   SRr SEGS W (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA WS_snprintf)) memT (seg_rom SEGS)) mdc) Post.

(* S2. the strlen call at 0x82ec0 *)
Definition stmt_strlen_call : Prop :=
forall W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F (pre : list Z) (Post : world SEGS -> config -> Prop),
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 - 224 -> sp0 mod 16 = 0 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 (F + 32) -> frame_addr lyc 1 fpos = F ->
garr8 SEGS (arm W memT) (F + 32) (pre ++ [0]) -> ~ In 0 pre -> (length pre <= 47)%nat ->
(forall o, 4 <= o < 10 -> aview SEGS (w_H W) memT (shadow_addr F + o) = Some 0) ->
rom_view SEGS W memT ->
(forall regs2 mem2 md2,
   ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W mem2 md2 k ->
   aregs_preserved regsT regs2 -> getr regs2 10 = w64 (Z.of_nat (length pre)) ->
   (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 224 - 2 * ESTACK <= a < sp0 - 224) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
   (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
   SRr SEGS W (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA WS_strlen)) memT (seg_rom SEGS)) mdc) Post.

(* ---- the mid cut of TOP's walk: 0x82e6c, after entry i's drain step (the call when s->eof = 0, nothing
   otherwise).  s2 = 56 i, s4 = F's shadow, s6 = i, s7 = g_src's register image; GTOPM and the budget after the
   drain step (gtop_bud). ---- *)
Definition PD (cx : gcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 spent,
c1 = cfg_at SEGS (BASE + A_rig_pd) regs1 m1 md1 /\
gregs_base cx regs1 /\
getr regs1 18 = w64 (AENT * Z.of_nat i) /\ getr regs1 20 = w64 (shadow_addr F) /\
getr regs1 22 = w64 (Z.of_nat i) /\ getr regs1 23 = w64 (rg_src RG + RIG_HI_SRC) /\
GLIVE B PST ARx RG cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots RG cx F W1 m1 /\
GTOPM cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 W1 m1 /\
gtop_bud cx e1 c1' O1 cap1 i ly1 S1 spent.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): TOP's journal helpers and statements at a world relation R.  Each X_xR is X above with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the cx file's carriers (GLIVE, RGO, RGI, RGE, gPOST)
   and W_rig_top_defs.v's journal statements -> their R twins, the journal lemmas -> their _xR twins (W_journal_x.v).  Every other token is X's.  The hypothesis list is
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
(* :195 gx_callS_x *)
Lemma gx_callS_xR : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1
(o : Z) raw ch1 (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
gx_ok SEGS B G ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
 SRrG SEGS R W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK1 (spZ regsc) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRrG SEGS R W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros G W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 K
HGx HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRrG_mono.
{ apply Hcallee.
  pose proof HJ as HJin. apply ajournal_gx_inner_xR in HJin. destruct HJin as (memS & HJi & _).
  rewrite !Z.add_0_r in HJi.
  eapply (afn_pre_x_atR SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memc mdc k regsc STK1 o ch1 HJi);
  try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HPr & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [reflexivity|].
rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HPr | exact HK]]].
change own with ([] ++ own).
eapply (ajournal_gx_sub_xR SEGS B PST ARx LAWS pa_segs_low R_trans);
[exact HJ | exact HJ1 | lia | lia | lia | | exact HGx | exact HF].
intros a (r & Hr & _). destruct Hr.
Qed.
(* :239 ajgx_pres_x *)
Lemma ajgx_pres_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (HS0 & HX0 & (memS & HJi & _) & _) a Ha.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. lia.
Qed.
(* :247 ajgx_keep_high_x *)
Lemma ajgx_keep_high_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
gx_ok SEGS B G -> ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
pose proof asan_consts as (C1 & _).
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
pose proof (inG_low SEGS B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* :259 ajgx_keep_img_x *)
Lemma ajgx_keep_img_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a -> ~ inG G a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _)
  a Hi Ho He Hq Hf Hg.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hq Hf).
pose proof (pa_segs_low a Hi) as HL.
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
(* :291 ajgx_ly_top_x *)
Lemma ajgx_ly_top_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ly_top ly' = ly_top ly.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET.
Qed.
(* :299 tj_AR *)
Lemma tj_AR_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ARx ly' S' Hp' W' mem' md'.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.
(* :466 stmt_top_rep_open *)
Definition stmt_top_rep_open_xR : Prop :=
forall cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 sp1 ly2 S2 Hp2 W2 m2 md2 k2,
let e := gnth cx i in let h := fst (ghj cx i) in
GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> re_eof e = 0 ->
GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
ARx ly1 S1 Hp1 W1 m1 md1 ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x sp1 (dr_fp (gSA cx i) e h cap2 out2)
  ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k2 ->
alloc_ceiling <= sp1 - DRAIN_STK_x ->
DRK cx i c2 O2 cap2 out2 ly1 S1 W1 m1 ly2 S2 W2 m2 ->
exists e1 h1 ev LB out1,
let no2 := Z.of_nat (length O2) in
let live := dr_live c2 h in
let c1 := dr_ctl c2 h ev in
let O1 := if live then O2 ++ LB else O2 in
let cap1 := if live then drain_b_c.ds_ocap (dr_fin c2 (gxmx cx) no2 cap2 e h) else cap2 in
GTOPM cx i qd c2 O2 cap2 e1 h1 ev LB c1 O1 cap1 out1 ly2 S2 W2 m2.
(* :538 stmt_live_kept *)
Definition stmt_live_kept_xR : Prop :=
forall cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 Hp2 m2 md2 (P : Z -> Prop),
GBASE B ARx MT RP MMAX RG cx ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
rom_view SEGS W1 m1 -> apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 ->
alock_at RG W1 m1 true -> g_lslots RG cx F W1 m1 ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp2 W1 m2 md2 k1 ->
(forall a, P a -> (gsp1 cx - 3 * ESTACK <= a < gsp1 cx) \/ (gsp1 cx + 80 <= a < gsp1 cx + 88) \/
   (F + 32 <= a < F + 80) \/ (shadow_addr F <= a < shadow_addr F + 16)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
GLIVE_xR B PST ARx RG R cx F FL ly1 S1 W1 m2 md2 k1 /\ g_lslots RG cx F W1 m2.
(* :556 stmt_live_drain *)
Definition stmt_live_drain_xR : Prop :=
forall cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 SA e h cap out ly2 S2 Hp2 W2 m2 md2 k2 Hp3 k3,
GBASE B ARx MT RP MMAX RG cx ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
rom_view SEGS W1 m1 -> apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 ->
alock_at RG W1 m1 true -> g_lslots RG cx F W1 m1 ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (gsp1 cx) (dr_fp SA e h cap out)
  ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k2 ->
(forall a, inFP (dr_fp SA e h cap out) a -> exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) ->
apres_kept B W1 m1 W2 m2 ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly2 S2 Hp3 W2 m2 md2 k3 ->
GLIVE_xR B PST ARx RG R cx F FL ly2 S2 W2 m2 md2 k3 /\ g_lslots RG cx F W2 m2.
(* :599 stmt_snp_call *)
Definition stmt_snp_call_xR : Prop :=
forall W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F id idv (Post : world SEGS -> config -> Prop),
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 - 224 -> sp0 mod 16 = 0 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 (F + 32) -> getr regsT 11 = w64 48 -> getr regsT 12 = w64 (VAL (A_OBJ 17)) ->
getr regsT 13 = w64 (VAL (A_OBJ 18)) -> getr regsT 14 = w64 idv -> idv mod 2 ^ 32 = id mod 2 ^ 32 -> - 2 ^ 31 <= id < 2 ^ 31 ->
frame_addr lyc 1 fpos = F ->
(forall o, 4 <= o < 10 -> aview SEGS (w_H W) memT (shadow_addr F + o) = Some 0) ->
rom_view SEGS W memT ->
aguard_ok W memT FR_GOT_GUARD FR_GUARD ->
(forall regs2 mem2 md2,
   ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W mem2 md2 k ->
   aregs_preserved regsT regs2 ->
   getr regs2 10 = w64 (Z.of_nat (length (relay_instance_gone_b_c.instance_prefix id))) ->
   garr8 SEGS (arm W mem2) (F + 32) (relay_instance_gone_b_c.instance_prefix id ++ [0]) ->
   (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 80) -> ~ (sp0 - 224 - 3 * ESTACK <= a < sp0 - 224) ->
      aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
   (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
   SRrG SEGS R W (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Post) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA WS_snprintf)) memT (seg_rom SEGS)) mdc) Post.
(* :622 stmt_strlen_call *)
Definition stmt_strlen_call_xR : Prop :=
forall W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F (pre : list Z) (Post : world SEGS -> config -> Prop),
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 - 224 -> sp0 mod 16 = 0 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 (F + 32) -> frame_addr lyc 1 fpos = F ->
garr8 SEGS (arm W memT) (F + 32) (pre ++ [0]) -> ~ In 0 pre -> (length pre <= 47)%nat ->
(forall o, 4 <= o < 10 -> aview SEGS (w_H W) memT (shadow_addr F + o) = Some 0) ->
rom_view SEGS W memT ->
(forall regs2 mem2 md2,
   ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W mem2 md2 k ->
   aregs_preserved regsT regs2 -> getr regs2 10 = w64 (Z.of_nat (length pre)) ->
   (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 224 - 2 * ESTACK <= a < sp0 - 224) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
   (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
   SRrG SEGS R W (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Post) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA WS_strlen)) memT (seg_rom SEGS)) mdc) Post.
(* :642 PD *)
Definition PD_xR (cx : gcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 spent,
c1 = cfg_at SEGS (BASE + A_rig_pd) regs1 m1 md1 /\
gregs_base cx regs1 /\
getr regs1 18 = w64 (AENT * Z.of_nat i) /\ getr regs1 20 = w64 (shadow_addr F) /\
getr regs1 22 = w64 (Z.of_nat i) /\ getr regs1 23 = w64 (rg_src RG + RIG_HI_SRC) /\
GLIVE_xR B PST ARx RG R cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots RG cx F W1 m1 /\
GTOPM cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 W1 m1 /\
gtop_bud cx e1 c1' O1 cap1 i ly1 S1 spent.
End wR.

End c.
End b.
End a.
