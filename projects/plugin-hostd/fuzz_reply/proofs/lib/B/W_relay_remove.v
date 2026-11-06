(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASSEMBLY of the IMAGE-B walk of fuzz_reply's relay_remove
   (fuzz_reply.asan-ubsan 0x841fc): pb_relay_remove : rr_spec, from the segment statements of
   lib/B/W_relay_remove_cx.v composed by W_rr_all.v rr_all.  Applied: W_rr_pro.v rr_pro, W_rr_tail.v rr_tail.  Open,
   as Section hypotheses named for their statements until they land: SCAN / SCANS (a Theorem Labs lane, lib/B/W_rr_scan.v);
   MATCH is W_rr_match.v rr_match.  WAKE is a Theorem Labs lane's W_wake.v pb_wake.
   The Section block is regenerated from the cx file whenever the cx file changes. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record)) in the room form,
   lane RRX, the image-A twin's (a Theorem Labs lane, commit f4cd818e98d, lib/A/W_relay_remove.v Section c), IN PLACE:
   pb_relay_remove_x : rr_spec_x over ANY allocator relation ARx with its laws (W_contract_x.v, at RR_STK_x), from the
   generic segments composed by W_rr_all.v rr_all.  The AR theorem pb_relay_remove and its Section are deleted
   (a Theorem Labs lane 10:34Z: no consumer; the B top takes rr_spec_x as a hypothesis).  The Section is the cx file's generic
   block with WAKE built here from W_wake_x.v pb_wake_x (wake's own hypotheses are this Section's LAWS / TL / TLF / WFx /
   WFL / SFREE / SMALLOC / OWNLOW / IMGC / ASMP / ASF / FFL and the B-only HV8 / HWK / HERRS, W_wake.v's texts). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_remove_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rr_all.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_rr_pro W_rr_tail W_rr_match W_rr_scan W_wake_x.
(* route R (the Section wR below): SRrG, the R contracts of drain / gestures_end (a Theorem Labs lane) and of relay_remove
   (a Theorem Labs lane), and the R twins of the segments *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_relayB W_rr_match_cx.
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
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (one table for free and free(NULL); image B's closed singleton row:
   relay_remove keeps no frame pointer, so its free at 0x8435c has the trace [0x84360], K0's B CTX_AFREE row,
   lib/B/YCk0.v:19; rr_spec_x's last premise `In [pc + 356] CTX_AFREE`) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses (W_relay_remove_cx.v's generic block; WAKE is built below). ---- *)
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
(* the program functions relay_remove calls: drain, gestures_end (the kit's _x specs) *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x8435c with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
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
(* B only: wake (tail-called at 0x843e8; image A inlines it).  Its contract is W_wake_x.v pb_wake_x over this ARx;
   its own hypotheses beyond the Section's above, W_wake.v:113-129's texts: HV8 (g_wake's placement, A_OBJ 8 of
   lib/B/W_listing.v; PB_fr by W_wake_x.v wk_hv8_fr), HWK (g_wake[1]'s bytes are image bytes, not the runtime's owned
   statics, not errno), HERRS (errno is not one of the runtime's owned statics). *)
Hypothesis HV8 : VAL (A_OBJ 8) = rg_wake RG.
Hypothesis HWK : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HERRS : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
Let WAKE : wk_spec_x B PST ARx RG (BASE + AF_fr_wake) :=
  W_wake_x.pb_wake_x B PST ARx RG LAWS TL TLF WFx WFL SFREE SMALLOC OWNLOW IMGC ASMP ASF FFL HV8 HWK HERRS.

(* THE GENERIC WALK: the segments over ARx give rr_spec_x. *)
Theorem pb_relay_remove_x : rr_spec_x B PST ARx MT RP MMAX RG CTX_AFREE A_rr_entryP.
Proof.
apply (rr_all B PST ARx MT RP MMAX RG CTX_AFREE).
- eapply W_rr_pro.rr_pro; eassumption.
- eapply W_rr_scan.rr_scan; eassumption.
- eapply W_rr_scan.rr_scans; eassumption.
- eapply W_rr_match.rr_match; eassumption.
- eapply W_rr_tail.rr_tail; eassumption.
Qed.

(* ---- ROUTE R (a Theorem Labs lane's route-R lift crew, group G8b-relayrm-B; G4's form): census rows :122 AFREE -> AFREE_R,
   :126 DRAIN -> DRAIN_R, :127 GSE -> GSE_R, :129 AFREEN -> AFREEN_R, :152 pb_relay_remove_x -> pb_relay_remove_xR.
   relay_remove's contract at a world relation R (W_contract_xR_relayB.v rr_spec_xR), from the segments at R composed by
   W_rr_all.v rr_all_xR.  The Section block is W_relay_remove_cx.v's Section wR; WAKE stays the strict wake contract
   built above (wake frees nothing).  The callees free through CTX_AFREE, so drain / gestures_end / free enter at R
   (DRAIN_R / GSE_R / AFREE_R / AFREEN_R), never through their strict forms.  Applied: W_rr_pro.v rr_pro_xR,
   W_rr_scan.v rr_scan_xR / rr_scans_xR, W_rr_match.v rr_match_xR (over the four hops' twins W_rr_m_drain / _ge /
   _free / _cpy.v), W_rr_tail.v rr_tail_xR.  No segment premise is left. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* the R free rules' call-boundary premise RO, from the journal's ARx at the call state (part 3c removed their memnorm
   premise) *)
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
(* :122 AFREE at R *)
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* :126 DRAIN, :127 GSE at R (W_contract_xR.v) *)
Hypothesis DRAIN_R : dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE_R : gse_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* :129 AFREEN at R *)
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.

(* :152 THE GENERIC WALK AT R: the segments at R give rr_spec_xR. *)
Theorem pb_relay_remove_xR : rr_spec_xR B PST ARx R MT RP MMAX RG CTX_AFREE A_rr_entryP.
Proof.
apply (rr_all_xR B PST ARx MT RP MMAX RG CTX_AFREE R).
- eapply W_rr_pro.rr_pro_xR; eassumption.
- eapply W_rr_scan.rr_scan_xR; eassumption.
- eapply W_rr_scan.rr_scans_xR; eassumption.
- (* RO by name *)
  eapply W_rr_match.rr_match_xR with (RO := RO); eassumption.
- eapply W_rr_tail.rr_tail_xR; eassumption.
Qed.
End wR.
End c.
End b.
End a.
