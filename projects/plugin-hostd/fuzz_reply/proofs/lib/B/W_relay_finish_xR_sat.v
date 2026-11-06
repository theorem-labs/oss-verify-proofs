(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's
   relay_finish, a NEW walk over lib/B/W_listing.v (B's body is not A's up to relocation: VERDICT.md (sha256 810ca1df9ca9; internal record)),
   after lib/A/W_relay_finish_h.v (a working branch a3987bff22c: its loop rf_loop and its tail rf_tail), in the
   form of the B walks lib/B/W_check_bounded.v (a working branch 7e062bb9b9c) and lib/B/W_gse_loop.v
   (a working branch bb5ed8a0689). *)
(* Modified by Theorem Labs, 2026-10: the room `_x` form (a Theorem Labs lane, RoomRFB): the walk is pb_relay_finish_x,
   stated over any allocator relation ARx with its laws as W_contract_x.v rf_spec_x (Section c below: PST / ARx / hl /
   LAWS / HP0 / BLKN, the callees' and the allocator rules' `_x` twins, PSTR / PSTC), and it threads rf_spec_x's room
   round: the budget rp_RM RP (each round: the free's 1, then gestures_end's charge) and the count premise
   cnt_ok_pk RP rf_pk (rf_pk = 5) to the free (cnt_ok) and to gestures_end (gse_pk = 4); the round's room bound follows
   rf_room's `- cap` threading (the round frees the old g_out block).  The room argument is lib/A/W_relay_finish_h.v's
   (a working branch 9e4f84a8fb9), the ARx form that of lib/B/W_list_free.v / W_source_reset.v
   (a working branch dfa1a225350).
   B's relay_finish sets no frame pointer and calls no __asan_stack_malloc, so A's fake-frame seat, its set_fs step and rp_RPF across the seat do not apply.
   pb_relay_finish keeps its statement, byte-identical, and its Section hypotheses (the same terms in the same order;
   HPLAIN / HWSEG write rf_cells as rf_cells RG GTU GL): it is re-derived from pb_relay_finish_x at ARx := ARi0,
   PST := [], RP := RP_AR (Section cAR); pb_relay_finish_fr / _fr_tfib are unchanged. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_relay_finish.v, with its module names changed; 25 of its 109 lines of code are new or changed and 4259 lines of the source are left out. *)
(* Satisfiability at the real image B of the R contract texts (W_contract_xR.v), at R := wle' SEGS RZ_cf: each
   lemma derives the R form from the existing strict walk, under that walk's own Section hypotheses. The import block
   is the walk file's (W_relay_finish.v), so each hypothesis reads as there. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State
Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15
YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06
YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a YP07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq
YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_contract W_rep
W_journal W_sites W_frame W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_relay_finish.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.

(* pb_relay_finish_xR_sat: rf_spec_xR at R := wle' SEGS RZ_cf, from W_relay_finish.pb_relay_finish_x by rf_spec_xR_of_x and YA0nH.wle_wle'. The Section
   hypotheses are pb_relay_finish_x's own (W_relay_finish.v, Sections a / b / c), unchanged; their comments are left out. *)
Section sat.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable RG : rep_globals.
Variable GTU GL : Z.
Variable CTX : list (list Z).
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis TL : PALib B.
Hypothesis MLAW : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AFREE0 : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
Hypothesis HV1 : VAL (A_OBJ 1) = GTU.
Hypothesis HV3 : VAL (A_OBJ 3) = rg_lock RG.
Hypothesis HV4 : VAL (A_OBJ 4) = rg_nsrc RG.
Hypothesis HV5 : VAL (A_OBJ 5) = rg_src RG.
Hypothesis HH5 : VAL (A_HI 5) + (-1672) = rg_nsrc RG.
Hypothesis HH7 : VAL (A_HI 7) + 292 = rg_client RG.
Hypothesis HH8 : VAL (A_HI 8) + 248 = GL.
Hypothesis HIG : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0x5fc000)
[(GTU, 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4); (GL, 4)].
Hypothesis HSEPG : zseps
[(VAL (A_OBJ 0), 8); (VAL (A_OBJ 30), 8);
 (GTU, 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4); (GL, 4);
 (as_errno B, 4)].
Let rf_cells : list (Z * Z) :=
[(GTU, 1); (rg_lock RG, 12); (rg_nsrc RG, 4); (rg_src RG, 8); (rg_capsrc RG, 4); (rg_client RG, 4); (GL, 4)].
Hypothesis HPLAIN : forall a, inG rf_cells a ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HWSEG : forall a, inG rf_cells a -> wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None.
Hypothesis RGAL : rg_lock RG mod 4 = 0.
Hypothesis HIGO : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0x5fc000)
[(rg_send_max RG, 8); (rg_nout RG, 8); (rg_capout RG, 8); (rg_out RG, 8);
 (rg_client_broken RG, 1); (rg_send_dead RG, 1); (rg_send_eintr RG, 1)].
Hypothesis HSEPO : zseps
[(rg_lock RG, 12); (rg_nsrc RG, 4); (rg_client RG, 4); (GL, 4);
 (rg_send_max RG, 8); (rg_nout RG, 8); (rg_capout RG, 8); (rg_out RG, 8);
 (rg_client_broken RG, 1); (rg_send_dead RG, 1); (rg_send_eintr RG, 1); (as_errno B, 4);
 (rg_src RG, 8); (rg_capsrc RG, 4)].
Hypothesis HPLAINO : forall a,
(rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HROMG : forall a,
inG (RF_G RG GL) a \/ inG (G_SL B RG) a \/
(rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_send_dead RG <= a < rg_send_dead RG + 1) ->
~ in_rom SEGS a.
Hypothesis HE5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + Z.of_nat (length END5) -> in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HWSEGE : forall a, as_errno B <= a < as_errno B + 4 ->
wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None.
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTC : forall a, inG rf_cells a -> ~ Exists (in_zr a) PST.
Theorem pb_relay_finish_xR_sat :
  rf_spec_xR B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) MT RP MMAX G RG GTU GL CTX (BASE + AF_fr_relay_finish).
Proof.
apply rf_spec_xR_of_x; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) |].
eapply W_relay_finish.pb_relay_finish_x; eassumption.
Qed.
End sat.
