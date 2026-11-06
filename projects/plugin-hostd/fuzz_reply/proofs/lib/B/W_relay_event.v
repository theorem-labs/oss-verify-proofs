(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the image-B (asan-ubsan) walk of plugin-hostd's relay_event, ported from
   lib/A/W_relay_event.v (a working branch 26a1ccdf1c1), in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (runtime call sites) and lib/A/ACh2.v with lib/YC85.v cl_callS (the
   internal call), over lib/B/W_journal.v's ajournal_gx. *)
(* Modified by Theorem Labs, 2026-10-30 (a Theorem Labs lane, the B room re-fit onto kit candidate 13): the walk is
   lib/B/W_relay_event_x.v's pb_relay_event_x (G-BRE: relay_event over any allocator relation ARx at the room texts,
   lib/A/W_relay_event.v fc38e83bfbf / 922a710cda0 / 88557c15170 / 9f5567c9e80 on image B), the one generic walk;
   this file's own copy of it is removed.  What stays is the AR statement: pb_relay_event, re_spec's text
   (lib/B/W_contract.v), as that walk's corollary at ARx := ARi0, PST := [], RP := RP_AR (Section cAR). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_journal W_contract W_sites W_rep W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
(* the walk: Require only, cited qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_relay_event_x.
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
(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_relay_event's statement is
   re_spec's (lib/B/W_contract.v), byte-identical, a corollary of W_relay_event_x.pb_relay_event_x at ARx := ARi0
   (cgif's AR with the head set empty), PST := [], RP := RP_AR.  Its Section takes LX0 (the laws at ARi0, a Theorem Labs lane's
   rulings (a) and HP0) in place of LAWS: the instance builds it once, W_journal_x.AR_laws_x_ARi0
   (YCbqG.AR_laws_x_of_AR ..).  Bridges: W_contract_x re_spec_x_AR0 (the conclusion; it discharges the room premises at
   RP_AR), sl_spec_x_of_AR0 / astrlen_realizes_x_of_AR0 and W_sites_x alock_realizes_x_of_AR0 /
   aunlock_realizes_x_of_AR0 (the callees); HP0 at ARi0 is ARi0_hp0; the walk's BLKM is AR_blkm below and its HLPST
   holds at PST = [].  (lib/A's Section cAR, fc38e83bfbf / 9f5567c9e80, on image B.) ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable RG : rep_globals.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis SL : @sl_spec fx rc SK PI B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis ALOCK : alock_realizes B (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes B (SIGMA WS_pthread_mutex_unlock).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
(* placement: g_lock is the listing's object 3 (the auipc/addi pair at 0x82818; A: object 6), its address is
   4-aligned (the mutex entries need it; the listing does not fix the addi offset), and its 12 bytes are apart from
   send_line's globals (send_line's journal may change every byte of G_SL). *)
Hypothesis HV3 : VAL (A_OBJ 3) = rg_lock RG.
Hypothesis HLA : rg_lock RG mod 4 = 0.
Hypothesis HLD : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ inG (G_SL B RG) a.
(* g_lock is in a writable segment: its bytes are not read-only image bytes.  Needed to carry the walk's rom_view
   past the mutex's write of the lock word. *)
Hypothesis HLRW : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ in_rom SEGS a.
(* and apart from the three output globals that are not in G_SL (G_SL's six are HLD's) *)
Hypothesis HAOD : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
  ~ (rg_send_max RG <= a < rg_send_max RG + 8) /\ ~ (rg_client RG <= a < rg_client RG + 4) /\
  ~ (rg_send_dead RG <= a < rg_send_dead RG + 1).
(* the same three cells lie in image B's band [0x10000, 0x5fc000) (the other six of aout_fp are G_SL's, hence image
   bytes by gx_ok) *)
Hypothesis HAO3 : (0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fc000) /\
  (0x10000 <= rg_client RG /\ rg_client RG + 4 <= 0x5fc000) /\
  (0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= 0x5fc000).
Lemma AR_blkm : forall ly S (Hp : list Z) (W : world SEGS) mem md p n, ARi0 SEGS B ly S Hp W mem md ->
In (p, n) (ablocks B ly S) -> 0 <= n < 2 ^ 30.
Proof.
intros ly S Hp W mem md p n ((M & _ & _) & _) Hin. apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn).
pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _). rewrite Hn in G7. unfold MALLOC_MAX in G7. lia.
Qed.
Theorem pb_relay_event : @re_spec fx rc SK PI B MT MMAX G RG (BASE + AF_fr_relay_event).
Proof.
apply re_spec_x_AR0.
pose proof AR_blkm as BLKM.
assert (HLPST : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ Exists (in_zr a) ([] : list (Z * Z)))
  by (intros a _ Hx; inversion Hx).
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (SLx : sl_spec_x B [] (ARi0 SEGS B) MT RP_AR MMAX RG (BASE + AF_fr_send_line)) by (apply sl_spec_x_of_AR0; exact SL).
assert (ALx : alock_realizes_x B (ARi0 SEGS B) (SIGMA WS_pthread_mutex_lock)) by (apply alock_realizes_x_of_AR0; exact ALOCK).
assert (AUx : aunlock_realizes_x B (ARi0 SEGS B) (SIGMA WS_pthread_mutex_unlock)) by (apply aunlock_realizes_x_of_AR0; exact AUNLOCK).
assert (ASx : astrlen_realizes_x B (ARi0 SEGS B) (SIGMA WS_strlen)) by (apply astrlen_realizes_x_of_AR0; exact ASTRLEN).
eapply W_relay_event_x.pb_relay_event_x; eassumption.
Qed.
End cAR.
End b.
End a.
Print Assumptions pb_relay_event.
