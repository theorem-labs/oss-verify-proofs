(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the source that fuzz_reply's op_add opens (fuzz_reply.c:573-594), as the
   ASan representation lib/B/W_rep.v asrc_at states it (image B, fuzz_reply.asan-ubsan); a pure-memory lemma the
   walk of lib/B/W_op_add.v uses.  Image-independent: lib/A/W_op_add_src.v (a working branch e412cf890aa) over
   the B kit. *)
(* After op_add's stores, the slot g_s[i] at HA holds the descriptor fd, open = 1, the pointer q of the
   6000-byte partial buffer, and zero everywhere else (source_reset's memset).  Then asrc_at holds of the
   source HS fd 1 0 0 empty_list 0 q pj 0 0 [] empty_list empty_list, where pj is whatever q's block holds:
   its bytes are present (AR_blocks_law, Reusable/YG0d.v:435), so Reusable/YI00.v garr8_of_present names them.
   Section hypothesis: the allocator laws LAWS (for AR_blocks_law). *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane's route (b), step 3): proved once over the generic allocator relation ARx
   (oa_new_src_at_x, from AR_laws_x's block law alx_blocks); oa_new_src_at (statement unchanged) is its corollary at
   ARx := ARi0 (cgif's AR with the head set empty), with the laws at ARi0 (LX0) in place of AR_laws.  Image A's
   conversion (lib/A/W_op_add_src.v, a working branch 6cad466fd5b) carried onto image B's file. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d YI00 YN0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_journal W_rep W_contract
W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gestures_end_b_c.
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

(* a byte string read as values 0..255 is the bzs of its bytes (lib/A/W_list_push.v lp_bzs_map) *)
Lemma oas_bzs_map : forall jz : list Z, Forall (fun b => 0 <= b < 256) jz -> bzs (map (Z_to_bv 8) jz) = jz.
Proof.
induction jz as [|b jz IH]; intros HF; [reflexivity|]. apply Forall_cons_iff in HF as [Hb HF].
unfold bzs in *. cbn [map]. rewrite (IH HF). f_equal. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_small. exact Hb.
Qed.

(* struct list at LA, all 16 bytes zero and writable: the empty list *)
Lemma oas_alist_empty : forall ly S (W : world SEGS) mem LA lines,
  val_mem SEGS (arm W mem) LA 8 0 -> val_mem SEGS (arm W mem) (LA + 8) 4 0 ->
  val_mem SEGS (arm W mem) (LA + 12) 4 0 -> awr W mem LA 16 ->
  alist_at B ly S W mem LA empty_list lines.
Proof.
intros ly S W mem LA lines H0 H8 H12 HW. unfold alist_at, empty_list, hl_n.
cbn [hl_v hl_cap hl_recs hl_junk length map Z.of_nat].
split; [exact H0|]. split; [exact H8|]. split; [exact H12|]. split; [exact HW|].
split; [lia|]. split; [left; split; reflexivity|].
split; [constructor|]. split; [intros []|]. constructor.
Qed.

Local Ltac oas_in := repeat (first [left; reflexivity | right]).

(* the source, over the generic allocator relation ARx (only the block law alx_blocks is read) *)
Section x.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Lemma oa_new_src_at_x : forall ly S Hp (W : world SEGS) mem md HA fd q, ARx ly S Hp W mem md -> In (q, APARTIAL) (ablocks B ly S) -> 0 <= fd < 2^31 -> awr W mem HA ASRC -> val_mem SEGS (arm W mem) HA 4 fd -> val_mem SEGS (arm W mem) (HA+4) 4 1 -> val_mem SEGS (arm W mem) (HA+40) 8 q -> Forall (fun p => val_mem SEGS (arm W mem) (HA + fst p) (snd p) 0) [(8,4%nat);(12,4%nat);(16,8%nat);(24,4%nat);(28,4%nat);(32,8%nat);(48,8%nat);(56,4%nat);(64,8%nat);(72,4%nat);(76,4%nat);(80,8%nat);(88,4%nat);(92,4%nat)] -> exists pj, asrc_at B ly S W mem HA (HS fd 1 0 0 empty_list 0 q pj 0 0 [] empty_list empty_list).
Proof.
intros ly S Hp W mem md HA fd q HAR Hq Hfd HW V0 V4 V40 HZ.
assert (VZ : forall o n, In (o, n) [(8,4%nat);(12,4%nat);(16,8%nat);(24,4%nat);(28,4%nat);(32,8%nat);(48,8%nat);
  (56,4%nat);(64,8%nat);(72,4%nat);(76,4%nat);(80,8%nat);(88,4%nat);(92,4%nat)] ->
  val_mem SEGS (arm W mem) (HA + o) n 0)
  by (intros o n Hin; rewrite Forall_forall in HZ; exact (HZ (o, n) Hin)).
clear HZ.
assert (HWs : forall o n, 0 <= o -> o + n <= ASRC -> awr W mem (HA + o) n).
{ intros o n Ho Hn i Hi. replace (HA + o + i) with (HA + (o + i)) by lia.
  exact (HW (o + i) ltac:(unfold ASRC in *; lia)). }
(* the bytes of q's block: present, so some byte string pj *)
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md q APARTIAL HAR Hq) as (_ & _ & _ & _ & Hpr & _).
assert (Rq : req_size APARTIAL = APARTIAL) by reflexivity.
rewrite Rq in Hpr.
destruct (garr8_of_present SEGS (arm W mem) q (Z.to_nat APARTIAL)) as (jz & Hlen & Hg).
{ intros a Ha. rewrite Z2Nat.id in Ha by (unfold APARTIAL; lia).
  destruct (Hpr a Ha) as ((Hh & b & Hb) & _).
  exists b. unfold arm, mrestrict. rewrite Hh. exact Hb. }
assert (HjF : Forall (fun b => 0 <= b < 256) jz) by exact (garr8_bytes_ok SEGS _ _ _ Hg).
exists (map (Z_to_bv 8) jz).
unfold asrc_at.
cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad
  hs_expected hs_held].
split; [exact V0|].
split; [exact V4|].
split; [exact (VZ 8 4%nat ltac:(oas_in))|].
split; [exact (VZ 12 4%nat ltac:(oas_in))|].
split; [exact HW|].
split; [left; reflexivity|].
split; [left; reflexivity|].
split; [reflexivity|].
split; [exact Hfd|].
split.
{ apply oas_alist_empty.
  - exact (VZ 16 8%nat ltac:(oas_in)).
  - replace (HA + 16 + 8) with (HA + 24) by lia. exact (VZ 24 4%nat ltac:(oas_in)).
  - replace (HA + 16 + 12) with (HA + 28) by lia. exact (VZ 28 4%nat ltac:(oas_in)).
  - apply HWs; unfold ASRC; lia. }
split; [exact (VZ 32 8%nat ltac:(oas_in))|].
split; [exact V40|].
split; [exact (VZ 48 8%nat ltac:(oas_in))|].
split; [exact (VZ 56 4%nat ltac:(oas_in))|].
split; [left; split; reflexivity|].
split; [unfold APARTIAL; lia|].
split; [left; reflexivity|].
split; [exact Hq|].
split; [rewrite length_map, Hlen; apply Z2Nat.id; unfold APARTIAL; lia|].
split; [rewrite (oas_bzs_map jz HjF); exact Hg|].
split; [unfold hs_W; intros []|].
split.
{ apply oas_alist_empty.
  - exact (VZ 64 8%nat ltac:(oas_in)).
  - replace (HA + 64 + 8) with (HA + 72) by lia. exact (VZ 72 4%nat ltac:(oas_in)).
  - replace (HA + 64 + 12) with (HA + 76) by lia. exact (VZ 76 4%nat ltac:(oas_in)).
  - apply HWs; unfold ASRC; lia. }
split.
{ apply oas_alist_empty.
  - exact (VZ 80 8%nat ltac:(oas_in)).
  - replace (HA + 80 + 8) with (HA + 88) by lia. exact (VZ 88 4%nat ltac:(oas_in)).
  - replace (HA + 80 + 12) with (HA + 92) by lia. exact (VZ 92 4%nat ltac:(oas_in)).
  - apply HWs; unfold ASRC; lia. }
unfold hs_blocks, list_blocks, empty_list.
cbn [hs_pending hs_partial hs_expected hs_held hl_cap hl_v hl_recs map app Z.eqb].
(* hs_blocks's NoDup is stdpp's (x ∉ l is an inductive membership), so the singleton case goes by inversion *)
first [apply NoDup_singleton | constructor; [intros Hin; inversion Hin | constructor]].
Qed.
End x.

(* re-derived at ARx := ARi0 (= AR /\ Hp = []): the laws at ARi0 in place of AR_laws *)
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Lemma oa_new_src_at : forall ly S (W : world SEGS) mem md HA fd q, AR SEGS B ly S W mem md -> In (q, APARTIAL) (ablocks B ly S) -> 0 <= fd < 2^31 -> awr W mem HA ASRC -> val_mem SEGS (arm W mem) HA 4 fd -> val_mem SEGS (arm W mem) (HA+4) 4 1 -> val_mem SEGS (arm W mem) (HA+40) 8 q -> Forall (fun p => val_mem SEGS (arm W mem) (HA + fst p) (snd p) 0) [(8,4%nat);(12,4%nat);(16,8%nat);(24,4%nat);(28,4%nat);(32,8%nat);(48,8%nat);(56,4%nat);(64,8%nat);(72,4%nat);(76,4%nat);(80,8%nat);(88,4%nat);(92,4%nat)] -> exists pj, asrc_at B ly S W mem HA (HS fd 1 0 0 empty_list 0 q pj 0 0 [] empty_list empty_list).
Proof.
intros ly S W mem md HA fd q HAR.
exact (oa_new_src_at_x (ARi0 SEGS B) LX0 ly S [] W mem md HA fd q (conj HAR eq_refl)).
Qed.

End c.
End b.
End a.
