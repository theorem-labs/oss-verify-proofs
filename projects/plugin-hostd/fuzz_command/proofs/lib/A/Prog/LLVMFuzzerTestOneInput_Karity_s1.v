(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the reader transports of segment K's check_arity step of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86948 .. jal check_arity at 0x8694c): the cut facts (lt_saved, lt_slots, lt_kregs, lt_words, lt_rec of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v and _Kcut.v) kept by a reader that agrees on the frame, the live blocks and the program statics, an 8-byte word read as the recorder vocabulary's field, and the budget after a call of no event; in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh4.v (cl_vkept: the values kept across a call) and lib/A/Prog/PaCallPg.v (rec_repA_kept). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo CmdGlob PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_clear_c send_message_c check_reply_c
  check_arity_c check_words_c check_refusal_c check_round_trip_c verbs_receive_c LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_Kcut.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* an 8-byte word read through the ASan view is the 8-byte field the recorder's vocabulary reads *)
Lemma lt_rdword_aval8_loc : forall (segs : list Segment) H mem a v,
  rdword (aview segs H mem) a = Some v -> aval_mem (aview segs H mem) a 8 v.
Proof.
intros segs H mem a v E k Hk.
pose proof (val_mem_of_rdword segs H mem a v E k Hk) as Hb.
unfold aview. rewrite Hb. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte, YG0f.le_byte.
apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.

(* a word read through a reader that agrees on its 8 bytes *)
Lemma lt_rdword_kept_loc : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros j Hj. apply HK. lia. Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the registers the entry saved, in its frame [sp1, sp0) *)
Lemma lt_saved_kept_loc : forall (cx : lcx) (rd rd' : reader),
  (forall x, x_sp1 cx <= x < x_sp0 cx -> rd' x = rd x) -> lt_saved cx rd -> lt_saved cx rd'.
Proof.
intros cx rd rd' HK H i r Hi.
assert (Hl : (i < length LT_SAVED)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
change (length LT_SAVED) with 13%nat in Hl.
apply (lt_rdword_kept_loc rd); [|exact (H i r Hi)].
intros x Hx. apply HK. unfold x_sp1, x_sp0, LT_FRAME in *. lia.
Qed.

(* the eleven words below the struct *)
Lemma lt_slots_kept_loc : forall (cx : lcx) (rd rd' : reader),
  (forall x, x_sp1 cx <= x < x_sp0 cx -> rd' x = rd x) -> lt_slots cx rd -> lt_slots cx rd'.
Proof.
intros cx rd rd' HK H o v Hin.
assert (Ho : 0 <= o <= 80).
{ pose proof Hin as Hin'. unfold LT_SLOTS in Hin'. cbn [In] in Hin'.
  repeat (destruct Hin' as [Hq|Hin']; [injection Hq as Eo _; lia|]). destruct Hin'. }
apply (lt_rdword_kept_loc rd); [|exact (H o v Hin)].
intros x Hx. apply HK. unfold x_sp1, x_sp0, LT_FRAME in *. lia.
Qed.

(* the message registers and the two frame words of segment K's cuts *)
Lemma lt_kregs_kept_loc : forall (cx : lcx) (regs regs' : bvmap 5 word) (rd rd' : reader) m r Rh,
  aregs_preserved regs regs' ->
  (forall x, x_sp1 cx <= x < x_sp0 cx -> rd' x = rd x) ->
  lt_kregs cx regs rd m r Rh -> lt_kregs cx regs' rd' m r Rh.
Proof.
intros cx regs regs' rd rd' m r Rh HP HK (H0 & H19 & H20 & H26 & H27 & Hh & Hs).
split; [exact H0|].
split; [exact (eq_trans (HP 19 ltac:(unfold acallee_saved; lia)) H19)|].
split; [exact (eq_trans (HP 20 ltac:(unfold acallee_saved; lia)) H20)|].
split; [exact (eq_trans (HP 26 ltac:(unfold acallee_saved; lia)) H26)|].
split; [exact (eq_trans (HP 27 ltac:(unfold acallee_saved; lia)) H27)|].
split.
- apply (lt_rdword_kept_loc rd); [|exact Hh]. intros x Hx. apply HK. unfold x_sp1, x_sp0, LT_FRAME, LT_HOSTB in *. lia.
- apply (lt_rdword_kept_loc rd); [|exact Hs]. intros x Hx. apply HK. unfold x_sp1, x_sp0, LT_FRAME, LT_STATEB in *. lia.
Qed.

(* the words of the message: the struct in the frame, the pointer array and the copy block *)
Lemma lt_words_kept_loc : forall (cx : lcx) (regs regs' : bvmap 5 word) (rd rd' : reader) (D : list byte)
  (ws : list (list byte)) text copy arr (wp : list Z),
  aregs_preserved regs regs' ->
  (forall x, x_sp1 cx <= x < x_sp0 cx -> rd' x = rd x) ->
  (forall x, arr <= x < arr + SlotSpec.arr_size (StrFun.strnlen_res (Z.of_nat (length D)) D) -> rd' x = rd x) ->
  (forall x, copy <= x < copy + StrFun.strnlen_res (Z.of_nat (length D)) D + 1 -> rd' x = rd x) ->
  8 * Z.of_nat (length ws) <= SlotSpec.arr_size (StrFun.strnlen_res (Z.of_nat (length D)) D) ->
  lt_words cx regs rd D ws text copy arr wp -> lt_words cx regs' rd' D ws text copy arr wp.
Proof.
intros cx regs regs' rd rd' D ws text copy arr wp HP HK HKa HKc Hws HW.
destruct HW as (R24 & R23 & R25 & WT & WC & WA & WN & WL & WP & WS).
unfold lt_words. cbv zeta.
split; [exact (eq_trans (HP 24 ltac:(unfold acallee_saved; lia)) R24)|].
split; [exact (eq_trans (HP 23 ltac:(unfold acallee_saved; lia)) R23)|].
split; [exact (eq_trans (HP 25 ltac:(unfold acallee_saved; lia)) R25)|].
split; [apply (lt_rdword_kept_loc rd); [intros x Hx; apply HK; unfold x_sp1, x_sp0, LT_FRAME, LT_W in *; lia | exact WT]|].
split; [apply (lt_rdword_kept_loc rd); [intros x Hx; apply HK; unfold x_sp1, x_sp0, LT_FRAME, LT_W in *; lia | exact WC]|].
split; [apply (lt_rdword_kept_loc rd); [intros x Hx; apply HK; unfold x_sp1, x_sp0, LT_FRAME, LT_W in *; lia | exact WA]|].
split.
{ apply (aval_mem_kept_r rd); [|exact WN]. intros x Hx. apply HK.
  cbn [Z.of_nat Pos.of_succ_nat] in Hx. unfold x_sp1, x_sp0, LT_FRAME, LT_W in *. lia. }
split; [exact WL|].
split.
- intros i pt Hi. apply (lt_rdword_kept_loc rd); [|exact (WP i pt Hi)].
  assert (Hil : (i < length wp)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  rewrite WL in Hil. intros x Hx. apply HKa. lia.
- intros i pt w Hi Hw. destruct (WS i pt w Hi Hw) as (C1 & C2 & C3).
  split; [exact C1|]. split; [exact C2|].
  apply (astr_atR_kept_r rd); [|exact C3]. intros x Hx. apply HKc. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* the recorder between two passes, kept by a reader that agrees on the program statics and the live blocks *)
Lemma lt_rec_kept_loc : forall (cx : lcx) ly S (W W' : world SEGS) mem mem' R O q extra,
  (forall a, inFP cmd_PG a -> rdW W' mem' a = rdW W mem a) ->
  (forall p n x, In (p, n) (ablocks B ly S) -> p <= x < p + req_size n -> rdW W' mem' x = rdW W mem x) ->
  lt_rec B cx ly S W mem R O q extra -> lt_rec B cx ly S W' mem' R O q extra.
Proof.
intros cx ly S W W' mem mem' R O q extra KG KB (HR & H1 & H2 & HQ & RQ & HPm).
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. left. exact Hpn. }
split.
{ apply (rec_repA_kept B ly S (rdW W mem) ly S (rdW W' mem') R O HR HO).
  intros a [Ha | [Ha | Ha]].
  - apply KG. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity|].
    unfold REC_SIZE in Ha. cbn [fst snd]. lia.
  - apply KG. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity|].
    unfold SC_SIZE in Ha. cbn [fst snd]. lia.
  - destruct Ha as (rg & Hrg & Hin). unfold ablocks_fp in Hrg. apply in_map_iff in Hrg as ([p n] & Ep & Hpn).
    subst rg. cbn [fst snd] in Hin. exact (KB p n a (HO _ Hpn) Hin). }
split; [exact H1|]. split; [exact H2|].
split.
{ apply (aval_mem_kept_r (rdW W mem)); [|exact HQ]. intros x Hx. apply KG.
  exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; right; right; left; reflexivity|].
  cbn [Z.of_nat Pos.of_succ_nat fst snd] in *. lia. }
split; [exact RQ | exact HPm].
Qed.

(* the budget after a call of no event (EV_CHECK_ARITY = 0) *)
Lemma lt_bud_arity_loc : forall (cx : lcx) S k acc Y Z1,
  lt_bud MT cx S k acc (3 + EV_CHECK_ARITY + EV_CHECK_WORDS + EV_CHECK_REFUSAL + Y + Z1) ->
  lt_bud MT cx S (k + EV_CHECK_ARITY) acc (3 + EV_CHECK_WORDS + EV_CHECK_REFUSAL + Y + Z1).
Proof.
intros cx S k acc Y Z1 H. unfold EV_CHECK_ARITY in *. rewrite Z.add_0_r.
replace (3 + 0 + EV_CHECK_WORDS + EV_CHECK_REFUSAL + Y + Z1) with (3 + EV_CHECK_WORDS + EV_CHECK_REFUSAL + Y + Z1) in H
  by ring.
exact H.
Qed.

(* the events still allowed at a point of the budget *)
Lemma lt_nev_loc : forall (cx : lcx) S k acc rem,
  lt_bud MT cx S k acc rem -> st_nev S <= st_nev (x_S cx) + k -> st_nev (x_S cx) + EV_LTOI (x_pl cx) <= EV_MAX ->
  st_nev S + EV_CHECK_ARITY <= EV_MAX.
Proof. intros cx S k acc rem (H1 & H2 & H3 & _) H4 H5. unfold EV_CHECK_ARITY. lia. Qed.
End e.
End f.
End d.
