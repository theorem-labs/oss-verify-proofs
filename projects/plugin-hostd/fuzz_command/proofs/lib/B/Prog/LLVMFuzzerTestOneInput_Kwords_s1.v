(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the local facts of the check_words step of segment K of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86a1c addi a0,sp,120 .. 0x86a20 jal check_words): the three words blocks' sizes, the live bytes and the budget at the call, the callee-saved registers the two instructions keep, and the symbolic state at 0x86a1c with no region; the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_Kwords_s1.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (cl_seedX: the seed of a run with no region and no fact). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01
LLVMFuzzerTestOneInput_Kcut LLVMFuzzerTestOneInput_Karity_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Notation JN := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.joined_c.join_need.

(* the three words blocks of a message of at most 8192 bytes sum to at most LT_WORDSB *)
Lemma kw_wblocks_bsum_loc : forall D text copy arr,
  0 <= StrFun.strnlen_res (Z.of_nat (length D)) D <= 8192 -> bsum (lt_wblocks D text copy arr) <= LT_WORDSB.
Proof.
intros D text copy arr. unfold lt_wblocks, LT_WORDSB, SlotSpec.arr_size. cbv zeta.
generalize (StrFun.strnlen_res (Z.of_nat (length D)) D). intros L0 HL. cbn [bsum snd].
pose proof (Z.div_mod L0 2 ltac:(lia)). pose proof (Z.mod_pos_bound L0 2 ltac:(lia)). lia.
Qed.

(* the registers the two instructions to the call and the call itself keep: sp, gp, tp and s0 .. s11 *)
Definition kw_kept : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Ltac kw_in := unfold kw_kept; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]).
(* a state that keeps the registers of kw_kept keeps every callee-saved register *)
Lemma kw_pres_loc : forall (regs regs' : bvmap 5 word),
  (forall rr, In rr kw_kept -> getr regs' rr = getr regs rr) -> aregs_preserved regs regs'.
Proof.
intros regs regs' HK z Hz. apply HK. unfold acallee_saved in Hz.
assert (Hz' : z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ z = 18 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/
  z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by lia.
destruct Hz' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
  kw_in.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ---- the symbolic state at 0x86a1c (LO_K2): every register its own atom, no memory region (the two
   instructions to the call, addi a0,sp,120 and jal check_words, read and write no memory), no fact ---- *)
Definition kw_ss : sstate := mkSS LO_K2 sr_atoms [] None (mkFacts [] [] []).
Definition kw_Bx : sv := SLit 0x7fff8000.
Definition kw_span : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).
Lemma kw_seed_loc : forall (W : world SEGS) (regs : bvmap 5 word) mem,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) kw_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K2)) mem (seg_rom SEGS))) /\
  sh_ok SEGS kw_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem. split; [|constructor].
unfold kw_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn. exact I.
- cbn. repeat split.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.

(* the live bytes at the call: the entry's, the recorder's (at most LT_RECB), the three words blocks (at most
   LT_WORDSB) and joined's block at its peak fit LIVE_LTOI *)
Lemma kw_live_loc : forall cx ly S (W : world SEGS) mem md R O q D text copy arr,
  lt_base B MT cx -> AR SEGS B ly S W mem md -> lt_rec B cx ly S W mem R O q (lt_wblocks D text copy arr) ->
  0 <= StrFun.strnlen_res (Z.of_nat (length D)) D <= 8192 ->
  blocks_bytes S + LIVE_CHECK_WORDS <= LIVE_MAX.
Proof.
intros cx ly S W mem md R O q D text copy arr HBASE HAR HREC HL0.
pose proof HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLIVE0 & _).
pose proof (lt_rec_live B LAWS cx ly S W mem md R O q _ HAR HREC) as HLv.
pose proof (kw_wblocks_bsum_loc D text copy arr HL0) as Hwb.
pose proof (Z.le_max_l LIVE_CHECK_WORDS LIVE_CHECK_ROUND_TRIP) as Hx1.
pose proof (Z.le_max_r LIVE_SEND_MESSAGE (Z.max LIVE_CHECK_WORDS LIVE_CHECK_ROUND_TRIP)) as Hx2.
unfold LIVE_LTOI in HLIVE0. unfold LT_RECB in HLv. unfold LT_WORDSB in Hwb.
revert HLv Hwb HLIVE0 Hx1 Hx2.
generalize (Z.max LIVE_SEND_MESSAGE (Z.max LIVE_CHECK_WORDS LIVE_CHECK_ROUND_TRIP)).
generalize (Z.max LIVE_CHECK_WORDS LIVE_CHECK_ROUND_TRIP).
generalize (bsum (lt_wblocks D text copy arr)). intros. lia.
Qed.

(* the budget of the call: check_words' two events and its meter come out of the rest of LT_K2_stmt's budget, and
   what is left is LT_K3_stmt's *)
Lemma kw_bud_loc : forall cx ly S (W : world SEGS) mem md k acc ws RT F,
  lt_base B MT cx ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k ->
  JN ws + 1 <= 32784 -> 0 <= RT -> 0 <= F ->
  lt_bud MT cx S k acc (3 + EV_CHECK_WORDS + EV_CHECK_REFUSAL + RT + F) ->
  st_nev S + EV_CHECK_WORDS <= EV_MAX /\ mo_ok MT S (XM_CHECK_WORDS MT ws) /\
  forall S3, mo_le MT S S3 (XM_CHECK_WORDS MT ws) ->
  lt_bud MT cx S3 (k + EV_CHECK_WORDS) (acc + XM_CHECK_WORDS MT ws) (3 + EV_CHECK_REFUSAL + RT + F).
Proof.
intros cx ly S W mem md k acc ws RT F HBASE HJ Hj HRT HF HBUD.
pose proof (lt_nev_bud B MT cx ly S W mem md k acc _ HBASE HJ HBUD) as Hnev.
pose proof HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmo0).
pose proof HBUD as (Hk & Hrem & Hkr & Hmle & Hacc & Hax).
pose proof (xm_check_words_le MT MTL ws Hj) as HXW.
pose proof (LT_U_nonneg MT MTL) as HU.
assert (HX0 : 0 <= XM_CHECK_WORDS MT ws).
{ unfold XM_CHECK_WORDS, OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.joined_c.XM_JOINED.
  pose proof (join_need_ge0 ws) as Hj0.
  pose proof (mo_malloc_nonneg MT MTL (JN ws + 1) ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia. }
assert (EVW : EV_CHECK_WORDS = 2) by reflexivity.
assert (EVF : EV_CHECK_REFUSAL = 0) by reflexivity.
rewrite EVW, EVF in *.
unfold lt_bud.
set (U := LT_U MT) in *. set (XW := XM_CHECK_WORDS MT ws) in *.
clearbody U XW.
assert (HremU : (3 + 2 + 0 + RT + F) * U = 2 * U + (3 + 0 + RT + F) * U) by ring.
assert (H0U : 0 <= (3 + 0 + RT + F) * U) by (apply Z.mul_nonneg_nonneg; lia).
split; [lia|]. split.
{ apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc XW MTL Hmo0 Hmle); lia. }
intros S3 HML. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmle HML)|]. split; lia.
Qed.
End e.
End f.
End d.
