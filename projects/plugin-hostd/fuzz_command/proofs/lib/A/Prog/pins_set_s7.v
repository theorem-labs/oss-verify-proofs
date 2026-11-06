(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the steps of pins_set's ASan walk between two calls of xstrdup, after
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh3.v .. ACh6.v (cgif_close's segments between its calls) over fuzz_command's
   recorder slot. *)

(* `ps_store`: the store of the j-th copy into the slot (nargs := j, args[j - 1] := p) keeps the walk's invariant.
   `ps_seg_x` (j = 1 .. 3): from the return of the j-th xstrdup to the call of the (j + 1)-th: the instrumented
   checks on the slot's nargs word and argument word (both bytes marked usable, so the error path is not reached),
   the two stores, the test of the next argument against 0 and the default literal. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c mix_call_c answer_code_c pins_set_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas pins_set_s2 pins_set_s1 pins_set_s3 pins_set_s5 pins_set_s6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma ps_aval_mod : forall rd a n v, aval_mem rd a n v -> aval_mem rd a n (v mod 2 ^ (8 * Z.of_nat n)).
Proof.
intros rd a n v H k Hk. rewrite (H k Hk). unfold le_byte. rewrite Zmod_mod. reflexivity.
Qed.

Lemma ps_rec_record_scalars : forall X f A,
r_refuse (rec_record X f A) = r_refuse X /\ r_code (rec_record X f A) = r_code X /\
r_state (rec_record X f A) = r_state X /\ r_answer (rec_record X f A) = r_answer X.
Proof. intros X f A. unfold rec_record. destruct (Nat.ltb _ _); destruct X; repeat split. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a byte outside every writable range of a run's start state is kept *)
Lemma ps_rd_frame : forall E rs (H : word -> bool) m m' a, frame_of E rs m m' -> 0 <= a < 2 ^ 64 ->
~ in_wrange E rs a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a Hfr Ha Hn. unfold aview, YP09.mbyte, mrestrict.
destruct (H (Z_to_bv 64 a)); [reflexivity|]. rewrite Hfr; [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
#[local] Notation LAWS := (AR_laws_ok SEGS B).

Section entry.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (pu pf pl pv : Z) (uri files layout verdict : option (list byte)) (R : rstate)
  (O : list (Z * Z)).
Hypothesis HPRE : afn_pre SEGS B PINS_SET_STK ly S W regs mem md ch.

#[local] Notation sp0 := (ps_sp0 regs).
#[local] Notation FPps := (ps_FP O).
#[local] Notation A := (ps_A uri files layout verdict).
#[local] Notation PTRS := (ps_ptrs pu pf pl pv uri files layout verdict).
#[local] Notation CORE := (ps_core B MT ly S W regs mem md uri files layout verdict R O).
#[local] Notation KEEP := (ps_keep B regs pf pl pv R).
#[local] Notation POST := (ps_post B MT ly S W regs mem md uri files layout verdict R O).

Lemma ps_sp0_facts : 2 ^ 46 <= sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0 /\ alloc_ceiling + 80 <= sp0.
Proof.
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold ps_sp0. unfold PINS_SET_STK, REC_CALLS_FREE_STK, XSTRDUP_STK, MIX_CALL_STK, ANSWER_CODE_STK, HAND_BACK_STK,
  ASTACK, ESTACK in *.
change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328. lia.
Qed.

(* the walk's slot, from the invariant *)
Lemma ps_core_slot : forall P Pn lyc Sc Wc memc mdc k, CORE P Pn lyc Sc Wc memc mdc k ->
0 <= ps_n R <= 16 /\ ps_slot_ok (ps_c R) /\
((A_G_REC + OFF_CALLS <= ps_c R /\ ps_c R + CALL_SIZE <= A_G_REC + OFF_ANSWER /\ ps_n R < 16) \/
 (ps_c R = A_REC_SPILL /\ ps_n R = 16)).
Proof.
intros P Pn lyc Sc Wc memc mdc k HC.
destruct HC as [_ _ _ _ _ _ _ (Rb & Qb & rdb & blb & HA & HlenR & _)].
destruct HA as (_ & _ & _ & (Hl16 & _) & _).
assert (Hn : 0 <= ps_n R <= 16) by (unfold ps_n; lia).
split; [exact Hn|]. split; [exact (ps_slot_of_ok _ Hn)|].
unfold ps_c, ps_slot_of. destruct (Z.eqb_spec (ps_n R) 16) as [E | E]; [right; split; [reflexivity | exact E] | left].
unfold A_G_REC, OFF_CALLS, CALL_SIZE, OFF_ANSWER. lia.
Qed.

(* the bytes the walk's invariant reads outside the slot: g_rec less the slot, record.spill on the table arm, and
   the recorder's blocks *)
Lemma ps_prot_out_slot : forall Qb x,
(forall pn, In pn (lay_blocks Qb) -> iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE) ->
0 <= ps_n R <= 16 ->
put_prot (ps_n R) Qb x -> ~ (ps_c R <= x < ps_c R + CALL_SIZE).
Proof.
intros Qb x HOWN Hn Hx Hin. unfold ps_c, ps_slot_of in Hin.
destruct Hx as [(Hg & Hnot) | [(Hs & Hlt) | ([q m] & Hq & Hx)]].
- destruct (Z.eqb_spec (ps_n R) 16) as [E | E].
  + unfold A_G_REC, A_REC_SPILL, REC_SIZE, CALL_SIZE in *. lia.
  + apply Hnot. split; [lia|]. right. unfold ps_slot_of. rewrite (proj2 (Z.eqb_neq _ _) E). exact Hin.
- destruct (Z.eqb_spec (ps_n R) 16) as [E | E]; [lia|].
  unfold A_G_REC, A_REC_SPILL, SC_SIZE, OFF_CALLS, CALL_SIZE in *. lia.
- destruct (HOWN _ Hq) as [D1 D2]. cbn [fst snd] in *. unfold iv_apart in D1, D2.
  destruct (Z.eqb_spec (ps_n R) 16) as [E | E];
    unfold A_G_REC, A_REC_SPILL, SC_SIZE, REC_SIZE, OFF_CALLS, CALL_SIZE in *; lia.
Qed.

Lemma ps_store : ps_store_stmt B MT ly S W regs mem md uri files layout verdict R O.
Proof.
unfold ps_store_stmt.
intros j P pn lyc Sc Wc memc memc' mdc mdc' k Hj HlenP HC HJ' KEEPM HNA HARG.
pose proof (ps_core_slot P [pn] lyc Sc Wc memc mdc k HC) as (Hn & Hcok & Hcases).
pose proof ps_sp0_facts as (Hsp & Hsp16 & Hspc).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HC as [HJ Hk Hlen Hmo Hbb Hfr Hlive Hrec].
destruct Hrec as (Rb & Qb & rdb & blb & HA & HlenR & Hrr & Hsp0 & Hprot & HQb & Hcov & HNC & HFN & HNA0 & HND & HARGS & HNEWB).
pose proof (proj1 HJ) as HARc.
assert (HOWN : forall pn, In pn (lay_blocks Qb) ->
  iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE)
  by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA)))))))).
assert (Hj1 : Z.of_nat (j - 1) <= 3) by lia.
set (c := ps_c R) in *.
assert (Hc64 : 0 <= c /\ c + CALL_SIZE <= A_REC_SPILL + SC_SIZE).
{ destruct Hcases as [(H1 & H2 & _) | (H1 & _)]; unfold A_G_REC, OFF_CALLS, OFF_ANSWER, A_REC_SPILL, CALL_SIZE, SC_SIZE in *; lia. }
(* every byte outside the slot is kept *)
assert (KS : forall x, 0 <= x < 2 ^ 64 -> ~ (c <= x < c + CALL_SIZE) -> rdW Wc memc' x = rdW Wc memc x).
{ intros x Hx Hnx. apply KEEPM; [exact Hx | |]; unfold CALL_SIZE in Hnx; lia. }
(* a byte of a live block is outside the slot *)
assert (KB : forall q m x, In (q, m) (ablocks B lyc Sc) -> iv_apart q m A_G_REC REC_SIZE -> iv_apart q m A_REC_SPILL SC_SIZE ->
  q <= x < q + m -> rdW Wc memc' x = rdW Wc memc x).
{ intros q m x Hin D1 D2 Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc Hin) as (_ & H4096 & Hce & _).
  assert (req_size m >= m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  apply KS; [lia|]. unfold iv_apart in D1, D2.
  destruct Hcases as [(H1 & H2 & _) | (H1 & _)];
    unfold A_G_REC, OFF_CALLS, OFF_ANSWER, A_REC_SPILL, CALL_SIZE, SC_SIZE, REC_SIZE in *; lia. }
constructor.
- exact HJ'.
- rewrite app_nil_r. exact Hk.
- rewrite app_nil_r. exact Hlen.
- rewrite app_nil_r. exact Hmo.
- rewrite app_nil_r. exact Hbb.
- intros i r Hir. apply (ps_aval_mem_in (rdW Wc memc)); [exact (Hfr i r Hir)|].
  assert (Hi : (i < 10)%nat) by (change 10%nat with (length ps_saved); apply nth_error_Some; rewrite Hir; discriminate).
  intros x Hx. apply KS; [lia|].
  destruct Hcases as [(H1 & H2 & _) | (H1 & _)];
    unfold A_G_REC, OFF_CALLS, OFF_ANSWER, A_REC_SPILL, CALL_SIZE, SC_SIZE in *; lia.
- exact Hlive.
- exists Rb, Qb, rdb, blb.
  split; [exact HA|]. split; [exact HlenR|]. split; [exact Hrr|]. split; [exact Hsp0|].
  split.
  { intros x Hx. rewrite <- (Hprot x Hx). apply KS; [|exact (ps_prot_out_slot Qb x HOWN Hn Hx)].
    destruct Hx as [(Hg & _) | [(Hs & _) | ([q m] & Hq & Hx)]];
      [unfold A_G_REC, REC_SIZE in *; lia | unfold A_REC_SPILL, SC_SIZE in *; lia|].
    destruct (HQb _ Hq) as (HqS & _ & _). destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc HqS) as (_ & H4096 & Hce & _).
    assert (req_size m >= m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). cbn [fst snd] in Hx. lia. }
  split; [exact HQb|].
  split; [rewrite app_nil_r; exact Hcov|].
  split.
  { intros Hlt. apply (ps_aval_mem_in (rdW Wc memc)); [exact (HNC Hlt)|].
    intros x Hx. apply KS; [unfold A_G_REC, OFF_NCALLS in *; lia|].
    destruct Hcases as [(H1 & H2 & _) | (H1 & H2)]; [|lia].
    unfold A_G_REC, OFF_CALLS, OFF_NCALLS, CALL_SIZE in *. lia. }
  split.
  { apply (ps_aval_mem_in (rdW Wc memc)); [exact HFN|].
    intros x Hx. cbn in Hx. apply KEEPM; unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia. }
  split.
  { rewrite length_app. cbn [length]. rewrite HlenP.
    replace (Z.of_nat (j - 1 + 1)) with (Z.of_nat j) by lia. exact HNA. }
  split; [rewrite app_nil_r; exact HND|].
  split.
  { intros i q Hi.
    destruct (Nat.lt_ge_cases i (length P)) as [Hil | Hil].
    - rewrite nth_error_app1 in Hi by exact Hil.
      apply (ps_aval_mem_in (rdW Wc memc)); [exact (HARGS i q Hi)|].
      assert (Hil' : Z.of_nat i < Z.of_nat (j - 1)) by lia.
      intros x Hx. cbn in Hx. apply KEEPM; unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia.
    - rewrite nth_error_app2 in Hi by exact Hil.
      remember (i - length P)%nat as z eqn:Ez. destruct z as [|z]; [|destruct z; discriminate Hi].
      cbn [nth_error] in Hi. injection Hi as <-.
      replace i with (j - 1)%nat by lia. exact HARG. }
  intros i q Hi. rewrite app_nil_r in Hi.
  destruct (HNEWB i q Hi) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  split; [exact N1|]. split; [exact N2|].
  split.
  { apply (ps_astr_kept (rdW Wc memc)); [exact N3|]. intros y Hy. destruct q as [q m]. cbn [fst snd] in *.
    apply (KB q m y N4 N5 N6). lia. }
  split; [exact N4|]. split; [exact N5|]. split; [exact N6|]. split; [exact N7 | exact N8].
Qed.

End entry.
End e.
End f.
End d.
