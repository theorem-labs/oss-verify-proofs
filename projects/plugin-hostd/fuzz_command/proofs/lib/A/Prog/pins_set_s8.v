(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the segments of pins_set's ASan walk between two calls of xstrdup, after
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh3.v .. ACh6.v (cgif_close's segments between its calls, each a symbolic run
   from a re-seeded state) over fuzz_command's recorder slot. *)

(* `ps_seg_x` (j = 1 .. 3): from the return of the j-th xstrdup to the call of the (j + 1)-th. The run checks the
   shadow byte of the slot's nargs word (marked usable: the error path is not reached), loads nargs, stores
   nargs + 1, checks the shadow byte of args[nargs], stores the copy there, tests the next argument against 0
   (taking the default literal when it is 0) and calls xstrdup. *)
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
RecBLemmas pins_set_s2 pins_set_s1 pins_set_s3 pins_set_s5 pins_set_s6 pins_set_s7.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* a write of the walk into the slot or g_rec: a byte of a program static in the footprint *)
Lemma ps_awr_prog : forall STK sp0 O bl0 blc fr0 lyc own a,
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
awr_byte SEGS B STK sp0 (ps_FP O) bl0 blc fr0 lyc own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyc own a Ha.
assert (HP : Exists (in_zr a) recb_PG) by (destruct Ha as [Ha | Ha]; [exact (recb_grec_in a Ha) | exact (recb_spill_in a Ha)]).
right; right; right; right. left.
split; [|split; [rewrite (recb_ts_prog_m B HB); exact HP | exact (cmd_prog_img a HP)]].
unfold ps_FP. destruct Ha as [Ha | Ha].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

Lemma ps_awr_slot : forall STK sp0 O bl0 blc fr0 lyc own c a, ps_slot_ok c -> c <= a < c + CALL_SIZE ->
awr_byte SEGS B STK sp0 (ps_FP O) bl0 blc fr0 lyc own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyc own c a [(H1 & H2 & _) | ->] Ha; apply ps_awr_prog;
  [left | right]; unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia.
Qed.

Section entry.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (pu pf pl pv : Z) (uri files layout verdict : option (list byte)) (R : rstate)
  (O : list (Z * Z)).
Hypothesis HPRE : afn_pre SEGS B PINS_SET_STK ly S W regs mem md ch.
Hypothesis HSF : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pf files.
Hypothesis HSL : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pl layout.
Hypothesis HSV : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pv verdict.

#[local] Notation sp0 := (ps_sp0 regs).
#[local] Notation FPps := (ps_FP O).
#[local] Notation A := (ps_A uri files layout verdict).
#[local] Notation PTRS := (ps_ptrs pu pf pl pv uri files layout verdict).
#[local] Notation CORE := (ps_core B MT ly S W regs mem md uri files layout verdict R O).
#[local] Notation KEEP := (ps_keep B regs pf pl pv R).
#[local] Notation POST := (ps_post B MT ly S W regs mem md uri files layout verdict R O).

(* g_rec.refuse / code / state, read from the walk's invariant *)
Lemma ps_core_scalars : forall P Pn lyc Sc Wc memc mdc k, CORE P Pn lyc Sc Wc memc mdc k ->
aval_mem (rdW Wc memc) A_G_REC 4 (r_refuse R mod 2 ^ 32) /\
aval_mem (rdW Wc memc) (A_G_REC + 4) 4 (r_code R mod 2 ^ 32) /\
aval_mem (rdW Wc memc) (A_G_REC + OFF_STATE) 8 (r_state R) /\
0 <= r_state R < 2 ^ 64 /\ -2 ^ 31 <= r_refuse R < 2 ^ 31 /\ -2 ^ 31 <= r_code R < 2 ^ 31.
Proof.
intros P Pn lyc Sc Wc memc mdc k HC.
pose proof (ps_core_slot B MT ly S W regs mem md uri files layout verdict R O P Pn lyc Sc Wc memc mdc k HC)
  as (Hn & Hcok & Hcases).
destruct HC as [_ _ _ _ _ _ _ (Rb & Qb & rdb & blb & HA & HlenR & Hrr & Hsp0 & Hprot & _)].
pose proof HA as (_ & _ & _ & _ & _ & _ & HSC & _).
destruct HSC as (Vr & Vc & Vn & Vs & Vh & Rr & Rc & Rn & Rs & Rh).
pose proof (Hrr []) as Hrr0.
destruct (ps_rec_record_scalars Rb REC_PINS_SET []) as (E1 & E2 & E3 & _).
destruct (ps_rec_record_scalars R REC_PINS_SET []) as (F1 & F2 & F3 & _).
assert (ER : r_refuse Rb = r_refuse R) by (rewrite <- E1, <- F1, Hrr0; reflexivity).
assert (EC : r_code Rb = r_code R) by (rewrite <- E2, <- F2, Hrr0; reflexivity).
assert (ES : r_state Rb = r_state R) by (rewrite <- E3, <- F3, Hrr0; reflexivity).
rewrite ER in Vr, Rr. rewrite EC in Vc, Rc. rewrite ES in Vs, Rs.
assert (KG : forall x, A_G_REC <= x < A_G_REC + OFF_NCALLS \/ A_G_REC + OFF_ANSWER <= x < A_G_REC + REC_SIZE ->
  rdW Wc memc x = rdb x).
{ intros x Hx. apply Hprot. left. split; [cbv [OFF_NCALLS OFF_ANSWER REC_SIZE] in *; lia|].
  intros (Hlt & [Hnc | Hsl]); [cbv [OFF_NCALLS OFF_CALLS OFF_ANSWER] in *; lia|].
  unfold ps_slot_of in Hsl. assert (Hn16 : ps_n R <> 16) by lia. rewrite (proj2 (Z.eqb_neq (ps_n R) 16) Hn16) in Hsl.
  clear - Hx Hsl Hn Hlt. cbv [A_G_REC OFF_CALLS CALL_SIZE OFF_ANSWER REC_SIZE OFF_NCALLS] in *. lia. }
unfold OFF_REFUSE, OFF_CODE in Vr, Vc. rewrite Z.add_0_r in Vr.
split; [apply (ps_aval_mem_in rdb); [exact (ps_aval_mod _ _ 4 _ Vr) | intros x Hx; apply KG; cbn in Hx; unfold OFF_NCALLS; lia]|].
split; [apply (ps_aval_mem_in rdb); [exact (ps_aval_mod _ _ 4 _ Vc) | intros x Hx; apply KG; cbn in Hx; unfold OFF_NCALLS; lia]|].
split; [apply (ps_aval_mem_in rdb); [exact Vs | intros x Hx; apply KG; cbn in Hx; cbv [OFF_STATE OFF_ANSWER REC_SIZE] in *; lia]|].
split; [exact Rs|]. split; [exact Rr | exact Rc].
Qed.

End entry.
End e.
End f.
End d.
