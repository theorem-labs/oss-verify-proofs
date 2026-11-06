(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the invariant of pins_set's ASan walk at record()'s join, after
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the facts a segment of cgif_close carries) over fuzz_command's
   recorder. *)

(* `ps_jinv`: the state at record()'s join (pc PS_JOIN on the table arm, PS_RET_RCF after rec_calls_free on the
   spill arm): the journal from the entry, the frame of saved registers, the registers the rest of the body reads,
   and the recorder ready for the new call (ps_rec without the slot's fields, which the join writes). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas pins_set_s2 pins_set_s1 pins_set_s3.
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
Section entry.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (pu pf pl pv : Z) (uri files layout verdict : option (list byte)) (R : rstate) (O : list (Z * Z)).

(* the recorder at the join: ps_rec (pins_set_s3.v) without the slot's fields *)
Definition ps_rec0 lyc Sc (Wc : world SEGS) memc : Prop :=
exists Rb Qb (rdb : reader) blb,
arep_at blb rdb A_G_REC A_REC_SPILL Rb Qb /\
length (r_calls Rb) = length (r_calls R) /\ (forall A, rec_record Rb REC_PINS_SET A = rec_record R REC_PINS_SET A) /\
(16 <= ps_n R -> l_spill Qb = []) /\
(forall x, put_prot (ps_n R) Qb x -> rdW Wc memc x = rdb x) /\
(forall pn, In pn (lay_blocks Qb) -> In pn (ablocks B lyc Sc) /\ In pn O /\ 0 < snd pn) /\
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn (lay_blocks Qb)) /\
(ps_n R < 16 -> aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (ps_n R + 1)).

Definition ps_jinv lyc Sc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc (k : Z) : Prop :=
ajournal SEGS B PINS_SET_STK (ps_sp0 regs) (ps_FP O) ly S W mem md [] lyc Sc Wc memc mdc k /\
k <= rec_spill_frees R /\
mo_le MT S Sc (rec_spill_frees R * mo_free MT) /\
blocks_bytes Sc <= blocks_bytes S /\
(forall i r, nth_error ps_saved i = Some r ->
  aval_mem (rdW Wc memc) (ps_sp0 regs - 8 - 8 * Z.of_nat i) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
ps_rec0 lyc Sc Wc memc /\
getr regsc 2 = w64 (ps_sp0 regs - 80) /\ getr regsc 3 = w64 (as_gp B) /\ getr regsc 4 = w64 (as_tp B) /\
getr regsc 8 = w64 (ps_c R) /\ getr regsc 22 = w64 A_G_REC /\ getr regsc 23 = w64 SB /\
getr regsc 21 = w64 pu /\ getr regsc 20 = w64 pf /\ getr regsc 19 = w64 pl /\ getr regsc 9 = w64 pv /\
(forall r, 25 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).

#[local] Notation A := (ps_A uri files layout verdict).
#[local] Notation CORE := (ps_core B MT ly S W regs mem md uri files layout verdict R O).
#[local] Notation KEEP := (ps_keep B regs pf pl pv R).
#[local] Notation POST := (ps_post B MT ly S W regs mem md uri files layout verdict R O).

(* --- the statements of the walk's pieces; each is proved in its own file and the assembly (pins_set.v) chains
   them --------------------------------------------------------------------------------------------------- *)

(* storing the j-th copy: nargs := j and args[j - 1] := p, every other byte kept (pins_set_s7.v) *)
Definition ps_store_stmt : Prop := forall j P pn lyc Sc (Wc : world SEGS) memc memc' mdc mdc' k,
(1 <= j <= 4)%nat -> length P = (j - 1)%nat ->
CORE P [pn] lyc Sc Wc memc mdc k ->
ajournal SEGS B PINS_SET_STK (ps_sp0 regs) (ps_FP O) ly S W mem md [] lyc Sc Wc memc' mdc' k ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (ps_c R + 4 <= x < ps_c R + 8) ->
  ~ (ps_c R + 8 + 8 * Z.of_nat (j - 1) <= x < ps_c R + 16 + 8 * Z.of_nat (j - 1)) ->
  rdW Wc memc' x = rdW Wc memc x) ->
aval_mem (rdW Wc memc') (ps_c R + 4) 4 (Z.of_nat j) ->
aval_mem (rdW Wc memc') (ps_c R + 8 + 8 * Z.of_nat (j - 1)) 8 (fst pn) ->
CORE (P ++ [pn]) [] lyc Sc Wc memc' mdc' k.

(* the recorded call closes into the model's rec_record (pins_set_s10.v) *)
Definition ps_close_stmt : Prop := forall P lyc Sc (Wc : world SEGS) memc mdc k,
length P = 4%nat -> CORE P [] lyc Sc Wc memc mdc k ->
exists O2, rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_PINS_SET A) O2 /\
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O2) /\
(forall pn, In pn O2 -> In pn O \/ ~ In pn (ablocks B ly S)) /\
acall_at (ablocks B lyc Sc) (rdW Wc memc) (ps_c R) (REC_PINS_SET, A) P.

(* the tail jump into answer_code (pins_set_s10.v) *)
Definition ps_tail_stmt : Prop := forall lyc Sc (Wc : world SEGS) memc mdc k (regs2 : bvmap 5 word) R2 O2 code,
ajournal SEGS B PINS_SET_STK (ps_sp0 regs) (ps_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
spZ regs2 = ps_sp0 regs -> getr regs2 1 = getr regs 1 -> aregs_preserved regs regs2 ->
getr regs2 10 = w64 code -> -2 ^ 31 <= code < 2 ^ 31 ->
rec_repA B lyc Sc (rdW Wc memc) R2 O2 ->
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O2) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn O2 -> In pn O \/ ~ In pn (ablocks B ly S)) ->
pins_set_m R uri files layout verdict = rec_answer_code R2 code ->
k + EV_ANSWER_CODE <= EV_PINS_SET R ->
blocks_bytes Sc <= blocks_bytes S + ps_live uri files layout verdict 4 ->
mo_le MT S Sc (rec_spill_frees R * mo_free MT + ps_xm MT uri files layout verdict 4) ->
SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + AF_answer_code)) memc (seg_rom SEGS)) mdc) POST.

(* the walk at record()'s join (pc PS_JOIN on the table arm, PS_RET_RCF after rec_calls_free on the spill arm) *)
Definition ps_jcont : Prop :=
forall pc lyc Sc (Wc : world SEGS) regsc memc mdc k, (pc = PS_JOIN \/ pc = PS_RET_RCF) ->
ps_jinv lyc Sc Wc regsc memc mdc k ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)) mdc) POST.

(* from the entry to record()'s join, both arms (pins_set_s9.v) *)
Definition ps_entry_stmt : Prop :=
ps_jcont -> SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + PS_ENTRY)) mem (seg_rom SEGS)) md) POST.

(* the walk at the return of the j-th xstrdup (j = 1 .. 4), the copy p in a0 *)
Definition ps_xret_stmt (j : nat) : Prop := forall P p lyc Sc (Wc : world SEGS) regsc memc mdc k,
length P = (j - 1)%nat ->
CORE P [(p, Z.of_nat (length (nth (j - 1) A [])) + 1)] lyc Sc Wc memc mdc k ->
KEEP j regsc -> getr regsc 10 = w64 p ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + ps_ret j)) memc (seg_rom SEGS)) mdc) POST.

(* from the return of the fourth xstrdup to the end (pins_set_s11.v) *)
Definition ps_x4_stmt : Prop := ps_xret_stmt 4.

(* from the return of the j-th xstrdup to the call of the (j + 1)-th (j = 1 .. 3, pins_set_s8.v) *)
Definition ps_segx_stmt (j : nat) : Prop := ps_xret_stmt (Datatypes.S j) -> ps_xret_stmt j.

(* from record()'s join to the call of the first xstrdup (pins_set_s12.v) *)
Definition ps_join_stmt : Prop := ps_xret_stmt 1 -> ps_jcont.

End entry.
End e.
End f.
End d.
