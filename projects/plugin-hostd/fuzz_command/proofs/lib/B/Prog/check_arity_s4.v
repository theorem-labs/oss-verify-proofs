(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the release of number's class-0 side-stack frame (0x8e5a0..0x8e618, cgif's exitRA in A/ACam.v) and number's return. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/numberR.v, with its module paths and module names changed; 109 of its 138 lines of code are new or changed and 187 lines of the source are left out. *)
(* check_arity on image B (fuzz_command.asan-ubsan): the 18 matched rows of g_parsed whose run from the matched-row
   entry CA_SEG (0x87478) to the `ret` (CA_RET, 0x87998) makes no call: rows 1, 2, 4-7, 9-13 and 15-17 (syntax arm,
   syntax_arity inlined) and 18-21 (format arm, syntax_format_arity inlined). Rows 0, 3, 8 and 14 call bcmp and are
   in check_arity_r0/r3/r8/r14.

   Port of a Theorem Labs lane's A walk lib/A/Prog/check_arity_s4.v (a working branch 9c6410fb32e). The row
   interface (ca_post, ca_row_pre, ca_row_open, ca_final_ok, ca_regs_back), which A has at the head of its s4, is in
   B's check_arity_s3.v; this file holds the row lemmas only. B changes: the frame is 144 bytes (the frame region's
   offset from the entry sp is -144 in ca_awr), and s3 holds read = min(w->n, 64) at CA_SEG, so ca_row_pre bounds
   s3v - 1 by the row's arity (mn, mx), and the seed's atom 32 = s3v has the fact [mn + 1, mx + 1].

   Each row lemma is one symbolic run (paj_run_shc in ca_row) of the B code from CA_SEG to the `ret`; every branch of
   the run is decided inside the run (decide_cond2 over check_arity_s3's ca_seed state), and the run never reaches
   the UBSan trap `unimp` 0x87a2c. Instructions run before the `ret` (equal to the concrete interpreter
   (internal path) on the B twin 658cefbe, which counts the `ret` too: 1 more), rows 1 61, 2 235, 4 343, 5 595,
   6 438, 7 623, 9 287, 10 712, 11 179, 12 235, 13 521, 15 184, 16 179, 17 179, 18 239, 19 335, 20 359, 21 148.

   UBSan trap edges in this range, each refuted at its branch:
   - 0x874ac (`beqz s4`, syntax nonnull, format arm): refuted by the run of ca_row_18, ca_row_19, ca_row_20, ca_row_21
     at check_arity_s4.v:125 (ca_row's paj_run_shc; lemmas at :140-245), from s4 is the row's syntax word, a literal >=
     0x21140 (ca_gparsed of ca_seed, from cmd_ro_ok). Visits per row (row (count)): 18 (1), 19 (1), 20 (1), 21 (1).
   - 0x87654 (`beqz s4`, syntax nonnull, syntax arm): refuted by the run of ca_row_1 .. ca_row_17 (rows 1, 2, 4, 5, 6,
     7, 9, 10, 11, 12, 13, 15, 16, 17) at check_arity_s4.v:125 (ca_row's paj_run_shc; lemmas at :140-245), from as
     0x874ac. Visits per row (row (count)): 1 (1), 2 (1), 4 (1), 5 (1), 6 (1), 7 (1), 9 (1), 10 (1), 11 (1), 12 (1), 13
     (1), 15 (1), 16 (1), 17 (1).
   - 0x87560 (`beq a0,s6`, p + 1 overflow, format skip-spaces): refuted by the run of ca_row_18, ca_row_19, ca_row_20
     at check_arity_s4.v:125 (ca_row's paj_run_shc; lemmas at :140-245), from p is a literal address in the row's
     syntax string (ca_syn of ca_seed, from cmd_ro_ok), < 0x218c0. Visits per row (row (count)): 18 (1), 19 (2), 20
     (2).
   - 0x875c4 (`beq s5,s6`, p + 1 overflow, format item scan): refuted by the run of ca_row_18, ca_row_19, ca_row_20 at
     check_arity_s4.v:125 (ca_row's paj_run_shc; lemmas at :140-245), from as 0x87560. Visits per row (row (count)): 18
     (2), 19 (4), 20 (4).
   - 0x879f8 (`beq s5,a6`, p + 1 overflow, format first item): refuted by the run of ca_row_18, ca_row_19, ca_row_20,
     ca_row_21 at check_arity_s4.v:125 (ca_row's paj_run_shc; lemmas at :140-245), from as 0x87560. Visits per row (row
     (count)): 18 (6), 19 (7), 20 (10), 21 (4).
   - 0x87630 (`blt a0,t0`, min + 1 overflow, format arm): refuted by the run of ca_row_18, ca_row_19, ca_row_20 at
     check_arity_s4.v:125 (ca_row's paj_run_shc; lemmas at :140-245), from min is a literal counter <= 80. Visits per
     row (row (count)): 18 (1), 19 (2), 20 (2).
   - 0x876bc (`beq s4,s6`, p + 1 overflow, token scan): refuted by the run of ca_row_4 .. ca_row_13 (rows 4, 5, 6, 7,
     9, 10, 13) at check_arity_s4.v:125 (ca_row's paj_run_shc; lemmas at :140-245), from as 0x87560. Visits per row
     (row (count)): 4 (1), 5 (2), 6 (1), 7 (2), 9 (1), 10 (1), 13 (1).
   - 0x87720 (`beq s4,s6`, p + 1 overflow, item scan): refuted by the run of ca_row_2 .. ca_row_17 (rows 2, 4, 5, 6, 7,
     9, 10, 11, 12, 13, 15, 16, 17) at check_arity_s4.v:125 (ca_row's paj_run_shc; lemmas at :140-245), from as
     0x87560. Visits per row (row (count)): 2 (10), 4 (11), 5 (16), 6 (21), 7 (32), 9 (6), 10 (42), 11 (5), 12 (10), 13
     (27), 15 (7), 16 (5), 17 (5).
   - 0x87788 (`beq a4,s6`, p + 1 overflow, '|' skip): refuted by the run of ca_row_4, ca_row_5, ca_row_9 at
     check_arity_s4.v:125 (ca_row's paj_run_shc; lemmas at :140-245), from as 0x87560. Visits per row (row (count)): 4
     (1), 5 (1), 9 (1).
   - 0x877f0 (`beq a1,s6`, p + 1 overflow, '|' next item): refuted by the run of ca_row_4, ca_row_5, ca_row_9 at
     check_arity_s4.v:125 (ca_row's paj_run_shc; lemmas at :140-245), from as 0x87560. Visits per row (row (count)): 4
     (3), 5 (11), 9 (3).
   - 0x8770c (`blt a5,a4`, depth + 1 overflow): refuted by the run of ca_row_2 .. ca_row_17 (rows 2, 4, 5, 6, 7, 9, 10,
     11, 12, 13, 15, 16, 17) at check_arity_s4.v:125 (ca_row's paj_run_shc; lemmas at :140-245), from depth is a
     literal counter <= 80. Visits per row (row (count)): 2 (1), 4 (1), 5 (1), 6 (2), 7 (3), 9 (1), 10 (2), 11 (1), 12
     (1), 13 (3), 15 (1), 16 (1), 17 (1).
   - 0x877dc (`blt a3,a2`, depth + 1 overflow, '|' next item): refuted by the run of ca_row_5 at check_arity_s4.v:125
     (ca_row's paj_run_shc; lemmas at :140-245), from as 0x8770c. Visits per row (row (count)): 5 (1).
   - 0x87918 (`blt a0,t0`, min + 1 overflow, syntax arm): refuted by the run of ca_row_2 .. ca_row_17 (rows 2, 4, 5, 6,
     7, 9, 10, 11, 12, 13, 15, 16, 17) at check_arity_s4.v:125 (ca_row's paj_run_shc; lemmas at :140-245), from as
     0x87630. Visits per row (row (count)): 2 (1), 4 (1), 5 (2), 6 (2), 7 (3), 9 (1), 10 (2), 11 (1), 12 (1), 13 (2),
     15 (1), 16 (1), 17 (1).
   - 0x87954 (`addiw a0,s3,-1; bge a0,s3`, read - 1 overflow): refuted by the run of ca_row_1 .. ca_row_21 (rows 1, 2,
     4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21) at check_arity_s4.v:125 (ca_row's paj_run_shc; lemmas
     at :140-245), from s3 is atom 32 = s3v with the fact [mn + 1, mx + 1] (ca_ss's ca_facts), inside [1, 64] by
     ca_row_pre's mn <= s3v - 1 <= mx and 1 <= s3v <= 64; read - 1 = atom - 1 does not wrap 32 bits and is below read.
     Visits per row (row (count)): 1 (1), 2 (1), 4 (1), 5 (1), 6 (1), 7 (1), 9 (1), 10 (1), 11 (1), 12 (1), 13 (1), 15
     (1), 16 (1), 17 (1), 18 (1), 19 (1), 20 (1), 21 (1).
   Not reached by these rows: 0x874d8 and 0x879e4 (no format string starts with ' ' or has '<' / '['), 0x875b0
   (the same), 0x87840 and 0x87880 (no item starting with '[' of length >= 3). Entry sites 0x872a8, 0x87358,
   0x87360, 0x8740c, 0x87414 are before CA_SEG (entry lane). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_arity_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_arity_s1 check_arity_s3.
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
Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) B LAWS.

Ltac ca_awr Usp :=
unfold ca_ss; cbn [ss_mem];
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -144);
[ reflexivity | rewrite Usp; lia | unfold CHECK_ARITY_STK, ESTACK; cbn; lia | cbn; lia |];
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* one row: the run from CA_SEG to the `ret` (paj_run_shc), then the return (paj_ret_at) with ca_regs_back *)
Ltac ca_row k mn mx :=
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP;
pose proof (ca_row_open (PI := PI) B HB k mn mx ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP)
  as HS;
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _);
unfold cfg_at; change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG));
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity);
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env;
paj_run_shc RUNP RUNC HS HJ;
[ ca_awr Usp
| lazymatch goal with HS1 : st_ok_pi _ _ _ _ (restrict _ ?ms1) |- _ =>
    destruct (ca_regs_back (PI := PI) (w_H W) _ ms1 regs regs0 s3v HS1 ltac:(vm_compute; reflexivity) R3 R4
      ltac:(lia)) as [HPR Hra'];
    eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS1 eq_refl
      ltac:(vm_compute; reflexivity));
    intros mat'; unfold ca_post, apost_base;
    lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end;
    split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
    split; [|split; [exact HPR | split; reflexivity]];
    unfold EV_CHECK_ARITY; apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ
  end ].

(* row 1, worker_list (syntax arm): arity [0, 0] *)
Lemma ca_row_1 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 1 0 0 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 1%nat 0 0. Qed.

(* row 2, instance_info (syntax arm): arity [1, 1] *)
Lemma ca_row_2 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 2 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 2%nat 1 1. Qed.

(* row 4, quarantine_clear (syntax arm): arity [1, 1] *)
Lemma ca_row_4 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 4 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 4%nat 1 1. Qed.

(* row 5, policy_set (syntax arm): arity [2, 2] *)
Lemma ca_row_5 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 5 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 5%nat 2 2. Qed.

(* row 6, pool_config (syntax arm): arity [2, 2] *)
Lemma ca_row_6 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 6 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 6%nat 2 2. Qed.

(* row 7, worker_env (syntax arm): arity [3, 3] *)
Lemma ca_row_7 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 7 3 3 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 7%nat 3 3. Qed.

(* row 9, pin_clear (syntax arm): arity [1, 1] *)
Lemma ca_row_9 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 9 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 9%nat 1 1. Qed.

(* row 10, lv2_worker_set (syntax arm): arity [2, 2] *)
Lemma ca_row_10 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 10 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 10%nat 2 2. Qed.

(* row 11, pin_accept (syntax arm): arity [1, 1] *)
Lemma ca_row_11 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 11 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 11%nat 1 1. Qed.

(* row 12, pin_layout (syntax arm): arity [1, 1] *)
Lemma ca_row_12 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 12 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 12%nat 1 1. Qed.

(* row 13, pin_expect (syntax arm): arity [2, 2] *)
Lemma ca_row_13 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 13 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 13%nat 2 2. Qed.

(* row 15, chain_clear (syntax arm): arity [1, 1] *)
Lemma ca_row_15 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 15 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 15%nat 1 1. Qed.

(* row 16, descriptor_get (syntax arm): arity [1, 1] *)
Lemma ca_row_16 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 16 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 16%nat 1 1. Qed.

(* row 17, panel_get (syntax arm): arity [1, 1] *)
Lemma ca_row_17 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 17 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 17%nat 1 1. Qed.

(* row 18, remove (format arm): arity [1, 1] *)
Lemma ca_row_18 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 18 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 18%nat 1 1. Qed.

(* row 19, connect (format arm): arity [2, 2] *)
Lemma ca_row_19 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 19 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 19%nat 2 2. Qed.

(* row 20, disconnect (format arm): arity [2, 2] *)
Lemma ca_row_20 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 20 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 20%nat 2 2. Qed.

(* row 21, quit (format arm): arity [0, 0] *)
Lemma ca_row_21 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre (PI := PI) B 21 0 0 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post (PI := PI) B regs0 ly S W0 mem0 md0).
Proof. ca_row 21%nat 0 0. Qed.

End e.
End f.
End d.
