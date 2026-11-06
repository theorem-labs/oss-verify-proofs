(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the release of number's class-0 side-stack frame (0x8e5a0..0x8e618, cgif's exitRA in A/ACam.v) and number's return. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/numberR.v, with its module paths and module names changed; 63 of its 93 lines of code are new or changed and 186 lines of the source are left out. *)
(* check_arity on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan, lib/B): ROW 8 of
   g_parsed (`pin_set`, syntax "<uri> <path>=<sha256>[,<path>=<sha256>...] <scheme>:<sha256> [verdict=<verdict>]" at
   0x21580, (mn, mx) = (3, 4)), from the matched-row entry BASE + CA_SEG (0x87478) to `ret` (BASE + CA_RET, 0x87998).
   The port of a Theorem Labs lane's A walk check_arity_r8.v (a working branch 30490f0ad18), written
   with s7's per-site tactic ca_site_ne as the r3 and r14 walks are (A's r8 had a local per-site tactic).

   B facts the walk meets (the run computes them; listed here as the cross-check):
   - the syntax arm (0x87654) enters syntax_has's dots_loop (head 0x8787c) for the item "[verdict=<verdict>]" and
     calls the bcmp wrapper 17 times, all at the jal 0x87898, return 0x8789c (retk 4972 = 0x8789c - BASE 0x86530),
     a1 = A_OBJ 19 = "..." (0x218c0), a2 = 3; the items are 0x215bd, 0x215be, ..., 0x215cd (A's + 0x40); none of them
     equals "...", so every `beqz a0` at 0x8789c falls through;
   - B reads its frame slots 0x00 .. 0x20 back after each call; s7's ca_bcmp_step keeps the frame region's chunks;
   - at CA_SEG s3 holds read (not read - 1): the arity test computes read - 1 at 0x87950;
   - 1574 instructions from CA_SEG to `ret` inclusive (1280 to the first jal, 15 from each jal to the next, 54 from
     the last jal to `ret`); call j uses the junk band kk = 1024 + 16 j.
   Concrete interpreter (internal path, read = 4 and read = 5): 1574 instructions, 17 calls, a0 =
   0x215bd .. 0x215cd, a1 = 0x218c0, return 0x8789c, no equal call; A twin 1327 / 17 / 0x2157d.

   UBSan trap edges on this row's path (all branch to the `unimp` 0x87a2c; none is taken). The symbolic run
   (sym_runN_pi) decides each by computation; RUNC (SRr_run_pi_AJ_call, lib/B/Prog/PaCallRun.v:41) certifies a run
   that ends at a call, RUNP (SRr_run_pi_AJ, lib/B/Prog/PaLibF.v:424) the run that ends at `ret`. The runs stop at
   no branch but the `beqz a0` after each call (measured: (internal path)).
   - 0x87654: refuted by RUNC at check_arity_r8.v:107, from the syntax pointer ca_syn_addr 8 = 0x21580, a literal
     of ca_ss (check_arity_s1.v) from cmd_ro_ok / cmd_val_objs.
   - 0x876bc, 0x87720: refuted by RUNC at check_arity_r8.v:107, from the literal scan pointer (inside the literal
     0x21580).
   - 0x8770c: refuted by RUNC at check_arity_r8.v:107, from the literal depth of the run (0 or 1).
   - 0x87840: refuted by RUNC at check_arity_r8.v:107, from the literal ~item and len - 1 of the run.
   - 0x87918: refuted by RUNC at check_arity_r8.v:107, from the literal min of the run (0 .. 2).
   - 0x87880: refuted by RUNC at check_arity_r8.v:107-123 (once per call), from the literal ~item reloaded from the
     frame slot 0x20 (a chunk ca_bcmp_step keeps) and the literal i in s1 (callee-saved, kept by the step).
   - 0x87954: refuted by RUNP at check_arity_r8.v:125, from the atom-32 fact [mn + 1, Z.min mx 63 + 1] = [4, 5] of
     ca_facts (check_arity_s1.v), seeded by ca_row_open (check_arity_s3.v) from ca_row_pre's
     `mn <= s3v - 1 <= mx /\ 1 <= s3v <= 64`.
   The arity tests 0x87958 / 0x8795c fall through by the same fact (the abort edge 0x87a94 is not reached).

   Templates (read only, never imported): a working branch fd8e07f77cd lib/B/Prog/check_arity.v, the
   old-route B walk in the abandoned lib/Lib `evt` / MState framework against the OLD check_arity_contract. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_arity_s1 check_arity_s2 check_arity_s3 check_arity_s5 check_arity_s6 check_arity_s7.
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
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).

Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp).
Hypothesis HVO : cmd_val_objs.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let CBS := ca_bcmp_step B HB ABCMP HVO.

Lemma ca_row_8 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre B 8 3 4 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
getr regs0 3 = w64 (as_gp B) -> getr regs0 4 = w64 (as_tp B) ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post B regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP G3 G4.
pose proof (ca_row_open B HB 8 3 4 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO0 & Hsp & HFR & R3 & R4 & _).
pose proof (proj1 HRO0) as HRO.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
assert (Hsp0 : 2 ^ 46 <= spZ regs0 <= 2 ^ 47) by (unfold CHECK_ARITY_STK, ESTACK in *; lia).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
set (E0 := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply Eimg_env.
assert (EE : forall n (r : bv 5), (n < A_TEXT)%nat -> Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs r).
{ intros n r Hn Hr. subst E0. rewrite Eimg_low by exact Hn. apply ew_Ereg_nat. exact Hr. }
assert (Usp : bv_unsigned (ew E0 2) = spZ regs0 - 144) by (rewrite (EE 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Hsp).
assert (Egp : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl), R3; exact G3).
assert (Etp : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl), R4; exact G4).
assert (AG : forall n, (n < A_TEXT)%nat -> ew E0 n = ew E0 n) by reflexivity.
pose proof (ca_lowkept_refl W memc) as HLK.
clear EE HFR HRO0 Hceil Hslo Hshi H47 Hc1 Hc2.
(* call 0: the first run (CA_SEG .. jal 0x87898, 1280 instructions); calls 0 .. 16 (x = 0x215bd .. 0x215cd) *)
ca_site_ne CBS RUNP RUNC BR 8%nat 1024%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1040%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1056%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1072%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1088%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1104%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1120%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1136%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1152%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1168%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1184%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1200%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1216%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1232%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1248%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1264%nat.
ca_site_ne CBS RUNP RUNC BR 8%nat 1280%nat.
(* ret: 0x878a0 .. `ret` 0x87998 (the arity test 0x87950 .. 0x8795c, the epilogue) *)
ca_run RUNP RUNC.
destruct (ca_regs_back_g (w_H W) _ _ _ regs regs0 s3v HS AG ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

End e.
End f.
End d.
