(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of pins_clear's ASan walk on plugin-hostd/fuzz_command
   (the inlined record(), recorder.c:205-221), after proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v (cl_A_okX, the
   entry segment of the cgif_close walk) over fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/pins_clear_s3.v, with its module paths and module names changed; 57 of its 90 lines of code are new or changed and 657 lines of the source are left out. *)
(* check_arity's row 3 (the verb whose syntax string is at 0x21320; (mn, mx) = (0, 1)), from the matched-row entry
   0x87334 (CA_SEG) to `ret` (0x8777c, CA_RET), shaped like check_arity_s4.v's ca_row_1 with the two extra
   hypotheses the bcmp wrapper's contract needs (gp and tp at the entry).

   The walk: the syntax arm (0x874d8) enters dots_loop (head 0x87638) and scans the 14 consecutive items
   0x21320 .. 0x2132d with the bcmp wrapper against "..." (jal 0x8764c, return 0x87650); no item equals "...", so
   every `beqz a0` at 0x87650 falls through, and the walk reaches `ret` with the callee-saved registers back
   (ca_regs_back_g). 421 instructions to `ret`. Each call is check_arity_s7.v's ca_bcmp_step at its own junk band
   kk = 1024 + 16 j (one ca_site_ne line per site).

   Template (not used as a source): a former lib/A/Prog/check_arity.v, an earlier
   ASan walk in the OLD lib/Lib `evt` / MState framework against the OLD statement (bcmp_wrap_contract). It is a
   TEMPLATE, NOT A SOURCE: porting it is a rewrite into another execution model, and our concrete-run method needs
   none of its loop invariants. Its pcs agree with this walk: the syntax arm 0x874d8 is passed once, dots_loop's
   head 0x87638 14 times; the format arm 0x87368 and fmtloop 0x873dc are not reached (row 3 is a syntax row), and
   rows_loop's head 0x87304 lies before the matched-row entry this lemma starts from. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_arity_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_arity_s1 check_arity_s2 check_arity_s3 check_arity_s4 check_arity_s5 check_arity_s6 check_arity_s7.
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
Hypothesis ABCMP : abcmp_realizes SEGS B (SIG CS___interceptor_trampoline_bcmp).
Hypothesis HVO : cmd_val_objs.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let CBS := ca_bcmp_step B HB ABCMP HVO.

Lemma ca_row_3 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre B 3 0 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
getr regs0 3 = w64 (as_gp B) -> getr regs0 4 = w64 (as_tp B) ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post B regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP G3 G4.
pose proof (ca_row_open B HB 3 0 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
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
assert (Usp : bv_unsigned (ew E0 2) = spZ regs0 - 112) by (rewrite (EE 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Hsp).
assert (Egp : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl), R3; exact G3).
assert (Etp : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl), R4; exact G4).
assert (AG : forall n, (n < A_TEXT)%nat -> ew E0 n = ew E0 n) by reflexivity.
pose proof (ca_lowkept_refl W memc) as HLK.
clear EE HFR HRO0 Hceil Hslo Hshi H47 Hc1 Hc2.
ca_site_ne CBS RUNP RUNC BR 3%nat 1024%nat.
ca_site_ne CBS RUNP RUNC BR 3%nat 1040%nat.
ca_site_ne CBS RUNP RUNC BR 3%nat 1056%nat.
ca_site_ne CBS RUNP RUNC BR 3%nat 1072%nat.
ca_site_ne CBS RUNP RUNC BR 3%nat 1088%nat.
ca_site_ne CBS RUNP RUNC BR 3%nat 1104%nat.
ca_site_ne CBS RUNP RUNC BR 3%nat 1120%nat.
ca_site_ne CBS RUNP RUNC BR 3%nat 1136%nat.
ca_site_ne CBS RUNP RUNC BR 3%nat 1152%nat.
ca_site_ne CBS RUNP RUNC BR 3%nat 1168%nat.
ca_site_ne CBS RUNP RUNC BR 3%nat 1184%nat.
ca_site_ne CBS RUNP RUNC BR 3%nat 1200%nat.
ca_site_ne CBS RUNP RUNC BR 3%nat 1216%nat.
ca_site_ne CBS RUNP RUNC BR 3%nat 1232%nat.
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
