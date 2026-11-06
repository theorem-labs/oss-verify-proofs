(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the fifth segment of check_reply's walk (fuzz_command.asan, 0x86d78), the
   strcmp call of the refusal path (0x86fb8) and the branch into the epilogue, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call and back) and A/ACh5.v (a segment that ends
   in another segment's statement), at c8557374ad2e.

   The code of the segment is
     0x86fb8  jal  wrapper_strcmp       a0 = g_rec.reply, a1 = s3 = F + 32, which holds "resp <code>"
     0x86fbc  beqz a0, 0x86ff8          equal: the epilogue; else j 0x870d8, the abort
   The entry facts give `xr = refusal_text (reply_code_a xr)` for a negative code (reply_okA), and the frame holds
   `refusal_text code ++ [0]` (the snprintf step of segment 4), so the two strings are equal, the interceptor
   returns 0, and the abort edge 0x86fc0 is not taken.

   The walk runs with the symbolic regions dropped (`st_ok_pi_submem` with []): the two instructions write no
   memory, so the engine's frame is empty and every byte the walk reads is the byte of the state the segment was
   entered in. The interceptor's own writes are the ones its contract allows, inside its scratch window below sp. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module paths and module names changed; 69 of its 99 lines of code are new or changed and 382 lines of the source are left out. *)
(* check_arity, row 14 (`chain`, (mn, mx) = (2, 2147483647)): the walk from the matched-row entry 0x87334
   (BASE + CA_SEG) to `ret` 0x8777c (BASE + CA_RET), 700 instructions, with its 13 calls of the bcmp wrapper.
   Shaped like check_arity_s4.v's ca_row_1 with the two extra hypotheses the bcmp wrapper's contract needs (gp and
   tp at the entry).

   Template, cited and not used: a former lib/A/Prog/check_arity.v is an earlier ASan
   walk in the OLD lib/Lib `evt` / MState framework against the OLD statement (bcmp_wrap_contract). Its first half
   (dots_loop, synloop, fmtloop) compiled in earlier builds by its author's account; its second half (rest of
   rows_loop, minv_entry, linv_entry, cont_ok, look_ok, check_arity_holds) was never built. It is a TEMPLATE, NOT A
   SOURCE: porting it is a rewrite into another execution model, and our concrete-run method needs none of its loop
   invariants. Its pcs are cross-checks only. This walk (BASE = 0x864e4) agrees with each of them: it passes the
   syntax arm 0x874d8 (its :830) and the dots_loop head 0x87638 (its :457); it never reaches the format arm 0x87368
   (its :1255) or fmtloop 0x873dc (its :973), as a row without a format must not; the rows_loop head 0x87304 (its
   :1589) lies before the matched-row entry.

   The walk, measured by computation (the symbolic run with the call results supplied):
   - entry 0x87334 to the first call: 553 instructions;
   - 13 calls, all at `jal` 0x8764c (dots_loop's window scan), returning to 0x87650 (retk 4460 = 0x87650 - BASE),
     with a0 = 0x21773 + j (j = 0 .. 12, consecutive), a1 = A_OBJ 19 = "..." (0x21880), a2 = 3; call j uses the
     fresh junk band kk = 1024 + 16 j, and its a0 result is the atom kk + 4;
   - each call is followed at once by `beqz a0` 0x87650 (target 0x87710); between two calls, 8 instructions
     (0x87650, 0x87654 s8 += 1, 0x87658 bgeu back to 0x87638, 0x87638 .. 0x87648);
   - calls 0 .. 11: the three bytes differ from "...", so the branch falls through (the taken side is refuted):
     one ca_site_ne line each (check_arity_s7.v);
   - call 12 (x = 0x2177f) is the one call whose three bytes EQUAL "..." (the only such call of rows 0, 3, 8 and 14
     by a probe): the branch is TAKEN and the fall-through side is refuted, so this site is written out by hand.
     The row then runs 38 instructions to `ret`: 0x87710 .. 0x87714 set s4 = 0x7fffffff (the unbounded maximum),
     0x87718 reloads a6 from the frame slot 0(sp) (stored at 0x8762c), 0x8771c .. 0x87728 set a7 = '|', t0 = '>',
     t1 = 3, t4 = '[', and 0x8772c jumps back to the token scan at 0x87508; the scan reads the NUL at the end of the
     syntax string (0x87528, then 0x87548 `beqz` to 0x8773c) and leaves. At 0x8773c `blt s3, a6` and 0x87740
     `blt s4, s3` (the arity tests) fall through, both decided by the entry's facts on s3v; 0x87744 .. 0x87778
     reload ra and s0 .. s11 and pop the 112-byte frame; `ret` 0x8777c.

   The call is not walked: each site is one use of ca_bcmp_step (check_arity_s7.v). *)
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

(* the beqz a0 after the one call whose three bytes equal "...": ca_beqz_ne (check_arity_s7.v) mirrored, the
   fall-through side dies by HIFF and ca_eq3, the taken side is the walk *)
Ltac ca_beqz_eq RUNP BR :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ _ _, HIFF : _ <-> ca_eq3 _ _ = true |- _ =>
    psrr_branch_pi RUNP BR HS;
    [ lazymatch goal with Hc : branch_taken _ _ _ = true |- _ => clear Hc end; clear HIFF
    | exfalso;
      lazymatch goal with Hc : branch_taken _ _ _ = false |- _ =>
        rewrite branch_eq_U, U_SLit in Hc; apply Z.eqb_neq in Hc; change (zcanon 0) with 0 in Hc;
        apply Hc, HIFF; vm_compute; reflexivity end ]
  end.

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

Lemma ca_row_14 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre B 14 2 2147483647 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
getr regs0 3 = w64 (as_gp B) -> getr regs0 4 = w64 (as_tp B) ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post B regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP G3 G4.
pose proof (ca_row_open B HB 14 2 2147483647 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
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
(* calls 0 .. 11 (x = 0x21773 .. 0x2177e): the three bytes differ from "...", the beqz falls through *)
ca_site_ne CBS RUNP RUNC BR 14%nat 1024%nat.
ca_site_ne CBS RUNP RUNC BR 14%nat 1040%nat.
ca_site_ne CBS RUNP RUNC BR 14%nat 1056%nat.
ca_site_ne CBS RUNP RUNC BR 14%nat 1072%nat.
ca_site_ne CBS RUNP RUNC BR 14%nat 1088%nat.
ca_site_ne CBS RUNP RUNC BR 14%nat 1104%nat.
ca_site_ne CBS RUNP RUNC BR 14%nat 1120%nat.
ca_site_ne CBS RUNP RUNC BR 14%nat 1136%nat.
ca_site_ne CBS RUNP RUNC BR 14%nat 1152%nat.
ca_site_ne CBS RUNP RUNC BR 14%nat 1168%nat.
ca_site_ne CBS RUNP RUNC BR 14%nat 1184%nat.
ca_site_ne CBS RUNP RUNC BR 14%nat 1200%nat.
(* call 12 (x = 0x2177f): the three bytes equal "...", the beqz at 0x87650 is taken to 0x87710 *)
ca_run RUNP RUNC. ca_call CBS 14%nat 1216%nat. ca_run RUNP RUNC. ca_beqz_eq RUNP BR.
(* 0x87650 to `ret` 0x8777c (38 instructions) *)
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
