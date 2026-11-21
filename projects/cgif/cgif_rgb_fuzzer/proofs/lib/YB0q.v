(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the closed start-up certificate stated for either CONFIG_RSEQ flag and checked at both, the flag passed to check and init_acs_of_g, over the hand-off states and band join state computed from the run in YB00r.v with the recorded plan renumbered; tra_startup_closed stated over the run's ProcInput and mmap base in place of its separate fields, with the launch premises valid_launch and entry_launch_ok_va in place of entry_stack_fits and the recorded-kernel premise on the run's kernel, SINV0, argH0 and E0 over the input, and the certificate taken at the run's own flag; valid_input's channel-reader conjunct Hrdr passed to tra_startup for cs_ok's new co_rdr field). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK15 YK18 YK00 YK05 YK06 YK0d YK0f YK0g YK0a YK0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YB06 YB0l YB0o YB0n YB0t YB0p YB04 YB00r.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG. Import APSXG.
Open Scope Z_scope.
Definition BFUEL : nat := 400000%nat.
Definition KC0 : nat := 0%nat.
Definition FUEL : nat := 3000%nat.
Definition IT0 : itab := mk_itab_ranges TSEGS startup_plan_tra_ranges.
Lemma IT0_ok : itab_sound TSEGS IT0.
Proof. apply mk_itab_ranges_sound. Qed.
Definition hole_le_tra (h1 h2 : nat) : bool := true.
Definition startup_shape : shape :=
SCase (EVar 6) 10 (SAlt2 (SAlt2 (SAlt2 (SHole 14) (SHole 15)) (SAlt2 (SAlt2 (SHole 12) (SHole 13)) (SAlt2 (SAlt2 (SHole 10) (SHole 11)) (SAlt2 (SHole 8) (SHole 9))))) (SAlt2 (SAlt2 (SAlt2 (SHole 6) (SHole 7)) (SAlt2 (SHole 4) (SHole 5))) (SAlt2 (SAlt2 (SAlt2 (SHole 2) (SHole 3)) (SAlt2 (SHole 0) (SHole 1))) (SAlt2 (SAlt2 (SHole 42) (SHole 43)) (SAlt2 (SHole 40) (SHole 41))))))
(SCase (EVar 6) 1802 (SAlt2 (SAlt2 (SAlt2 (SHole 30) (SHole 31)) (SAlt2 (SAlt2 (SHole 28) (SHole 29)) (SAlt2 (SAlt2 (SHole 26) (SHole 27)) (SAlt2 (SHole 24) (SHole 25))))) (SAlt2 (SAlt2 (SAlt2 (SHole 22) (SHole 23)) (SAlt2 (SHole 20) (SHole 21))) (SAlt2 (SAlt2 (SAlt2 (SHole 18) (SHole 19)) (SAlt2 (SHole 16) (SHole 17))) (SAlt2 (SAlt2 (SHole 46) (SHole 47)) (SAlt2 (SHole 44) (SHole 45))))))
(SAlt2 (SAlt2 (SHole 39) (SAlt2 (SHole 38) (SAlt2 (SHole 37) (SHole 36)))) (SAlt2 (SAlt2 (SHole 35) (SHole 34)) (SAlt2 (SAlt2 (SHole 33) (SHole 32)) (SAlt2 (SHole 49) (SHole 48)))))).
(* #38: [init_acs_of_g] gained the run's CONFIG_RSEQ flag as its FIRST argument
   (YA01.v:719, via [init_kn_g] YA01.v:713).  This certificate is closed - no
   [inp] is in scope here - so it is stated for EITHER value of the flag and
   discharged at both, the idiom UL0g.v:263 / YL0g.v:261 use for the rseq-indexed
   closed facts.  The caller instantiates it at the run's own flag below, so
   [kb_rseq] stays free.
   #38 (rule 2g): [APG.check] gained the same flag as a section [Variable rz : Z]
   declared after [LIMIT] (YA0c.v), so it is also the sixth argument of the
   discharged [check].  The [forall rs] widening already supplies it - the SAME
   [rs] feeds both positions, so no binder is added and nothing is pinned. *)
(* At LPS 727298f3 the run's hand-off states and its band join state are spelled by the
   longer auxv and the [V_G]/[V_GID] variables, so they are no longer the recorded
   [YB00.HS_tra] / [YB02.JS_tra_band]: [YB00r.v] computes both per flag from the run, and the
   recorded plan [YB04.startup_plan_tra] is checked renumbered, with that join state in its one
   [PVia] ([YB00r.startup_plan_tra_r]). *)
Lemma startup_cert : forall rs : bool,
check TSEGS IT0 TRA NX0G YA02.LIMIT (APC.rseq_z rs) (XNG TSEGS tra_XN1) XE0 XB0 (HS_tra_r (APC.rseq_z rs)) hole_le_tra KC0 BFUEL FUEL None
(init_acs_of_g (APC.rseq_z rs) TRA) (startup_plan_tra_r (APC.rseq_z rs))
= COk startup_shape.
Proof. intros [|]; vm_cast_no_check (@eq_refl cres (COk startup_shape)). Qed.
Lemma startup_live : forall rs : bool, lv (startup_plan_tra_r (APC.rseq_z rs)) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
#[local] Instance tracert_fx : YK11.FPState := YK11.fx0.
Section a.
Variable sp : word. Variable rdraw : EntryDraw. Variable brk0 mbase : word.
(* 08b1429: over the run's input [inp], as YA02. *)
Variable inp : ProcInput.
#[local] Notation FSQ := (in_fs inp).
Hypothesis Hsp : valid_sp sp. Hypothesis Hbrk : valid_brk TSEGS brk0. Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv (in_argv inp). Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Huid : valid_id (in_uid inp). Hypothesis Hhw : valid_hwcap (in_hwcap inp).
Hypothesis Hlaunch : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
(* #38 (rules 12f, 12r): [valid_input]'s own recorded-kernel conjunct
   (75d69e00:Run.v:4596) in place of the whole-record pin; kb_rseq stays free. *)
Hypothesis Hrec : in_kernel inp = recorded_kernel (in_kernel inp).
(* LPS 727298f3: [valid_input]'s channel-reader conjunct, for [cs_ok]'s new last field
   [co_rdr]; [YB0p.tra_startup] takes it right after [Hrec]. *)
Hypothesis Hrdr : in_channel_reader inp = true.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0G E E' -> HOLES h E fs' = HOLES h E' fs'.
Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
Hypothesis HOLES_le : forall h' h E fs' tr, hole_le_tra h' h = true -> HOLES h' E fs' tr -> HOLES h E fs' tr.
Hypothesis HOLES_sound :
holes_stmt TSEGS TRA YA02.LIMIT (YA02.TOP sp) (HS_tra_r (APC.rseq_z (kb_rseq (in_kernel inp))))
(SINV0 TRA TPH sp rdraw brk0 mbase inp) (argH0 sp rdraw inp) HOLES FSQ.
Theorem tra_startup_closed :
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT
inp)
(sd HOLES t_nil (E0 sp rdraw brk0 inp) FSQ startup_shape).
Proof.
exact (tra_startup sp rdraw brk0 mbase inp Hsp Hbrk Hmb Hva Hve Huid Hhw Hlaunch Hlau Hrec Hrdr
IT0 IT0_ok (HS_tra_r (APC.rseq_z (kb_rseq (in_kernel inp)))) hole_le_tra
(startup_plan_tra_r (APC.rseq_z (kb_rseq (in_kernel inp)))) startup_shape KC0 BFUEL FUEL
(startup_cert (kb_rseq (in_kernel inp))) (startup_live (kb_rseq (in_kernel inp)))
HOLES HOLES_agree HOLES_nil HOLES_le HOLES_sound).
Qed.
End a.
