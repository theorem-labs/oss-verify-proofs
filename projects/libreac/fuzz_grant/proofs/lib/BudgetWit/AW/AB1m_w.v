(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1m.v, with its module paths changed. *) (* Modified by Theorem Labs, 2026-10: startup_cert is checked in parts that compile in parallel (AB1mW.v, AB1mK.v, AB1mP.v, AB1mA.v, AB1mB.v, AB1mC.v, AB1mS.v); no statement changed. This note and the Require of AB1mS (line 18) share existing lines, so that no declaration of this file moves. *)
(* Modified by Theorem Labs, 2026-11: made from A/AB1m.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: this twin does not Require A/AB1mS.v, and its startup_cert is not checked in the parts the
   note above names: those parts check the released Reusable/YA0c.v's APG.check at YA02.LIMIT, not YA0c_w's at
   YA02_w.LIMIT, and A/AB1mW.v's walk calls node_sys without the LIMIT argument YA0c_w.node_sys takes. It is checked
   whole by one vm_cast, as libreac/fuzz_identity's BudgetWit/AW/AB1m_w.v checks it. vm_cast_no_check skips only the
   check when the tactic runs; the kernel checks the cast by vm conversion at Qed, so startup_cert is proved here at
   YA02_w.LIMIT over YA0c_w, and nothing the parts prove is assumed. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 as this unit's lib/A/AB1m.v is, at the 16 GiB limit with its twin modules (changed startup_shape, startup_cert, tfibcert_fx, FSQ, tfib_startup_closed; added INP, RZ). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_grant.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK00 YK04.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import YK05_w.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK0c YK0e YK0f YK09 YK0a.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YA01.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import YA0c_w.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import YA0e_w YA0d_w YA0f_w YA02_w YA00_w YA0h_w.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import AB12.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import AB1h_w AB1k_w.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import YB1j_w.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import AB1p_w AB1l_w.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import AB05_w AB01r_w.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG. Import APSXG.
Open Scope Z_scope.
Definition BFUEL : nat := 400000%nat.
Definition KC0 : nat := 0%nat.
Definition FUEL : nat := 3000%nat.
Definition IT0 : itab := mk_itab_ranges TSEGS startup_plan_tfib_ranges.
Lemma IT0_ok : itab_sound TSEGS IT0.
Proof. apply mk_itab_ranges_sound. Qed.
Definition hole_le_tfib (h1 h2 : nat) : bool := true.
Definition startup_shape : shape :=
(SCase (EVar 6) 10 (SAlt2 (SAlt2 (SHole 8) (SHole 9)) (SAlt2 (SHole 0) (SHole 1))) (SCase (EVar 6) 1802 (SAlt2 (SAlt2 (SHole 24) (SHole 25)) (SAlt2 (SHole 16) (SHole 17))) (SAlt2 (SHole 36) (SHole 32)))).
(* THE CERTIFICATE OVER A FREE CONFIG_RSEQ FLAG.  The flag is [kb_rseq] of the run's own
   kernel record, which [Run.valid_input] leaves free, so the plan term
   [init_acs_of_g (rseq_z rs) TFIB] is open; [destruct] on the free boolean gives two closed
   checks, one per flag.  The hand-off states, the band join state and the plan's variable
   renumbering are [AB01r]'s, computed from the run in the build (the recorded [AB01_w.HS_tfib]
   and [AB03_w.JS_tfib_band] were written against the released launch).  As
   cgif/cgif_file_fuzzer's A/AB1m.v in this working copy. *)
Lemma startup_cert : forall rs : bool,
check TSEGS IT0 TFIB NX0G YA02_w.LIMIT (rseq_z rs) (XNG TSEGS tfib_XN1) XE0 XB0 (HS_tfib_r (rseq_z rs)) hole_le_tfib KC0 BFUEL FUEL None
(init_acs_of_g (rseq_z rs) TFIB) (startup_plan_tfib_r (rseq_z rs))
= COk startup_shape.
Proof. intros rs. destruct rs; vm_cast_no_check (@eq_refl cres (COk startup_shape)). Qed.
#[local] Instance tfibcert_fx : YK11.FPState := YK11.fx0.
Section a.
Variable sp : word. Variable rdraw : EntryDraw. Variable brk0 mbase : word. Variable argv envp : list (list byte).
Variable fs : Fs.Fs. Variable stdin : InputStream. Variables uid gid hw : word. Variable groups : list word. Variable net : NetQueue.
Variables nofile sigmask : word.
Variable urnd : InputStream. Variable tmp : Fs.Fs.
Variable kb : KernelBuild. Variable execfn : list byte. Variable sdef : bool.
Let INP : ProcInput := YA02_w.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef.
Let RZ : Z := rseq_z (kb_rseq (in_kernel INP)).
#[local] Notation FSQ := (fs_seed_tmp fs tmp).
Hypothesis Hsp : valid_sp sp. Hypothesis Hbrk : valid_brk TSEGS brk0. Hypothesis Hva : valid_argv argv. Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp. Hypothesis Huid : valid_id uid. Hypothesis Hhw : valid_hwcap hw.
Hypothesis Hmb : valid_mmap_base mbase. Hypothesis Hnof : valid_nofile nofile. Hypothesis Hsig : valid_sigmask INP.
Hypothesis Hvl : valid_launch INP. Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0G E E' -> HOLES h E fs' = HOLES h E' fs'.
Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
Hypothesis HOLES_le : forall h' h E fs' tr, hole_le_tfib h' h = true -> HOLES h' E fs' tr -> HOLES h E fs' tr.
Hypothesis HOLES_sound :
holes_stmt TSEGS TFIB YA02_w.LIMIT (YA02_w.TOP sp) (HS_tfib_r RZ)
(SINV0 TPH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef Asan.M.init_pc)
(argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) HOLES FSQ.
Theorem tfib_startup_closed :
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk0 mbase rdraw YA02_w.LIMIT INP)
(sd HOLES t_nil (E0 sp rdraw brk0 argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) FSQ startup_shape).
Proof.
(* [startup_cert] at the run's own flag: the caller supplies the branch. *)
eapply tfib_startup;
solve [ assumption | exact IT0_ok | exact (startup_cert (kb_rseq (in_kernel INP))) ].
Qed.
End a.
