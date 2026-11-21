(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10-29: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1m.v, with its module paths changed; this is the form the image-B' collector's certificate used (harness fix #102, pin d663f82d7f488d30, unstripped twin c90d4fa54d43160b). The certificate file of that run is ZStartColRB/Cert.v of the donor workspace (worktree h-pre-b3-donor2/proofs/cgif/cgif_file_fuzzer/lib/ZStartColRB/Cert.v, written by tools/startup/colrun.py install, run sha 59778df6f00b34ac): the same IT0 = mk_itab_ranges TSEGS startup_plan_tfib_ranges, the same BFUEL 400000 and FUEL 3000, and the same `check` application over HS_tfib and startup_plan_tfib. Its `Eval vm_compute` printed (0, 0, Some (SCase (EVar 6) 10 (SAlt2 (SAlt2 (SHole 8) (SHole 9)) (SAlt2 (SHole 0) (SHole 1))) (SCase (EVar 6) 1802 (SAlt2 (SAlt2 (SHole 24) (SHole 25)) (SAlt2 (SHole 16) (SHole 17))) (SAlt2 (SHole 36) (SHole 32))))) -- COk with exactly the startup_shape below, holes 0,1,8,9,16,17,24,25,32,36, so the shape and the two fuels of this file are unchanged by the re-pin and no numeral here moves. Build rc=0, wall 1,023 s, log worktree h-pre-b3-donor2.logs/hpb3-donor-b-rbuild-20261029T154734Z.log; record h-pre-b3's PREP.md. The plan it accepted is lib/Reusable/YB05.v and the states lib/Reusable/YB01.v / YB03.v of this tree. *)
(* Modified by Theorem Labs, 2026-10-29: route R1 (h-hpreset-7; merged here) edits this file: SINV0 in the hypothesis HOLES_sound is applied to TSEGS as its new first argument. A re-relocation from cgif must re-apply it. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revision's launch (CONFIG_RSEQ-sized auxv, execfn, group id, launch premises); the input-owned, top-anchored launch stack; the start-up certificate per CONFIG_RSEQ flag with states computed in the build). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK15 YK18 YK00 YK04 YK05 YK0c YK0e YK0f YK09 YK0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YB12 YB1h YB1k YB1j YB1p YB1l YB05 YB01r.
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
   renumbering are [AB01r]'s, computed from the run in the build (the recorded [AB01.HS_tfib]
   and [AB03.JS_tfib_band] were written against the released launch).  As
   cgif/cgif_file_fuzzer's A/AB1m.v in this working copy. *)
Lemma startup_cert : forall rs : bool,
check TSEGS IT0 TFIB NX0G YA02.LIMIT (rseq_z rs) (XNG TSEGS tfib_XN1) XE0 XB0 (HS_tfib_r (rseq_z rs)) hole_le_tfib KC0 BFUEL FUEL None
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
Let INP : ProcInput := YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef.
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
holes_stmt TSEGS TFIB YA02.LIMIT (YA02.TOP sp) (HS_tfib_r RZ)
(SINV0 TSEGS TPH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef AsanUbsan.M.init_pc)
(argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) HOLES FSQ.
Theorem tfib_startup_closed :
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT INP)
(sd HOLES t_nil (E0 sp rdraw brk0 argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) FSQ startup_shape).
Proof.
(* [startup_cert] at the run's own flag: the caller supplies the branch. *)
eapply tfib_startup;
solve [ assumption | exact IT0_ok | exact (startup_cert (kb_rseq (in_kernel INP))) ].
Qed.
End a.
