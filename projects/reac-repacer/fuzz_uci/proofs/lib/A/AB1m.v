(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1m.v at theorem-labs/oss-verify-proofs@6b32741d849a with its module paths changed to reac-repacer/fuzz_uci's split library. The donor's checker run on fuzz_uci's own states, plan and table (ZStartColR/Cert.v in the donor workspace; its build log, sha256 5390ade22da5; 656 s of vm_compute) returns (0, 0, Some <shape>) with exactly cgif's startup_shape, BFUEL 400000, FUEL 3000, KC0 0, so the text is unchanged. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input that leaves the SIGPIPE default free; the run's own kernel record and CONFIG_RSEQ flag; the exec file name; the launch premises valid_launch and entry_launch_ok_va; the start-up hand-off states computed from the run; as libreac/fuzz_decode's port); internal commit ids in comments replaced by public commits or removed. *)
(* Read from: fuzz_uci.asan (reac-repacer/fuzz_uci asan) sha256 6ea017c24525e6946fa06dc7e3075459ad2c5146d59af49873bf3c51a46e885d; unstripped twin sha256 56822e263d767986a76ec862cbfbee7571b0e64df2413ad18d7201205a7563fb *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_repacer.fuzz_uci.images Require Import Asan.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK15 YK18 YK00 YK04 YK05 YK0c YK0e YK0f YK09 YK0a.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB12 AB1h AB1k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YB1j.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1p AB1l AB05 AB01r.
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
(SINV0 TPH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef Asan.M.init_pc)
(argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) HOLES FSQ.
Theorem tfib_startup_closed :
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT INP)
(sd HOLES t_nil (E0 sp rdraw brk0 argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) FSQ startup_shape).
Proof.
(* [startup_cert] at the run's own flag: the caller supplies the branch. *)
eapply tfib_startup;
solve [ assumption | exact IT0_ok | exact (startup_cert (kb_rseq (in_kernel INP))) ].
Qed.
End a.
