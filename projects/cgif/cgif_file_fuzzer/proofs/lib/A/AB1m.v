(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises entry_launch_ok_va and valid_input; the run's CONFIG_RSEQ flag; AT_EXECFN; the launch's group id; the start-up hand-off states computed in the build; the launch's SIGPIPE disposition left free): changed startup_shape, startup_cert, HOLES_sound, tfib_startup_closed; added kb, execfn, sdef, INP, RZ, Hmb, Hzr, Hnof and 4 more. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK15 YK18 YK00 YK04 YK05 YK06 YK0c YK0e YK0f YK09 YK0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB12 AB1h AB1k.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YB1j.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1p AB1l AB05 AB01r.
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
(* THE CERTIFICATE OVER A FREE CONFIG_RSEQ FLAG.
   [init_acs_of_g] takes the flag as [YK09.rseq_z] writes it since the start-up port, and the flag
   itself is [kb_rseq kb] on the run's OWN kernel record, which [Run.valid_input]'s conjunct
   17 leaves FREE (75d69e00:theories/LinuxProcessSem/Run.v:4596).  With the flag free the
   plan term [init_acs_of_g RZ TFIB] is OPEN -- [YK0c]'s smart constructors end in a
   [Z.eqb (fst x) 0] that is a stuck match until the index is a literal -- so a single
   [vm_cast_no_check] cannot decide it.
   The fix is a BRANCH LABEL, not a pin: [destruct] the free boolean and discharge each of the
   two branches by its own CLOSED [vm_compute].  No [Hypothesis kb_rseq kb = true] is stated,
   no kernel record is fixed, and the lemma below holds for BOTH rseq-on and rseq-off builds.
   At LPS 727298f3 the run's hand-off states and its band join state are spelled by the
   longer auxv and the [V_G]/[V_GID] variables, so they are no longer the recorded
   [AB01.HS_tfib] / [AB03.JS_tfib_band]: [AB01r.v] computes both per flag from the run, and
   the recorded plan [AB05.startup_plan_tfib] is checked with that join state in its one
   [PVia] ([AB01r.startup_plan_tfib_r]). *)
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
Variable kb : KernelBuild.
Variable execfn : list byte.
Variable sdef : bool.
Let INP : ProcInput := YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef.
Let RZ : Z := rseq_z (kb_rseq kb).
#[local] Notation FSQ := (fs_seed_tmp fs tmp).
Hypothesis Hsp : valid_sp sp. Hypothesis Hbrk : valid_brk TSEGS brk0. Hypothesis Hva : valid_argv argv. Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp. Hypothesis Huid : valid_id uid. Hypothesis Hhw : valid_hwcap hw.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hzr : YK06.zero_random_draw (ed_random rdraw).
Hypothesis Hnof : valid_nofile nofile.
Hypothesis Hsig : valid_sigmask INP.
Hypothesis Hlaunch : valid_launch INP.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
Hypothesis Hvi : valid_input INP.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0G E E' -> HOLES h E fs' = HOLES h E' fs'.
Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
Hypothesis HOLES_le : forall h' h E fs' tr, hole_le_tfib h' h = true -> HOLES h' E fs' tr -> HOLES h E fs' tr.
Hypothesis HOLES_sound :
holes_stmt TSEGS TFIB YA02.LIMIT (YA02.TOP sp) (HS_tfib_r RZ)
(SINV0 TPH Asan.M.init_pc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef)
(argH0 sp rdraw argv envp kb execfn) HOLES FSQ.
Theorem tfib_startup_closed :
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT INP)
(sd HOLES t_nil (E0 sp rdraw brk0 argv envp uid gid hw kb execfn) FSQ startup_shape).
Proof.
(* [startup_cert] is instantiated at the run's OWN flag [kb_rseq kb].  That is the whole point
   of the [destruct] above: the caller supplies the branch, the lemma never asks which. *)
eapply tfib_startup;
solve [ assumption | exact IT0_ok | exact (startup_cert (kb_rseq kb)) ].
Qed.
End a.
