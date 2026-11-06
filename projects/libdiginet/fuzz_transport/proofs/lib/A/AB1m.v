(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1m.v at origin/ossv/recipes 25e3d17bdb50 with its module paths changed to libdiginet/fuzz_transport's split library. The donor's checker run on fuzz_transport's own states, plan and table (ZStartColR/Cert.v in the donor workspace; its build log, sha256 755cd85c89d0) returns (0, 0, Some <shape>) with exactly cgif's startup_shape, BFUEL 400000, FUEL 3000, KC0 0, so the text is unchanged. *)
(* Read from: fuzz_transport.asan (libdiginet/fuzz_transport asan) sha256 e89be137db17b720e0310addc2dcc601998945478a9102e6a9850b0566106350; unstripped twin sha256 86efc3a80314981197619c115e313dbde50e8b86a6c5fefad4e5cc420250c792 *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libdiginet.fuzz_transport.images Require Import Asan.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK15 YK18 YK00 YK04 YK05 YK0c YK0e YK0f YK09 YK0a.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB12 AB1h AB1k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YB1j.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1p AB1l AB05 AB01.
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
Lemma startup_cert :
check TSEGS IT0 TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib hole_le_tfib KC0 BFUEL FUEL None
(init_acs_of_g TFIB) startup_plan_tfib
= COk startup_shape.
Proof. vm_cast_no_check (@eq_refl cres (COk startup_shape)). Qed.
#[local] Instance tfibcert_fx : YK11.FPState := YK11.fx0.
Section a.
Variable sp : word. Variable rdraw : EntryDraw. Variable brk0 mbase : word. Variable argv envp : list (list byte).
Variable fs : Fs.Fs. Variable stdin : InputStream. Variables uid gid hw : word. Variable groups : list word. Variable net : NetQueue.
Variables nofile sigmask : word.
Variable urnd : InputStream. Variable tmp : Fs.Fs.
#[local] Notation FSQ := (fs_seed_tmp fs tmp).
Hypothesis Hsp : valid_sp sp. Hypothesis Hbrk : valid_brk TSEGS brk0. Hypothesis Hva : valid_argv argv. Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp. Hypothesis Huid : valid_id uid. Hypothesis Hhw : valid_hwcap hw.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0G E E' -> HOLES h E fs' = HOLES h E' fs'.
Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
Hypothesis HOLES_le : forall h' h E fs' tr, hole_le_tfib h' h = true -> HOLES h' E fs' tr -> HOLES h E fs' tr.
Hypothesis HOLES_sound :
holes_stmt TSEGS TFIB YA02.LIMIT (YA02.TOP sp) HS_tfib
(SINV0 TPH sp rdraw brk0 argv envp uid hw) (argH0 TPH sp rdraw argv envp uid hw) HOLES FSQ.
Theorem tfib_startup_closed :
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp))
(sd HOLES t_nil (E0 TPH sp rdraw brk0 argv envp uid hw) FSQ startup_shape).
Proof.
exact (tfib_startup sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
IT0 IT0_ok HS_tfib hole_le_tfib startup_plan_tfib startup_shape KC0 BFUEL FUEL startup_cert
HOLES HOLES_agree HOLES_nil HOLES_le HOLES_sound).
Qed.
End a.
