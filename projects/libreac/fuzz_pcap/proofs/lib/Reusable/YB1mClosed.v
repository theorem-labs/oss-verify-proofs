(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1m.v:36-61 for libreac/fuzz_pcap's
   asan-ubsan image, with its module paths changed; the asan-ubsan twin of a Theorem Labs lane's lib/A/AB1mClosed.v
   (a working branch a2a160b29d1).
   NOTHING ELSE CHANGED: the section, its hypotheses and the single `exact` are the donor's, and the text
   holds no image literal -- AsanUbsan.M.init_pc, TSEGS, TFIB, HS_tfib, startup_shape and startup_cert all come
   from this unit's own files.
   WHY THIS FILE EXISTS: lib/Reusable/YB1m.v is GENERATED (a Theorem Labs lane's start-up collector) and ends after
   startup_cert (the split ruling). The donor's YB1m.v:36-61, which turns that equation into
   `tfib_startup_closed` through Reusable/YB1j.v's tfib_startup, is relocated proof text, so it lives here and
   YB1m stays data. lib/Reusable/YB1n.v takes tfib_startup_closed from this file.
   NAMING (agreed with a Theorem Labs lane): AB1m.v is a donor lib/A file, so this twin of
   lib/A/AB1mClosed.v is lib/Reusable/YB1mClosed.v (module ...lib.Reusable.YB1mClosed); it was lib/B/AB1mClosed.v. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_pcap.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK15 YK18 YK00 YK04 YK05 YK0c YK0e YK0f YK09 YK0a.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YB12 YB1h YB1k YB1j YB1p YB1l YB05 YB01 YB1m.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG. Import APSXG.
Open Scope Z_scope.
(* donor YB1m.v:36 *)
#[local] Instance tfibcert_fx : YK11.FPState := YK11.fx0.
(* donor YB1m.v:37-61 *)
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
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp))
(sd HOLES t_nil (E0 TPH sp rdraw brk0 argv envp uid hw) FSQ startup_shape).
Proof.
exact (tfib_startup sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
IT0 IT0_ok HS_tfib hole_le_tfib startup_plan_tfib startup_shape KC0 BFUEL FUEL startup_cert
HOLES HOLES_agree HOLES_nil HOLES_le HOLES_sound).
Qed.
End a.
