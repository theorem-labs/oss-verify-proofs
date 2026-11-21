(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1m.v:37-62
   (theorem-labs/oss-verify-proofs@6b32741d849a) for libreac/fuzz_pcap's ASan image, with its module paths changed.
   NOTHING ELSE CHANGED: the section, its hypotheses and the single `exact` are the donor's, and the text
   holds no image literal -- Asan.M.init_pc, TSEGS, TFIB, HS_tfib, startup_shape and startup_cert all come
   from this unit's own files.
   WHY THIS FILE EXISTS: lib/A/AB1m.v is GENERATED (a Theorem Labs lane's start-up collector) and the generator emits
   the certificate data only -- startup_shape and the `check ... = COk startup_shape` equation. The donor's
   AB1m.v:37-62, which turns that equation into `tfib_startup_closed` through Reusable/YB1j.v's tfib_startup,
   is relocated proof text, so it lives here instead and AB1m stays data. lib/A/AB1n.v takes
   tfib_startup_closed from this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed tfibcert_fx, FSQ, tfib_startup_closed; added INP, RZ). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_pcap.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK15 YK18 YK00 YK04 YK05 YK0c YK0e YK0f YK09 YK0a.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YA01 YA0c YA0e YA0d YA0f YA02 YA00 YA0h.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB12 AB1h AB1k.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1j.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1p AB1l AB05 AB01r AB1m.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG. Import APSXG.
Open Scope Z_scope.
(* donor A/AB1m.v:37 *)
#[local] Instance tfibcert_fx : YK11.FPState := YK11.fx0.
(* donor A/AB1m.v:38-62 *)
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
