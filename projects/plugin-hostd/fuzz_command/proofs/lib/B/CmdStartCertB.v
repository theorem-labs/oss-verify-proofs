(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c, with the theorem statements restated in the form rc.2 states them; adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AB01.v (HS_tfib, HS_tfib_In) and AB1n.v (HS_ok, tfib_startup_T1, HS_ok_open), with its module paths changed; the start-up certificate's hole states are the field of class StartData and tfib_startup_T1 is the field of class StartThm, Section hypotheses until plugin-hostd/fuzz_command's certificate is generated; class TfibHolesStkAux states that every hole state reads the auxv and AT_RANDOM words (StartStkAuxG.stk_aux_chk), which the driver needs for the stack's presence at main. *)
(* Modified by Theorem Labs, 2026-10: copied from this harness's lib/A/CmdStartCert.v, with its module paths changed (lib/A to lib/B, image Asan to AsanUbsan) and its addresses moved to plugin-hostd/fuzz_command's ASan+UBSan build. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK15 YK18 YK0c YK0e YK09 YA01 YA0c YA0e YA02.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB12 YB1h StartStkAuxG.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
Class StartData := { HS_tfib_list : list acs }.
Definition HS_tfib {SD : StartData} (h : nat) : option acs := nth_error HS_tfib_list h.
Lemma HS_tfib_In {SD : StartData} : forall h ch, HS_tfib h = Some ch -> In ch HS_tfib_list.
Proof. intros h ch H. unfold HS_tfib in H. exact (nth_error_In _ _ H). Qed.
Class TfibHolesStkAux {SD : StartData} : Prop := { tfib_holes_stkaux_c : forallb stk_aux_chk HS_tfib_list = true }.
Section f.
#[local] Existing Instance YK11.fx0.
Context {SD : StartData}.
Definition HS_ok (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs)
(c : config) : Prop :=
exists ch E R FULL model,
HS_tfib h = Some ch
/\ c = cfg_of TSEGS R (pc ch) FULL model
/\ cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
(SINV0 TPH sp rdraw brk0 argv envp uid hw) (argH0 TPH sp rdraw argv envp uid hw) fs E ch R FULL model.
Class StartThm : Prop := { tfib_startup_T1 :
forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
(uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs),
valid_sp sp -> valid_brk TSEGS brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
valid_id uid -> valid_hwcap hw ->
forall T : TSet, T [] ->
(forall h c, HS_ok h sp rdraw brk0 argv envp uid hw (fs_seed_tmp fs tmp) c -> srealizes TSEGS c T) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) T }.
Lemma HS_ok_open : forall h sp rdraw brk0 argv envp uid hw fs c,
HS_ok h sp rdraw brk0 argv envp uid hw fs c ->
exists ch E R FULL model,
HS_tfib h = Some ch /\ c = cfg_of TSEGS R (pc ch) FULL model
/\ cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
(SINV0 TPH sp rdraw brk0 argv envp uid hw) (argH0 TPH sp rdraw argv envp uid hw) fs E ch R FULL model
/\ (forall n, (n < NX0G)%nat -> ev E n = ev (E0 TPH sp rdraw brk0 argv envp uid hw) n)
/\ (forall a, argH0 TPH sp rdraw argv envp uid hw E a = true -> FULL a = wrap_mem TPH sp argv envp uid hw rdraw a)
/\ eb E = eb (E0 TPH sp rdraw brk0 argv envp uid hw).
Proof.
intros h sp rdraw brk0 argv envp uid hw fs c (ch & E & R & FULL & model & Hh & Hc & HC).
exists ch, E, R, FULL, model. split; [exact Hh|]. split; [exact Hc|]. split; [exact HC|].
exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.
End f.
