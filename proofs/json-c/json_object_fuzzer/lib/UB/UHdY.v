(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udbv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udbv. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFOH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFOH.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWQV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWQV.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1oC.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1zM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1zM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmsF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmsF. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UleT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UleT.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ujk3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ujk3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmAj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmAj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udkw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udkw.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UYot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UYot. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3dw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3dw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UkF0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UkF0.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

#[local] Existing Instance fp0F.
#[local] Existing Instance fp0C.

Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
induction p as [|a p IH]; intros [|b q]; cbn [list_byte_eqb]; split; intros H; try discriminate; try reflexivity.
- apply andb_prop in H as [H1 H2]. unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b.
f_equal. apply IH. exact H2.
- injection H as <- <-. apply andb_true_intro. split; [unfold bv_eqb; apply Z.eqb_refl| apply IH; reflexivity].
Qed.

Lemma list_byte_eqb_false : forall p q, list_byte_eqb p q = false -> p <> q.
Proof. intros p q H E. apply (proj2 (list_byte_eqb_eq p q)) in E. rewrite E in H. discriminate. Qed.

Definition target_P : Prop := forall (RC__ : RunConsts) (HIx : heap_iface S4L), target_stmt S4L HIx 0x21024 hglob_P.

Section Top.
Context {AMB : Amb}.
Context {SL : SrcLim}.
Hypothesis TGT : target_P.

#[using="TGT"] Theorem drv_main_spec : forall (sp0 : word) (av envv : list (list byte)) (tid : word) (regs0 : bvmap 5 word)
(mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
valid_argv av -> valid_envp envv -> valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
main_entry sp0 av envv tid regs0 mem0 -> valid_brk RSEGS brk ->
a_sp = sp0 -> entry_stack_fits sp0 av envv ->
realizes RSEGS (mkCfg (mkst regs0 (0x20b84%bv : word) mem0 (seg_rom RSEGS))
(with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC av envv fs0 stdin0))))
(spec av fs0).
Proof.
intros sp0 av envv tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk ASP Hfit.
unfold spec.
destruct av as [|a0s [|path [|x rest]]].
- apply (UmsF.ref_usage_w sp0 [] envv tid regs0 mem0 brk mbase fs0 stdin0 LIM Hva Hve Hvsp Htid ME); [cbn; lia| exact Hfit].
- apply (UmsF.ref_usage_w sp0 [a0s] envv tid regs0 mem0 brk mbase fs0 stdin0 LIM Hva Hve Hvsp Htid ME); [cbn; lia| exact Hfit].
- destruct (Nat.leb_spec 4096 (length path)) as [LONG|SHORT].
+ apply (UleT.ref_open_fail_toolong_w sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 LIM Hva Hve Hvsp Htid ME Hfit). exact LONG.
+ destruct (list_byte_eqb path []) eqn:EMP.
* apply list_byte_eqb_eq in EMP.
apply (UleT.ref_open_fail_empty_w sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 LIM Hva Hve Hvsp Htid ME Hfit). exact EMP.
* apply list_byte_eqb_false in EMP.
destruct (list_byte_eqb path dot_path) eqn:DOT.
-- apply list_byte_eqb_eq in DOT.
replace (0x20b84%bv : word) with (Z_to_bv 64 0x20b84) by (apply bv_eq; reflexivity).
apply (drv_main_dir sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk EMP ltac:(lia) eq_refl ASP Hfit DOT).
-- apply list_byte_eqb_false in DOT.
destruct (fs_lookup fs0 path) as [data|] eqn:FS.
++ replace (0x20b84%bv : word) with (Z_to_bv 64 0x20b84) by (apply bv_eq; reflexivity).
apply (drv_main_file sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk EMP ltac:(lia) eq_refl ASP Hfit (TGT _ _) data DOT FS).
++ apply (UleT.ref_open_fail_absent_w sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 LIM Hva Hve Hvsp Htid ME Hfit); [lia| exact EMP| exact DOT| exact FS].
- apply (UmsF.ref_usage_w sp0 (a0s :: path :: x :: rest) envv tid regs0 mem0 brk mbase fs0 stdin0 LIM Hva Hve Hvsp Htid ME); [cbn; lia| exact Hfit].
Qed.
End Top.

Theorem drv_start_spec_lim : forall (lim : Z) (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
2^31 <= lim ->
target_P ->
valid_sp sp -> valid_brk rsegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
realizes rsegs (init_config rsegs Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rnd lim inp) (spec (in_argv inp) (in_fs inp)).
Proof.
intros lim sp brk mbase rnd inp Hlim TGT Hsp Hbrk Hva Hve Hfit.
apply (ref_startup sp brk mbase rnd lim inp _ Hsp); [exact Hbrk| exact Hva| exact Hve|].
intros tid regs mem Htid ME.
rewrite <- (init_model_C_of inp rnd sp Hsp).
exact (@drv_main_spec (amb_of inp rnd sp Hsp) (mkSrcLim lim Hlim) TGT sp (in_argv inp) (in_envp inp) tid regs mem brk mbase (in_fs inp) (in_stdin inp)
Hva Hve Hsp Htid ME Hbrk (a_sp_of inp rnd sp Hsp) Hfit).
Qed.

Theorem drv_realizes_P_lim : forall lim : Z, 2^31 <= lim -> target_P ->
forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
valid_sp sp -> valid_brk Ubsan.M.loaded_segments brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_input_either inp ->
realizes Ubsan.M.loaded_segments
(init_config Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rnd lim inp)
(spec (in_argv inp) (in_fs inp)).
Proof.
intros lim Hlim TGT sp brk mbase rnd inp Hsp Hbrk _ Hfit (Hva & Hve & _). exact (drv_start_spec_lim lim sp brk mbase rnd inp Hlim TGT Hsp Hbrk Hva Hve Hfit).
Qed.

Theorem drv_realizes_P : target_P ->
forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
valid_sp sp -> valid_brk Ubsan.M.loaded_segments brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_input_either inp ->
realizes Ubsan.M.loaded_segments
(init_config Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rnd source_alloc_limit inp)
(spec (in_argv inp) (in_fs inp)).
Proof. exact (drv_realizes_P_lim source_alloc_limit SrcLim_shipped_ge). Qed.

Theorem drv_realizes_P_san : target_P ->
forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
valid_sp sp -> valid_brk Ubsan.M.loaded_segments brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_input_either inp ->
realizes Ubsan.M.loaded_segments
(init_config Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rnd sanitizer_source_limit inp)
(spec (in_argv inp) (in_fs inp)).
Proof. exact (drv_realizes_P_lim sanitizer_source_limit SrcLim_sanitizer_ge). Qed.
