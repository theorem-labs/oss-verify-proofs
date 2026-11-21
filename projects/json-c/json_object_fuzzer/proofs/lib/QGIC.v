(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput: OBL_HANDOFF_REST_jo over its fields and QpvH.launch_ok, and jo_both_tgt_srealizes with entry_launch_ok_va, valid_launch, the channel reader and the kernel build from valid_input_either; the CONFIG_RSEQ flag of the start-up layer: HSCLASS_R at kb_rseq). *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.json_c.json_object_fuzzer.images Require Plain.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHdY.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Jo3 Require TargetJoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJur_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVWI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXVi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q45h. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvSK.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoL1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition OBL_HANDOFF_REST_jo : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (fs : Fs.Fs) (uid hw : word) (apc : N) (mbase : word) (ifs : Fs.Fs) (stdin : InputStream) (gid : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (abort_terminal : bool) (urnd : InputStream) (tmp : Fs.Fs) (kb : KernelBuild) (execfn : list byte) (rdr sgd sgt : bool)
(Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp) (Hfit : QpvH.launch_ok sp brk0 mbase rdraw (QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt))
E R FULL mo w ch (HCL : Q45h.HSCLASS_S w ch)
(HCLR : Q45h.HSCLASS_R (kb_rseq kb) w ch)
(CS : Q1LT.APS.cs_ok QXVi.JOB6SEGS QyaF.BJO6
QVWI.Mq0.LIMIT (bv_unsigned sp) (QpvH.SINV0 QXVi.JOB6PH apc sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt)
(QpvH.argH0 sp rdraw argv envp kb execfn) fs E ch R FULL mo),
QoL1.Mq0.handoff_rest sp rdraw brk0 argv envp fs uid hw apc mbase ifs stdin gid groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.

Theorem jo_both_tgt_srealizes : OBL_HANDOFF_REST_jo ->
forall sp brk mbase rnd (inp : ProcInput),
valid_sp sp -> valid_brk AsanUbsan.M.loaded_segments brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
valid_input_either inp ->
Q1lV.srealizes AsanUbsan.M.loaded_segments
(init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs
sp brk mbase rnd target_alloc_limit inp)
(spec (in_argv inp) (in_fs inp)).
Proof.
(* LPS 727298f3: the launch's whole ProcInput, its entry_launch_ok_va (valid_entry_va's fifth
conjunct), and valid_launch, the channel reader and the recorded kernel from valid_input_either. *)
intros OBL sp brk mbase rnd inp Hsp Hbrk Hmb Hfes Hlau
(Hva & Hve & _ & _ & _ & (Huid & _) & _ & _ & _ & Hsv & _ & Hlaunch & Hrdr & _ & Hk).
apply (QvSK.srz_C_to_A).
destruct inp as [argv envp ifs stdin uid gid groups net nofile sigmask hw abort_terminal vas urnd tmp kb execfn rdr sgd sgt].
unfold in_fs. cbn [in_argv in_envp in_image_fs in_tmp in_uid in_va_size in_channel_reader in_kernel] in *. subst vas.
exact (QoL1.Mq0.jo_both_srealizes sp rnd brk mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt
Hsp Hbrk Hmb Hva Hve (conj Hfes (conj Hk (conj Hlaunch Hlau))) Huid Hrdr
(fun E R FULL mo w ch HCL HCLR CS => OBL sp rnd brk argv envp (fs_seed_tmp ifs tmp) uid hw AsanUbsan.M.init_pc mbase ifs stdin gid groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt
Hsp Hva Hve (conj Hfes (conj Hk (conj Hlaunch Hlau))) E R FULL mo w ch HCL HCLR CS)).
Qed.

Theorem json_object_both_ba : OBL_HANDOFF_REST_jo ->
strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
intros OBL.
exact (QJur_c1.strong_universal_error_free_sanitizer_abort_of_mixed
Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs
AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs
(fun inp => spec (in_argv inp) (in_fs inp)) spec_kill_free_inp eq_refl eq_refl
(QHdY.drv_realizes_P_san OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Jo3.TargetJoP.target_P2_proof)
(jo_both_tgt_srealizes OBL)).
Qed.
