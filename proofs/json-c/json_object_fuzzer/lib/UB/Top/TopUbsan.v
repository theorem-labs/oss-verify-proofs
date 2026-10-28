From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Plain.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QdTb Q1lV QJur QHdY.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Jo3 Require TargetJoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Embed.
Variable segs : list Segment.

Lemma rz_lb_srz : (forall c T, QRjH.realizes segs c T -> Q1lV.srealizes segs c T)
/\ (forall V T c, QRjH.lbody segs V T c -> Q1lV.slbody segs V T c).
Proof.
apply QRjH.realizes_lbody_mutind.
- intros c I evs nx T i0 Hn _ IH. exact (Q1lV.srz_node segs c I evs nx T i0 Hn IH).
- intros c Hh. exact (Q1lV.srz_halt segs c Hh).
- intros c T T' _ IH Heq. exact (Q1lV.srz_conseq segs c T T' IH Heq).
- intros V T c c_e HV _ IHb Hw _ IHe. exact (Q1lV.srz_loop segs V T c c_e HV IHb Hw IHe).
- intros V T c _ IH. exact (Q1lV.slb_exit segs V T c IH).
- intros V T c I nx k Hn _ IHk HV. exact (Q1lV.slb_node segs V T c I nx k Hn IHk HV).
Qed.

Lemma realizes_srealizes : forall c T, QRjH.realizes segs c T -> Q1lV.srealizes segs c T.
Proof. exact (proj1 rz_lb_srz). Qed.
End Embed.

Definition TGT_UBSAN_REALIZES : Prop :=
forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
valid_sp sp -> valid_brk Ubsan.M.loaded_segments brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_input_either inp ->
QRjH.realizes Ubsan.M.loaded_segments
(init_config Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(spec (in_argv inp) (in_fs inp)).

Section Top.
Hypothesis TGT : TGT_UBSAN_REALIZES.

Theorem json_object_ubsan_ba :
LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
(LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
(LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.phdrs)
(LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.M.loaded_segments OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.M.init_pc OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.M.phdrs).
Proof.
exact (QJur.strong_universal_error_free_budgets_abort_of_mixed_at
Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs
Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
(fun inp => spec (in_argv inp) (in_fs inp)) QSpR.spec_kill_free_inp
source_alloc_limit target_alloc_limit
(QHdY.drv_realizes_P OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Jo3.TargetJoP.target_P2_proof)
(fun sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hei =>
realizes_srealizes _ _ _ (TGT sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hei))).
Qed.
End Top.
