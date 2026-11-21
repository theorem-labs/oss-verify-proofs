(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Js0Startup.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: ref_startup_sec_b unfolded from its encoded Section SE into a plain lemma over a whole ProcInput, and ref_startup_b gains valid_launch and entry_launch_ok_va premises, a vDSO-initialised model and a stack_zero-based J0, as in fuzz_bigint's copy; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/BudgetWit/Src0StartupB.v, 54 lines within its lines 13-182. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes RefNodes FileSim StartupTac ArgvEnv RefLayout Js0Img Js0StartupDefs Js0Startup1 Js0Memset Js0Startup2 Js0Startup3 Js0Startup4.
Import ListNotations.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Js0Startup.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit Require Import RefNodesB SpinAlgB.
Open Scope bv_scope.
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Lemma bwd_rz_b : (forall (segs : (@Corelib.Init.Datatypes.list (@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment))), (forall (scfg : (@LinuxProcessSemantics.LinuxProcessSem.Run.SpuriousCfg)), (forall (model : (@LinuxProcessSemantics.LinuxProcessSem.State.Model)), (forall (K : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.TSet)), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 64%positive))) (@LinuxProcessSemantics.LinuxProcessSem.State.m_halted model) (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv (Npos 64%positive))))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.list (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))) (@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy model) (@Corelib.Init.Datatypes.nil (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))))), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StartupTac.bwd segs (fun (st : (@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state)) => (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb segs scfg (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg st model) K))))))))).
Proof.
intros segs scfg model K Hh Hlazy st st' Hms Hst'. eapply SpinAlgB.rzb_msteps; eassumption.
Qed.
Section Assembly.
Variable scfg : SpuriousCfg.
Variable inp : ProcInput.
Variable mbase : word.
Variable sp brk : word.
Variable rdraw : EntryDraw.
Local Notation argv := (in_argv inp) (only parsing).
Local Notation envp := (in_envp inp) (only parsing).
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hvsp : valid_sp sp.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp.
Local Notation ENT := (0x33a60 : word) (only parsing).
Lemma Hlo : (@Stdlib.ZArith.BinInt.Z.le (Zpos 140735340871680%positive) (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) sp)).
Proof. destruct Hvsp as [H _]. exact H. Qed.
Lemma Hhi : (@Stdlib.ZArith.BinInt.Z.le (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) sp) (Zpos 140737488355328%positive)).
Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
Lemma Hal : (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@Stdlib.ZArith.BinInt.Z.modulo (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) sp) (Zpos 16%positive)) Z0).
Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.
Let J0 : word -> option byte := stack_zero (stack_window_lo (in_kernel inp) mbase rdraw).
Lemma HJ0 : wfJ sp J0.
Proof. exact (wfJ_stack_zero inp sp brk mbase rdraw Hvl Hlau). Qed.
Ltac side Hva Hve HG :=
first [ exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hlo | exact Hhi | exact Hal | exact HG
| exact HJ0
| lazymatch goal with |- getr _ _ = _ =>
gres; first [ assumption | reflexivity | bveq
| match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w, argcN;
first [reflexivity | f_equal; lia | bveq] end ] end
| idtac ].
Theorem ref_startup_sec_b : forall lim K,
(forall tid regs mem,
(0 < bv_unsigned tid < 2^22)%Z ->
Js0Startup.main_entry inp mbase ENT sp argv envp (in_uid inp) (in_hwcap inp) rdraw tid regs mem ->
SpinAlgB.rzb rsegs scfg (mkCfg (mkst regs (0x33bac : word) mem (seg_rom rsegs))
(with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
(init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
SpinAlgB.rzb rsegs scfg (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
Proof.
intros lim K.
intros HK.
pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
pose proof (u64_range sp) as Hsp.
unfold init_config. cbn [cfg_ms cfg_model].
set (model := with_vdso (Vdso.vdso_run_init (ed_vdso rdraw)) (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
assert (Hh : m_halted model = None) by reflexivity.
assert (Hlazy : m_vm_lazy model = []) by reflexivity.
assert (Ht0 : m_tid model = None) by reflexivity.
set (RZ := fun st : machine_state => SpinAlgB.rzb rsegs scfg (mkCfg st model) K).
assert (HG : bwd rsegs RZ) by (apply bwd_rz_b; [exact Hh | exact Hlazy]).
rewrite init_mkst.
replace (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) with (0x33a60 : word) by (apply bv_eq; reflexivity).
rewrite (cmem_init inp mbase RPH ENT sp brk rdraw Hlau). fold (regs_init sp). fold J0.
destruct (p1_run Sv48 inp mbase ENT sp brk rdraw Hva Hve Hvl Hlau Hlo' Hhi' Hal' (seg_rom SEGS) J0 HJ0)
as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact R1 |].
assert (A1' : getr regs1 1 = (0x98194 : word)) by (rewrite A1; apply bv_eq; reflexivity).
destruct (memset304_run regs1 (cmem sp (wrap_mem inp mbase RPH ENT sp rdraw) (J1 inp sp J0) (fun _ => None))
(seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x98194 : word) A1')
as [regs2 [mem2 (R2 & M2 & G2)]].
{ unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
{ exact A10. } { exact A11. } { exact A12. }
{ rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
{ rewrite u_Z2bv by lia. lia. }
{ apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; exact HJ0 | region_side | region_side]. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
rewrite wbytes_cmem_win by region_side.
carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
carry G2 A3 (3:reg) B3.
change (SpinAlgB.rzb SEGS scfg (mkCfg ?st model) K) with (RZ st).
eapply (p3_run Sv48 inp mbase ENT sp brk rdraw) with (G := RZ); try side Hva Hve HG.
{ unfold J1; repeat apply wfJ_wbytes; exact HJ0. }
intros regs3 C1 C2 C10 C18 G3.
carry G3 B3 (3:reg) C3. carry G3 B8 (8:reg) C8.
assert (Cz : forall r : reg, In r [5; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs3 r = Z_to_bv 64 0).
{ intros r Hr. rewrite (G3 r), (G2 r); [apply Az; exact Hr | |];
clear -Hr; cbn [In] in Hr; intros HH; cbn [In] in HH;
repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
pose proof (Cz 19 ltac:(in_list)) as Z19. pose proof (Cz 20 ltac:(in_list)) as Z20.
pose proof (Cz 21 ltac:(in_list)) as Z21. pose proof (Cz 22 ltac:(in_list)) as Z22.
pose proof (Cz 23 ltac:(in_list)) as Z23. pose proof (Cz 24 ltac:(in_list)) as Z24.
pose proof (Cz 25 ltac:(in_list)) as Z25. pose proof (Cz 26 ltac:(in_list)) as Z26.
pose proof (Cz 27 ltac:(in_list)) as Z27.
change (J1 inp sp J0) with (J_lsm inp sp J0).
eapply (tls_c1 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
intros regs4a; intros.
eapply (tls_c2 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
intros regs4b; intros.
eapply (tls_c3 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
intros regs4c; intros.
eapply (tls_c4 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
intros regs4; intros.
unfold RZ at 1.
eapply (RefNodesB.rz_set_tid_b SEGS scfg regs4 (0x986e4 : word) _ (seg_rom SEGS) model K (ltac:(oW' 0x986e4%Z)) (ltac:(oF' 0x986e4%Z)) (ltac:(oE' 0x986e4%Z)));
[exact Hh | exact Hlazy | assumption | exact Ht0 |].
intros tid Htid.
replace (v_addi (0x986e4 : word) 4) with (0x986e8 : word) by (apply bv_eq; reflexivity).
set (model' := with_tid tid model).
assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
set (RZ' := fun st : machine_state => SpinAlgB.rzb rsegs scfg (mkCfg st model') K).
assert (HG' : bwd rsegs RZ') by (apply bwd_rz_b; [exact Hh' | exact Hlazy']).
change (SpinAlgB.rzb SEGS scfg (mkCfg ?st model') K) with (RZ' st).
eapply (tls_c5 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ'); try side Hva Hve HG'.
intros regs5; intros.
eapply (fin_c6 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ'); try side Hva Hve HG'.
intros regs6; intros.
eapply (fin_c7 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ'); try side Hva Hve HG'.
intros regs7; intros.
eapply (fin_c8 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ'); try side Hva Hve HG'.
intros regs8; intros.
eapply (fin_c9 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ'); try side Hva Hve HG'.
intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
unfold RZ'. apply (HK tid regs9). { exact Htid. }
split; try assumption.
- intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
- exists brk, (Js0Startup.J_main inp mbase ENT sp rdraw J0 (getr regs3 9)).
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact Hvl|]. split; [exact Hlau|].
split; [|split; [exists J0, (getr regs3 9); reflexivity|]].
+ unfold Js0Startup.J_main, J_tls, J_aux, J_lsm. repeat apply wfJ_wbytes. exact HJ0.
+ unfold Js0Startup.J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
Qed.
End Assembly.
Theorem ref_startup_b : (forall (scfg : (@LinuxProcessSemantics.LinuxProcessSem.Run.SpuriousCfg)), (forall (sp : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (brk : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (mbase : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (rdraw : (@LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw)), (forall (lim : (@Corelib.Numbers.BinNums.Z)), (forall (inp : (@LinuxProcessSemantics.LinuxProcessSem.State.ProcInput)), (forall (K : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.TSet)), (forall (_ : (@LinuxProcessSemantics.LinuxProcessSem.Run.valid_sp sp)), (forall (_ : (@LinuxProcessSemantics.LinuxProcessSem.Run.valid_brk (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) brk)), (forall (_ : (@LinuxProcessSemantics.LinuxProcessSem.Run.valid_argv (@LinuxProcessSemantics.LinuxProcessSem.State.in_argv inp))), (forall (_ : (@LinuxProcessSemantics.LinuxProcessSem.Run.valid_envp (@LinuxProcessSemantics.LinuxProcessSem.State.in_envp inp))), valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
(forall (_ : (forall (tid : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (regs : (@LinuxProcessSemantics.Riscv.Prelude.bvmap (Npos 5%positive) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (mem : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (_ : (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt Z0 (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) tid)) (@Stdlib.ZArith.BinInt.Z.lt (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) tid) (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 22%positive))))), (forall (_ : (Js0Startup.main_entry inp mbase (0x33a60 : word) sp (@LinuxProcessSemantics.LinuxProcessSem.State.in_argv inp) (@LinuxProcessSemantics.LinuxProcessSem.State.in_envp inp) (@LinuxProcessSemantics.LinuxProcessSem.State.in_uid inp) (@LinuxProcessSemantics.LinuxProcessSem.State.in_hwcap inp) rdraw tid regs mem)), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) scfg (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.mkst (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.fx0) regs ((@stdpp.bitvector.definitions.BV (Npos 64%positive) (Zpos 211884%positive) (@Corelib.Init.Logic.I)) : (@stdpp.bitvector.definitions.bv (Npos 64%positive))) mem (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.seg_rom (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments))) (@LinuxProcessSemantics.LinuxProcessSem.State.with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
(@LinuxProcessSemantics.LinuxProcessSem.State.init_model (@LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments)) brk mbase sp lim inp)))) K))))))), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) scfg (@LinuxProcessSemantics.LinuxProcessSem.Run.init_config (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.init_pc) (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.phdrs) sp brk mbase rdraw lim inp) K)))))))))))))).
Proof.
intros scfg sp brk mbase rdraw lim inp K Hsp Hbrk Hva Hve Hvl Hlau HK.
exact (ref_startup_sec_b scfg inp mbase sp brk rdraw Hva Hve Hsp Hvl Hlau lim K HK).
Qed.
End FPX_1.
