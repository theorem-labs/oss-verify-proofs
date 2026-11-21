(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Js0Exit.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: section-variable wrappers around ref_exit_clean_b, ref_exit_flush_b and ref_exit_b replaced by plain #[using] theorems, with ref_exit_flush_b gaining an m_channel_reader premise threaded through ref_exit_b, as in fuzz_bigint's copy; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/BudgetWit/Src0ExitB.v, lines 32-35, 67-75, 111, 138-142, 150. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes Spec LibWritev Js0StdioDefs Js0Exit_run1 Js0Exit_run2 Js0Exit_run3 Js0StdioWrite_run1 Js0StdioWrite_run2 Js0StdioWrite.
Import ListNotations.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RdnPeelKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Js0Exit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit Require Import Js0StdioWriteB RefNodesB SpinAlgB.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac rdn_side_fast := rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia_fast.
Local Ltac rdn_solve_fast :=
lazymatch goal with
| |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
else (first [ RdnPeelKit.rdn_peel_many ltac:(idtac; rdn_side_fast) | rdn_peel1 ]; rdn_solve_fast)
| |- _ => rdn_hyp
end.
Local Ltac rdn_solve ::= rdn_solve_fast.
Section FPX_1.
Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
#[using="Type"] Theorem ref_exit_clean_b : (forall (regs : (@LinuxProcessSemantics.Riscv.Prelude.bvmap (Npos 5%positive) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (mem : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (model : (@LinuxProcessSemantics.LinuxProcessSem.State.Model)), (forall (sp : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (tp : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (code : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (tid : (@Corelib.Numbers.BinNums.Z)), (forall (wp2 : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (rp2 : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (wp1 : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (rp1 : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioDefs.exit_common regs mem sp tp code tid wp2 rp2)), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0ExitBase.file_clean mem (Zpos 745680%positive) wp1 rp1)), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 64%positive))) (@LinuxProcessSemantics.LinuxProcessSem.State.m_halted model) (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv (Npos 64%positive))))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.list (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))) (@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy model) (@Corelib.Init.Datatypes.nil (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))))), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) scfg (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.mkst fx regs ((@stdpp.bitvector.definitions.BV (Npos 64%positive) (Zpos 625360%positive) (@Corelib.Init.Logic.I)) : (@stdpp.bitvector.definitions.bv (Npos 64%positive))) mem (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.seg_rom (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments))) model) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_exit (@stdpp.bitvector.definitions.bv_and (Npos 64%positive) code (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (Zpos 255%positive))) (@LinuxProcessSemantics.LinuxProcessSem.State.m_fs model)))))))))))))))))).
Proof.
intros regs mem model sp tp code tid wp2 rp2 wp1 rp1.
intros EC F1 Hh Hlazy.
destruct EC. destruct ec_ax as [ax AX].
destruct (w1 ax regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
try assumption.
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
destruct (w2 regs1 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom RSEGS) sp code (getr regs1 9))
as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
all: try (unfold mem_w1, ax_writes; destruct ax as [|[|?]]; first [store_ok_peel; exact ec_sok | rdn_solve]).
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
destruct (w3a regs2 (mem_w2 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
(seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
1:{ unfold mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; store_ok_peel; exact ec_sok. }
1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; rdn_solve. }
1:{ repeat split; unfold mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; zaddr_goal; rdn_solve. }
1:{ repeat split; unfold mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; zaddr_goal; rdn_solve. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
eapply RefNodesB.rz_exit_at_b; [exact (ltac:(oF' 0x987e0%Z)) | exact (ltac:(oE' 0x987e0%Z)) | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.
#[using="Type"] Theorem ref_exit_flush_b :
forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
(wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
exit_common regs mem sp tp code tid wp2 rp2 ->
stdout_pending mem wb wp bufp bufsz rp1 can pending ->
m_halted model = None -> m_vm_lazy model = [] ->
fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
m_channel_reader model = true ->
SpinAlgB.rzb RSEGS scfg (mkCfg (mkst regs (0x98ad0 : word) mem (seg_rom RSEGS)) model)
(t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending.
intros EC SP Hh Hlazy Hfd Hrdr.
destruct EC. destruct ec_ax as [ax AX]. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
destruct (w1 ax regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
try assumption.
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
destruct (w2 regs1 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom RSEGS) sp code (getr regs1 9))
as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
all: try (unfold mem_w1, ax_writes; destruct ax as [|[|?]]; first [store_ok_peel; exact ec_sok | rdn_solve]).
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
destruct (w3b1 regs2 (mem_w2 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
(seg_rom RSEGS) sp code wb wp)
as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
1:{ unfold mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; store_ok_peel; exact ec_sok. }
1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; rdn_solve. }
1:{ repeat split; unfold mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; zaddr_goal; rdn_solve. }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
replace (Z_to_bv 64 0x9e188) with (0x9e188 : word) in R3ra by (apply bv_eq; reflexivity).
unfold W. rewrite <- (app_nil_r pending).
set (mem3 := mem_w3a (mem_w2 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
eapply (Js0StdioWriteB.ref_stdio_write_b scfg regs3 mem3 model (bv_unsigned sp - 32) 0xb60d0 wb wp 1
(Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x9e188 : word) pending []);
[ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
| lia | lia
|
subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; sok_stack ec_sok
| lia | lia
| split; subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; zaddr_goal; rdn_solve
| split; subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; rdn_solve
| lia | exact Hfd | exact Hrdr | exact Hh | exact Hlazy
| lia | lia | exact LEN
| cbn [length]; u_norm; reflexivity
| cbn [length]; lia
| lia | u_norm; lia | u_norm; lia
| subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; repeat rdn_peel1; exact BYTES
| reflexivity
| apply ret_ok_even; reflexivity
| apply t_emit_has_nil
| ].
intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
rewrite R3s0 in Q8.
destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax as [|[|?]]; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
eapply RefNodesB.rz_exit_at_b; [exact (ltac:(oF' 0x987e0%Z)) | exact (ltac:(oE' 0x987e0%Z)) | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.
#[using="Type"] Lemma t_emit_nil_exit : (forall (code : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (fs : (@LinuxProcessSemantics.LinuxProcessSem.Fs.Fs)), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_eq (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_exit code fs) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_emit (@Corelib.Init.Datatypes.nil (@LinuxProcessSemantics.LinuxProcessSem.State.event)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_exit code fs))))).
Proof.
intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.
#[using="Type"] Theorem ref_exit_b : (forall (regs : (@LinuxProcessSemantics.Riscv.Prelude.bvmap (Npos 5%positive) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (mem : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (model : (@LinuxProcessSemantics.LinuxProcessSem.State.Model)), (forall (code : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (pending : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioDefs.exit_pre regs mem model code pending)), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) scfg (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.mkst fx regs ((@stdpp.bitvector.definitions.BV (Npos 64%positive) (Zpos 625360%positive) (@Corelib.Init.Logic.I)) : (@stdpp.bitvector.definitions.bv (Npos 64%positive))) mem (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.seg_rom (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments))) model) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_emit (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec.W (Zpos 1%positive) pending) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_exit (@stdpp.bitvector.definitions.bv_and (Npos 64%positive) code (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (Zpos 255%positive))) (@LinuxProcessSemantics.LinuxProcessSem.State.m_fs model)))))))))).
Proof.
intros regs mem model code pending.
intros (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd & Hrdr)].
- eapply SpinAlgB.rzb_conseq; [ | apply t_emit_nil_exit ].
eapply ref_exit_clean_b; eassumption.
- eapply ref_exit_flush_b; eassumption.
Qed.
#[using="Type"] Corollary ref_exit_Z_b : (forall (regs : (@LinuxProcessSemantics.Riscv.Prelude.bvmap (Npos 5%positive) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (mem : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (model : (@LinuxProcessSemantics.LinuxProcessSem.State.Model)), (forall (code : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (pending : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioDefs.exit_pre regs mem model code pending)), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) scfg (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.mkst fx regs (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (Zpos 625360%positive)) mem (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.seg_rom (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments))) model) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_emit (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec.W (Zpos 1%positive) pending) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_exit (@stdpp.bitvector.definitions.bv_and (Npos 64%positive) code (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (Zpos 255%positive))) (@LinuxProcessSemantics.LinuxProcessSem.State.m_fs model)))))))))).
Proof.
intros. replace (Z_to_bv 64 0x98ad0) with (0x98ad0 : word) by (apply bv_eq; reflexivity).
apply ref_exit_b; assumption.
Qed.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
