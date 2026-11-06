(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import StoreOk CatSim.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_StepGrows () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.Riscv.Sem.eff"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_report"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.Riscv.Sem.core"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.interp_eff_accesses"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "OSSVerify.KrLib.ABoot.StoreOk.mem_grows"; "Corelib.Init.Datatypes.snd"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_value"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.decode_exec_accesses"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"].


Lemma interp_eff_accesses_grows : ltac2:(CDefT.buildp (gd_tbl_StepGrows ()) "Psegs,(0.$1.)Pt,$2.Pm,P,(3.&40.)(4.(3.&8.))Pr,(5.(6.$7.P,(3.&40.)(4.(3.&8.))))P,(8.(9.(5.(6.$7.P,(3.&40.)(4.(3.&8.)))))(:.R4.R3.R2.)(;.(5.(6.$7.P,(3.&40.)(4.(3.&8.))))R1.))(<.R3.(=.$7.P,(3.&40.)(4.(3.&8.))(>.(6.$7.P,(3.&40.)(4.(3.&8.)))R2.)))")
(* [comment removed for export] *).
Proof.
  intros segs t. induction t as [c | c | c | c | c | c | n a k IH | n a v k IH]; intros m r H; cbn [interp_eff_accesses] in H;
    try discriminate H.
  - injection H as <-. cbn. apply mem_grows_refl.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate H].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [rep| | ] eqn:E; try discriminate H.
    injection H as <-. cbn. exact (IH _ m rep E).
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate H].
    destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))) as [rep| | ] eqn:E;
      try discriminate H.
    injection H as <-. cbn.
    eapply mem_grows_trans; [apply write_to_mem_grows | exact (IH _ rep E)].
Qed.

Lemma decode_exec_accesses_grows : ltac2:(CDefT.buildp (gd_tbl_StepGrows ()) "Psegs,(0.$1.)Pst,$?.Pw,(3.&20.)Pr,(5.$?.)P,(8.(9.(5.$?.))(10.R4.R3.R2.)(;.(5.$?.)R1.))(<.(11.R4.)(11.(>.$?.R2.)))")
(* [comment removed for export] *).
Proof.
  intros segs st w r H. unfold decode_exec_accesses in H.
  destruct (is_ecall w).
  - injection H as <-. cbn. apply mem_grows_refl.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate H].
    destruct (interp_eff_accesses segs _ (ms_mem st)) as [rep| | ] eqn:E; try discriminate H.
    pose proof (interp_eff_accesses_grows segs _ _ rep E) as G.
    destruct (@access_value _ rep) as [c m'] eqn:Ev. injection H as <-. cbn. cbn in G. exact G.
Qed.

Lemma step_mem_grows : ltac2:(CDefT.buildp (gd_tbl_StepGrows ()) "Psegs,(0.$1.)Pst,$?.Pst',$?.P,(8.(9.$?.)(12.R3.R2.)(;.$?.R1.))(<.(11.R3.)(11.R2.))")
(* [comment removed for export] *).
Proof.
  intros segs st st' H. unfold RiscvSemantics.step, step_accesses, drop_access_report in H.
  destruct (fetch_word segs (ms_pc st)) as [w|].
  { destruct (decode_exec_accesses segs st w) as [rep| | ] eqn:E; try discriminate H. injection H as <-.
    exact (decode_exec_accesses_grows segs st w rep E). }
  destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|].
  { destruct (decode_exec_accesses segs st w) as [rep| | ] eqn:E; try discriminate H. injection H as <-.
    exact (decode_exec_accesses_grows segs st w rep E). }
  destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|].
  { destruct (decode_exec_accesses segs st w) as [rep| | ] eqn:E; try discriminate H. injection H as <-.
    exact (decode_exec_accesses_grows segs st w rep E). }
  destruct (fetch_failure segs (ms_mem st) (ms_pc st)) as [st1| | ] eqn:E; try discriminate H.
  exfalso. unfold fetch_failure in E. destruct (negb _); [discriminate E|]. destruct (_ : bool) in E; discriminate E.
Qed.

Theorem msteps_mem_grows : forall segs ms ms', msteps segs ms ms' -> mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros segs ms ms' H. induction H as [ms | ms ms1 ms2 Hp Hs Hm IH].
  - apply mem_grows_refl.
  - eapply mem_grows_trans; [exact (step_mem_grows segs ms ms1 Hs) | exact IH].
Qed.
