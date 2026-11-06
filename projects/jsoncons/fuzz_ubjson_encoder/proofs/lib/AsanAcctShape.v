(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import CatSim.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import ShapeAlg. (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAcct SpinAlg.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_AsanAcctShape () := "C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct7node_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8pnode_okC13~~~I47Corelib4Init9Datatypes4list00K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init9Datatypes4prod00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcctBrz_step_restrictedC13~~~I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcctErz_msteps_restricted'C13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Lemma node_ok_same : AsanAcct.node_ok segs = ShapeAlg.pnode_ok segs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcctShape ()) ["FPX_1"; "WithSegs"] "h01Ih11ch23evsh32nxp;1p;2g0000p4p73110R0g001;R1p4p73110R2p8P2P0p8g002Gj12TP1j11Tg002gj20Tg003AR1f0g0046#2[f1P1[p-0]3]2^00]1p,4segs#1'0o"). Qed.

Let P_of (T : TSet) : config -> Prop := fun c => realizes segs scfg c T.

Let P_of_silent1 (T : TSet) : forall c c',
    ms_svc_pending (cfg_ms c) = None ->
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    P_of T c' -> P_of T c :=
  fun c c' Hsvc Hn Hr => rz_silent1 segs scfg c c' T (node_ok_of_pnode_instr segs scfg c _ _ _ Hsvc Hn) Hr.

Theorem rz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  realizes segs scfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs scfg (mkCfg ms model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcctShape ()) ["FPX_1"; "WithSegs"] "h01Ah11Th25modelh32msh44msr'p;2p;1p;:g004lj22Tg002Gj11Tg005Ll:0Tg006bR0/20#1g007@R0g008Gg009=p,4segsp,1Hp,2HHp,3Hwxp,4P_off0R1O1p,<P_of_silent1P1O1f4f3f2f1M:0W1W2X40W3W0o"). Qed.

Theorem rz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      realizes segs scfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs scfg (mkCfg ms model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcctShape ()) ["FPX_1"; "WithSegs"] "h01Ah11Th25modelh32msh44msr'p;2p;1p;:g004lj22Tg002Gj11Tg00:El:0Tg006bR0/20#1g007@R0g008Gg009=p,4segsp,1Hp,2HHp,3Hwxp,4P_off0R1O1p,<P_of_silent1P1O1f4f3f2f1M:0W1W2X40W3W0o"). Qed.
(* [comment removed for export] *)
Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs scfg c T.

Let SP_of_silent1 (T : TSet) : forall c c',
    ms_svc_pending (cfg_ms c) = None ->
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    SP_of T c' -> SP_of T c :=
  fun c c' Hsvc Hn Hr => srz_silent1 segs scfg c c' T (node_ok_of_pnode_instr segs scfg c _ _ _ Hsvc Hn) Hr.

Theorem srz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  srealizes segs scfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcctShape ()) ["FPX_1"; "WithSegs"] "h01Ah11Th25modelh32msh44msr'p;2p;1p;:g004lj22Tg002Gj11Tg005Ll:0Tg006bR0/20#1g007@R0g008Gg009=p,4segsp,1Hp,2HHp,3Hwxp,5SP_off0R1O1p,=SP_of_silent1P1O1f4f3f2f1M:0W1W2X40W3W0o"). Qed.

Theorem srz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      srealizes segs scfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcctShape ()) ["FPX_1"; "WithSegs"] "h01Ah11Th25modelh32msh44msr'p;2p;1p;:g004lj22Tg002Gj11Tg00:El:0Tg006bR0/20#1g007@R0g008Gg009=p,4segsp,1Hp,2HHp,3Hwxp,5SP_off0R1O1p,=SP_of_silent1P1O1f4f3f2f1M:0W1W2X40W3W0o"). Qed.
End WithSegs.

End FPX_1.
