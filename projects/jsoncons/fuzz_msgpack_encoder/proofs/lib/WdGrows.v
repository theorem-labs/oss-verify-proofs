(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045.Tac.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma interp_grows segs : forall t m rep, interp_eff_accesses segs t m = MachineOk rep -> mem_grows m (snd (@access_value _ rep)).
Proof.
  induction t; intros m rep Hi; cbn in Hi; try discriminate.
  - injection Hi; intros <-. cbn. apply mem_grows_refl.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [rep'| |] eqn:E; try discriminate.
    injection Hi; intros <-. cbn. eapply (H _ m rep'). exact E.
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs t _) as [rep'| |] eqn:E; try discriminate.
    injection Hi; intros <-. cbn. eapply mem_grows_trans; [apply write_to_mem_grows | eapply (IHt _ rep'); exact E].
Qed.

Lemma decode_exec_grows segs st w rep :
  decode_exec_accesses segs st w = MachineOk rep -> mem_grows (ms_mem st) (ms_mem (@access_value _ rep)).
Proof.
  intros H. unfold decode_exec_accesses in H.
  destruct (is_ecall w). { injection H; intros <-. cbn. apply mem_grows_refl. }
  destruct (decode_any w) as [[i isz]|]. 2:{ destruct (is_defined_illegal w); discriminate. }
  destruct (interp_eff_accesses _ _) as [report| |] eqn:E; try discriminate.
  pose proof (interp_grows segs _ _ _ E) as G.
  destruct report as [[c m'] acc]. cbn in G, H. injection H; intros <-. exact G.
Qed.

Lemma step_grows segs ms ms' : RiscvSemantics.step segs ms = MachineOk ms' -> mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros H. unfold RiscvSemantics.step, step_accesses, drop_access_report in H.
  destruct (fetch_word segs (ms_pc ms)) as [w|].
  { destruct (decode_exec_accesses segs ms w) as [rep| |] eqn:E; try discriminate. injection H; intros <-. eapply decode_exec_grows; eassumption. }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
  { destruct (decode_exec_accesses segs ms w) as [rep| |] eqn:E; try discriminate. injection H; intros <-. eapply decode_exec_grows; eassumption. }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
  { destruct (decode_exec_accesses segs ms w) as [rep| |] eqn:E; try discriminate. injection H; intros <-. eapply decode_exec_grows; eassumption. }
  destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) as [st'| |] eqn:E; try discriminate.
  exfalso. unfold fetch_failure in E. destruct (negb _); [discriminate|]. destruct (_ || _)%bool; discriminate.
Qed.

Lemma msteps_grows segs ms ms' : msteps segs ms ms' -> mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  induction 1; [apply mem_grows_refl|]. eapply mem_grows_trans; [| exact IHmsteps]. destruct H as [_ ST]. eapply step_grows; eassumption.
Qed.

Lemma evt_grows segs (Q : machine_state -> Prop) ms :
  evt segs Q ms -> evt segs (fun ms' => Q ms' /\ mem_grows (ms_mem ms) (ms_mem ms')) ms.
Proof. intros (ms' & RUN & HQ). exists ms'. split; [exact RUN|]. split; [exact HQ | apply (msteps_grows segs _ _ RUN)]. Qed.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode.BMode}.

Lemma wmono_grows (m m' : word -> option byte) : mem_grows m m' -> wmono segs m m'.
Proof.
  intros Hg x Hx. unfold wview in *. destruct (m x) as [b|] eqn:E.
  - pose proof (Hg x ltac:(rewrite E; discriminate)) as G. destruct (m' x); [discriminate | congruence].
  - destruct (m' x); [discriminate | exact Hx].
Qed.

Lemma stk_grows (m m' : word -> option byte) lo hi : stk segs m lo hi -> mem_grows m m' -> stk segs m' lo hi.
Proof.
  intros (H1 & H2 & H) G. split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hb)]. split; [apply (wmono_grows m m' G); exact Hw|].
  unfold mrd in *. destruct (m (wa a)) as [b0|] eqn:E.
  - pose proof (G (wa a) ltac:(rewrite E; discriminate)) as G1. destruct (m' (wa a)) as [b1|]; [exists b1; reflexivity | congruence].
  - destruct (m' (wa a)) as [b1|]; [exists b1; reflexivity | exists b; exact Hb].
Qed.

(* [comment removed for export] *)
Lemma evt_stk (Q : machine_state -> Prop) ms lo hi :
  evt segs Q ms -> stk segs (ms_mem ms) lo hi -> evt segs (fun ms' => Q ms' /\ stk segs (ms_mem ms') lo hi) ms.
Proof.
  intros E ST. apply evt_grows in E. eapply evt_mono; [exact E|]. cbv beta. intros ms' (HQ & G). split; [exact HQ|]. eapply stk_grows; eassumption.
Qed.
End WithSegs.
