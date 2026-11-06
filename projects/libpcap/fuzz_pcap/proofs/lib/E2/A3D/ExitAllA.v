(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF StrwF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AProto MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import MonadG.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require F_module_dtorA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_module_dtorA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition EXIT_KEEP_IMG : list (Z * Z) :=
  [(0xa4f30, 0xa4f40); (0xa5480, 0xa5490); (0xa6190, 0xa61a0); (0xa71d0, 0xa71d8); (0xaaf90, 0xaaf91); (0x1404a0, 0x1404a1);
   (0x5e0c50, 0x5e0c58); (0x601608, 0x601609); (0x60160c, 0x601614); (0x601618, 0x601638); (0x601728, 0x601738); (0x601828, 0x60182c); (0x601848, 0x601850)].
(* [comment removed for export] *)
Definition EXIT_KEEP : list (Z * Z) := EXIT_KEEP_IMG ++ MDTOR_KEEP.

(* [comment removed for export] *)
Lemma exit_keep_ci_ok :
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= 0x1804c8 \/ 0x5d0510 <= fst iv) /\ snd iv <= 0x603000
                    /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv) /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                    /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv) /\ (snd iv <= 0xaaf98 \/ 0xaaf98 + 728 <= fst iv)) EXIT_KEEP.
Proof. unfold EXIT_KEEP, EXIT_KEEP_IMG, MDTOR_KEEP. cbn [app]. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

(* [comment removed for export] *)
Definition EXIT_KEEP_TLS : list (Z * Z) := [(ATPv + -168, ATPv + -164)].

#[using="Type"] Lemma exit_cells_frame : forall t reg (m m' : mem) W,
  exit_cells t reg m -> munch W m m' -> wmono asegs m m' -> Forall (iv_clear (EXIT_KEEP_TLS ++ EXIT_KEEP_IMG)) W -> exit_cells t reg m'.
Proof.
  intros t reg m m' W EC MU WM HW.
  assert (K : forall k A n, In k (EXIT_KEEP_TLS ++ EXIT_KEEP_IMG) -> fst k <= A -> A + n <= snd k -> disjoint_from W A n)
    by (intros k A n Hk H1 H2; eapply keep_disjoint; eassumption).
  destruct EC as (TID & EXL & ATXC & COV & GF & FA & FINZ & GCX & (dso & DSO) & Ht).
  destruct ATXC as (IFL & CBC & FIN & ALK & SLOT & HEAD & NEXT & F0 & F1 & A0 & A1 & (cdt & thr & sec & tm1 & LIBC)).
  unfold exit_cells, atx_cells.
  Ltac tr K k := eapply rw_cells_transport; [eassumption | eassumption | eassumption | apply (K k); [unfold EXIT_KEEP_TLS, EXIT_KEEP_IMG; keep_in| cbn; lia| cbn; lia]].
  split; [tr K (ATPv + -168, ATPv + -164)|]. split; [tr K (0x601828, 0x60182c)|].
  split. { split; [tr K (0x5e0c50, 0x5e0c58)|]. split; [tr K (0x5e0c50, 0x5e0c58)|].
           split; [tr K (0x601608, 0x601609)|]. split; [tr K (0x60160c, 0x601614)|]. split; [tr K (0x60160c, 0x601614)|].
           split; [tr K (0x601618, 0x601638)|]. split; [tr K (0x601618, 0x601638)|]. split; [tr K (0x601618, 0x601638)|]. split; [tr K (0x601618, 0x601638)|].
           split; [tr K (0x601728, 0x601738)|]. split; [tr K (0x601728, 0x601738)|]. exists cdt, thr, sec, tm1; tr K (0x601848, 0x601850). }
  split; [tr K (0x1404a0, 0x1404a1)|]. split; [tr K (0xa6190, 0xa61a0)|].
  split; [tr K (0xa4f30, 0xa4f40)|]. split; [tr K (0xaaf90, 0xaaf91)|]. split; [tr K (0xa5480, 0xa5490)|].
  split; [exists dso; tr K (0xa71d0, 0xa71d8)| exact Ht].
Qed.

(* [comment removed for export] *)
Definition exit_statics (m : mem) : Prop := (exists t reg, exit_cells t reg m) /\ mdtor_pre m.
Definition EXIT_KEEP_ALL : list (Z * Z) := EXIT_KEEP_TLS ++ EXIT_KEEP.

#[using="Type"] Lemma exit_statics_frame : forall (m m' : mem) W,
  exit_statics m -> munch W m m' -> wmono asegs m m' -> Forall (iv_clear EXIT_KEEP_ALL) W -> exit_statics m'.
Proof.
  intros m m' W [[t [reg EC]] MP] MU WM HW. unfold EXIT_KEEP_ALL, EXIT_KEEP in HW. split.
  - exists t, reg. eapply exit_cells_frame; [exact EC| exact MU| exact WM|].
    eapply Forall_impl; [| exact HW]. intros iv H. apply iv_clear_app in H as [H1 H2]. apply iv_clear_app in H2 as [H2 _].
    apply iv_clear_app. split; assumption.
  - eapply mdtor_pre_frame; [exact MP| exact MU| exact WM|].
    eapply Forall_impl; [| exact HW]. intros iv H. apply iv_clear_app in H as [_ H2]. apply iv_clear_app in H2 as [_ H2]. exact H2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma mdtor_w_low : Forall (fun iv => snd iv <= ATOP) MDTOR_W.
Proof. atop_facts. unfold MDTOR_W, SHW_LO, SHW_LEN. repeat (apply Forall_cons; [cbn [snd]; lia|]). apply Forall_nil. Qed.

#[using="Type"] Lemma mdtor_pre_exit_frame : forall sp (m m' : mem),
  mdtor_pre m -> ATOP + 4096 <= sp - 48 - MDTOR_DEPTH -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> mdtor_pre m'.
Proof.
  intros sp m m' P KH MU WM. eapply mdtor_pre_frame; [exact P| exact MU| exact WM|].
  atop_facts. unfold AEXIT_W1, MDTOR_DEPTH, MDTOR_KEEP, iv_clear in *.
  repeat (apply Forall_cons; [repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil|]). apply Forall_nil.
Qed.

Section Closed.
  Context {St : Type} (stdio_exit_model : Monad.M St unit).
  Variable SX : St -> footprint -> mem -> Prop.
  Variable stdio_exit_frame : Z.
  Hypothesis stdio_exit_frame_nonneg : 0 <= stdio_exit_frame.
  Hypothesis SX_frame : forall s RNG sp m m', SX s RNG m -> (ATOP + 4096 <= sp - 48 - MDTOR_DEPTH)%Z ->
    munch (AEXIT_W1 sp ++ MDTOR_W) m m' -> wmono asegs m m' -> SX s RNG m'.
  Hypothesis stdio_exit_spec : stdio_exit_stmtA stdio_exit_model SX stdio_exit_frame.

  Definition at_exit_closedA := at_exitA mdtor_pre SX stdio_exit_frame.
  Definition exit_closedA : forall (code : Z) (s : St) (RNG : footprint) (Q : Empty_set -> St -> footprint -> machine_state -> Prop) ms,
      at_exit_closedA code s RNG ms -> implMG RNG (exit_model stdio_exit_model code) s Q ms :=
    exit_specA stdio_exit_model mdtor_pre MDTOR_W module_dtor_proof mdtor_w_low mdtor_pre_exit_frame SX stdio_exit_frame
               stdio_exit_frame_nonneg SX_frame stdio_exit_spec.
End Closed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StrwF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_module_dtorA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition EXIT_KEEP_IMG : list (Z * Z) :=
  [(0xa5310, 0xa5320); (0xa5860, 0xa5870); (0xa6570, 0xa6580); (0xa75b0, 0xa75b8); (0xab390, 0xab391); (0x1408a0, 0x1408a1);
   (0x5e1050, 0x5e1058); (0x601a08, 0x601a09); (0x601a0c, 0x601a14); (0x601a18, 0x601a38); (0x601b28, 0x601b38); (0x601c28, 0x601c2c); (0x601c48, 0x601c50)].
(* [comment removed for export] *)
Definition EXIT_KEEP : list (Z * Z) := EXIT_KEEP_IMG ++ MDTOR_KEEP.

(* [comment removed for export] *)
Lemma exit_keep_ci_ok :
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= 0x1808c8 \/ 0x5d0910 <= fst iv) /\ snd iv <= 0x604000
                    /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv) /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                    /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv) /\ (snd iv <= 0xab398 \/ 0xab398 + 728 <= fst iv)) EXIT_KEEP.
Proof. unfold EXIT_KEEP, EXIT_KEEP_IMG, MDTOR_KEEP. cbn [app]. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

(* [comment removed for export] *)
Definition EXIT_KEEP_TLS : list (Z * Z) := [(ATPv + -168, ATPv + -164)].

#[using="Type"] Lemma exit_cells_frame : forall t reg (m m' : mem) W,
  exit_cells t reg m -> munch W m m' -> wmono asegs m m' -> Forall (iv_clear (EXIT_KEEP_TLS ++ EXIT_KEEP_IMG)) W -> exit_cells t reg m'.
Proof.
  intros t reg m m' W EC MU WM HW.
  assert (K : forall k A n, In k (EXIT_KEEP_TLS ++ EXIT_KEEP_IMG) -> fst k <= A -> A + n <= snd k -> disjoint_from W A n)
    by (intros k A n Hk H1 H2; eapply keep_disjoint; eassumption).
  destruct EC as (TID & EXL & ATXC & COV & GF & FA & FINZ & GCX & (dso & DSO) & Ht).
  destruct ATXC as (IFL & CBC & FIN & ALK & SLOT & HEAD & NEXT & F0 & F1 & A0 & A1 & (cdt & thr & sec & tm1 & LIBC)).
  unfold exit_cells, atx_cells.
  Ltac tr K k := eapply rw_cells_transport; [eassumption | eassumption | eassumption | apply (K k); [unfold EXIT_KEEP_TLS, EXIT_KEEP_IMG; keep_in| cbn; lia| cbn; lia]].
  split; [tr K (ATPv + -168, ATPv + -164)|]. split; [tr K (0x601c28, 0x601c2c)|].
  split. { split; [tr K (0x5e1050, 0x5e1058)|]. split; [tr K (0x5e1050, 0x5e1058)|].
           split; [tr K (0x601a08, 0x601a09)|]. split; [tr K (0x601a0c, 0x601a14)|]. split; [tr K (0x601a0c, 0x601a14)|].
           split; [tr K (0x601a18, 0x601a38)|]. split; [tr K (0x601a18, 0x601a38)|]. split; [tr K (0x601a18, 0x601a38)|]. split; [tr K (0x601a18, 0x601a38)|].
           split; [tr K (0x601b28, 0x601b38)|]. split; [tr K (0x601b28, 0x601b38)|]. exists cdt, thr, sec, tm1; tr K (0x601c48, 0x601c50). }
  split; [tr K (0x1408a0, 0x1408a1)|]. split; [tr K (0xa6570, 0xa6580)|].
  split; [tr K (0xa5310, 0xa5320)|]. split; [tr K (0xab390, 0xab391)|]. split; [tr K (0xa5860, 0xa5870)|].
  split; [exists dso; tr K (0xa75b0, 0xa75b8)| exact Ht].
Qed.

(* [comment removed for export] *)
Definition exit_statics (m : mem) : Prop := (exists t reg, exit_cells t reg m) /\ mdtor_pre m.
Definition EXIT_KEEP_ALL : list (Z * Z) := EXIT_KEEP_TLS ++ EXIT_KEEP.

#[using="Type"] Lemma exit_statics_frame : forall (m m' : mem) W,
  exit_statics m -> munch W m m' -> wmono asegs m m' -> Forall (iv_clear EXIT_KEEP_ALL) W -> exit_statics m'.
Proof.
  intros m m' W [[t [reg EC]] MP] MU WM HW. unfold EXIT_KEEP_ALL, EXIT_KEEP in HW. split.
  - exists t, reg. eapply exit_cells_frame; [exact EC| exact MU| exact WM|].
    eapply Forall_impl; [| exact HW]. intros iv H. apply iv_clear_app in H as [H1 H2]. apply iv_clear_app in H2 as [H2 _].
    apply iv_clear_app. split; assumption.
  - eapply mdtor_pre_frame; [exact MP| exact MU| exact WM|].
    eapply Forall_impl; [| exact HW]. intros iv H. apply iv_clear_app in H as [_ H2]. apply iv_clear_app in H2 as [_ H2]. exact H2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma mdtor_w_low : Forall (fun iv => snd iv <= ATOP) MDTOR_W.
Proof. atop_facts. unfold MDTOR_W, SHW_LO, SHW_LEN. repeat (apply Forall_cons; [cbn [snd]; lia|]). apply Forall_nil. Qed.

#[using="Type"] Lemma mdtor_pre_exit_frame : forall sp (m m' : mem),
  mdtor_pre m -> ATOP + 4096 <= sp - 48 - MDTOR_DEPTH -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> mdtor_pre m'.
Proof.
  intros sp m m' P KH MU WM. eapply mdtor_pre_frame; [exact P| exact MU| exact WM|].
  atop_facts. unfold AEXIT_W1, MDTOR_DEPTH, MDTOR_KEEP, iv_clear in *.
  repeat (apply Forall_cons; [repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil|]). apply Forall_nil.
Qed.

Section Closed.
  Context {St : Type} (stdio_exit_model : Monad.M St unit).
  Variable SX : St -> footprint -> mem -> Prop.
  Variable stdio_exit_frame : Z.
  Hypothesis stdio_exit_frame_nonneg : 0 <= stdio_exit_frame.
  Hypothesis SX_frame : forall s RNG sp m m', SX s RNG m -> (ATOP + 4096 <= sp - 48 - MDTOR_DEPTH)%Z ->
    munch (AEXIT_W1 sp ++ MDTOR_W) m m' -> wmono asegs m m' -> SX s RNG m'.
  Hypothesis stdio_exit_spec : stdio_exit_stmtA stdio_exit_model SX stdio_exit_frame.

  Definition at_exit_closedA := at_exitA mdtor_pre SX stdio_exit_frame.
  Definition exit_closedA : forall (code : Z) (s : St) (RNG : footprint) (Q : Empty_set -> St -> footprint -> machine_state -> Prop) ms,
      at_exit_closedA code s RNG ms -> implMG RNG (exit_model stdio_exit_model code) s Q ms :=
    exit_specA stdio_exit_model mdtor_pre MDTOR_W module_dtor_proof mdtor_w_low mdtor_pre_exit_frame SX stdio_exit_frame
               stdio_exit_frame_nonneg SX_frame stdio_exit_spec.
End Closed.
End CANSEC1.
End TwB.
