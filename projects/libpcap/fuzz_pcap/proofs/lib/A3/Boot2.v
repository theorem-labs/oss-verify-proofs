(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanStartLoops AllocSim MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanStartLoops OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import EntryKn StdioSymDrive.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import EntryGlue.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boot2_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  (* [comment removed for export] *)
  Let E7 : env := E7 sp rdraw argv envp uid hw.
  Let MEM0 : word -> option byte := MEM0 sp rdraw argv envp uid hw.
  Let above_ok := above_ok sp rdraw argv envp uid hw.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).

  #[using="Hsp"] Lemma SL : 0x7fff80000000 <= usp. Proof. destruct Hsp as (H & _ & _). unfold sp_window_lo in H. exact H. Qed.
  #[using="Hsp"] Lemma SH : usp <= 0x800000000000. Proof. destruct Hsp as (_ & H & _). unfold sp_window_hi in H. exact H. Qed.
  #[using="sp envp Hva usp envc"] Lemma LA : 1 <= argc <= 1024. Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  #[using="sp argv Hve usp argc"] Lemma LE : 0 <= envc <= 256. Proof. unfold envc. destruct Hve as [H _]. lia. Qed.


  (* [comment removed for export] *)
  Definition E8 (a : word) : env := Env (vals_ev (vals0 PH sp rdraw argv envp uid hw ++ [a])) (blobs0 rdraw argv).

  #[using="Type"] Lemma E8_agree : forall a, env_agree 7 E7 (E8 a).
  Proof. intros a. unfold E7, Boot1.E7, E0, E8. apply (vals_app_agree (vals0 PH sp rdraw argv envp uid hw) [a]). Qed.
  #[using="Type"] Lemma ev_E8_tls : forall a, ev (E8 a) V_TLS = a.
  Proof. intros a. reflexivity. Qed.
  #[using="Type"] Lemma ev_E8_sp : forall a, ev (E8 a) V_SP = sp.
  Proof. intros a. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Hsp argc envc"] Lemma above_ok_blockE : forall E lows M log,
    ev E 0%nat = sp -> lows_ok E usp lows ->
    above_ok M -> log_below_b 0%nat lows log = true -> above_ok (mem_denot E M log).
  Proof.
    intros E lows M log Hsp0 Hl HA Hb x Hx. pose proof SL. pose proof SH.
    rewrite (mem_denot_above E M log 0%nat lows usp x Hb); try (rewrite Hsp0; unfold usp in *; lia).
    - apply HA. exact Hx.
    - unfold usp. lia.
    - exact Hl.
    - exact Hx.
  Qed.

  Ltac vmc := lazymatch goal with |- log_below_b _ _ _ = true => vm_compute; reflexivity
                               | |- sr_vars_lt _ _ = true => vm_compute; reflexivity
                               | |- kn_vars_lt _ _ = true => vm_compute; reflexivity end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Hsp usp argc envc"] Lemma phase3 : forall R M,
    regs_ok E7 SR3 R -> know_ok SEGS E7 M KN3 -> above_ok M -> mem_grows MEM0 M ->
    exists R' M', msteps SEGS (mkst R (Z_to_bv 64 A_pnloop_exit) M ROM) (mkst R' (Z_to_bv 64 A_set_tid_ecall) M' ROM)
      /\ regs_ok E7 SR3e R' /\ know_ok SEGS E7 M' KN3e /\ above_ok M' /\ mem_grows MEM0 M'.
  Proof.
    intros R M HR HK HA HG.
    ms_block_with HR HK FUEL (@nil Z) noscr 7%nat R3 HR3 HK3 MS3.
    lazymatch type of HK3 with know_ok _ _ ?m _ => set (M3 := m) in * end.
    assert (A3 : above_ok M3).
    { unfold M3. apply (above_ok_blockE E7 []); [reflexivity | constructor | exact HA | vmc]. }
    assert (G3 : mem_grows MEM0 M3) by (unfold M3; eapply mem_grows_trans; [exact HG | apply mem_denot_grows]).
    clearbody M3. exists R3, M3. repeat split; assumption.
  Qed.

  (* The TLS block is musl's builtin_tls in .bss: a fixed address inside the image, no mapping. *)
  Definition tls_ok (a : word) : Prop :=
    bv_unsigned a mod 16 = 0 /\ 4096 <= bv_unsigned a /\ bv_unsigned a + 4096 <= usp - 8388608
    /\ bv_unsigned a = A_builtin_tls.

  #[using="Hsp argc envc"] Lemma tls_ok_builtin : tls_ok (Z_to_bv 64 A_builtin_tls).
  Proof.
    pose proof SL as S. unfold tls_ok. rewrite u_small by (unfold A_builtin_tls; lia).
    unfold A_builtin_tls, usp in S |- *. split; [reflexivity|]. lia.
  Qed.

  #[using="Type"] Lemma glue_tls : forall R M (a : word),
    regs_ok E7 SR3e R -> know_ok SEGS E7 M KN3e -> regs_ok (E8 a) SR4e R /\ know_ok SEGS (E8 a) M KN4e.
  Proof.
    intros R M a HR HK. split.
    - eapply regs_ok_agree; [apply E8_agree | vmc | exact HR].
    - eapply know_ok_agree; [apply E8_agree | vmc | exact HK].
  Qed.

End Walk.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanStartLoops OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boot2_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  (* [comment removed for export] *)
  Let E7 : env := E7 sp rdraw argv envp uid hw.
  Let MEM0 : word -> option byte := MEM0 sp rdraw argv envp uid hw.
  Let above_ok := above_ok sp rdraw argv envp uid hw.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).

  #[using="Hsp"] Lemma SL : 0x7fff80000000 <= usp. Proof. destruct Hsp as (H & _ & _). unfold sp_window_lo in H. exact H. Qed.
  #[using="Hsp"] Lemma SH : usp <= 0x800000000000. Proof. destruct Hsp as (_ & H & _). unfold sp_window_hi in H. exact H. Qed.
  #[using="sp envp Hva usp envc"] Lemma LA : 1 <= argc <= 1024. Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  #[using="sp argv Hve usp argc"] Lemma LE : 0 <= envc <= 256. Proof. unfold envc. destruct Hve as [H _]. lia. Qed.


  (* [comment removed for export] *)
  Definition E8 (a : word) : env := Env (vals_ev (vals0 PH sp rdraw argv envp uid hw ++ [a])) (blobs0 rdraw argv).

  #[using="Type"] Lemma E8_agree : forall a, env_agree 7 E7 (E8 a).
  Proof. intros a. unfold E7, A3.Boot1.TwB.E7, E0, E8. apply (vals_app_agree (vals0 PH sp rdraw argv envp uid hw) [a]). Qed.
  #[using="Type"] Lemma ev_E8_tls : forall a, ev (E8 a) V_TLS = a.
  Proof. intros a. reflexivity. Qed.
  #[using="Type"] Lemma ev_E8_sp : forall a, ev (E8 a) V_SP = sp.
  Proof. intros a. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Hsp argc envc"] Lemma above_ok_blockE : forall E lows M log,
    ev E 0%nat = sp -> lows_ok E usp lows ->
    above_ok M -> log_below_b 0%nat lows log = true -> above_ok (mem_denot E M log).
  Proof.
    intros E lows M log Hsp0 Hl HA Hb x Hx. pose proof SL. pose proof SH.
    rewrite (mem_denot_above E M log 0%nat lows usp x Hb); try (rewrite Hsp0; unfold usp in *; lia).
    - apply HA. exact Hx.
    - unfold usp. lia.
    - exact Hl.
    - exact Hx.
  Qed.

  Ltac vmc := lazymatch goal with |- log_below_b _ _ _ = true => vm_compute; reflexivity
                               | |- sr_vars_lt _ _ = true => vm_compute; reflexivity
                               | |- kn_vars_lt _ _ = true => vm_compute; reflexivity end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Hsp usp argc envc"] Lemma phase3 : forall R M,
    regs_ok E7 SR3 R -> know_ok SEGS E7 M KN3 -> above_ok M -> mem_grows MEM0 M ->
    exists R' M', msteps SEGS (mkst R (Z_to_bv 64 A_pnloop_exit) M ROM) (mkst R' (Z_to_bv 64 A_set_tid_ecall) M' ROM)
      /\ regs_ok E7 SR3e R' /\ know_ok SEGS E7 M' KN3e /\ above_ok M' /\ mem_grows MEM0 M'.
  Proof.
    intros R M HR HK HA HG.
    ms_block_with HR HK FUEL (@nil Z) noscr 7%nat R3 HR3 HK3 MS3.
    lazymatch type of HK3 with know_ok _ _ ?m _ => set (M3 := m) in * end.
    assert (A3 : above_ok M3).
    { unfold M3. apply (above_ok_blockE E7 []); [reflexivity | constructor | exact HA | vmc]. }
    assert (G3 : mem_grows MEM0 M3) by (unfold M3; eapply mem_grows_trans; [exact HG | apply mem_denot_grows]).
    clearbody M3. exists R3, M3. repeat split; assumption.
  Qed.

  (* The TLS block is musl's builtin_tls in .bss: a fixed address inside the image, no mapping. *)
  Definition tls_ok (a : word) : Prop :=
    bv_unsigned a mod 16 = 0 /\ 4096 <= bv_unsigned a /\ bv_unsigned a + 4096 <= usp - 8388608
    /\ bv_unsigned a = A_builtin_tls.

  #[using="Hsp argc envc"] Lemma tls_ok_builtin : tls_ok (Z_to_bv 64 A_builtin_tls).
  Proof.
    pose proof SL as S. unfold tls_ok. rewrite u_small by (unfold A_builtin_tls; lia).
    unfold A_builtin_tls, usp in S |- *. split; [reflexivity|]. lia.
  Qed.

  #[using="Type"] Lemma glue_tls : forall R M (a : word),
    regs_ok E7 SR3e R -> know_ok SEGS E7 M KN3e -> regs_ok (E8 a) SR4e R /\ know_ok SEGS (E8 a) M KN4e.
  Proof.
    intros R M a HR HK. split.
    - eapply regs_ok_agree; [apply E8_agree | vmc | exact HR].
    - eapply know_ok_agree; [apply E8_agree | vmc | exact HK].
  Qed.

End Walk.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
