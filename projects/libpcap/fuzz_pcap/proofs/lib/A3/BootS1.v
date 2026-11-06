(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg AsanNodesLibE. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn StdioSymDrive EntryGlue. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanNodes__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2 Boot3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots1_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* The model at the first ASan internal mmap: the initial model with the tid set (no TLS mapping: the
   TLS block is builtin_tls in .bss). *)
Definition M_E3 (sp brk mbase : word) (lim : Z) (inp : ProcInput) (a tid : word) : Model :=
  with_tid tid (init_model (segments_reserved SEGS) brk mbase sp lim inp).

(* [comment removed for export] *)
Record at_E3 (sp : word) (draw : EntryDraw) (argv envp : list (list byte)) (uid hw a tid c : word)
                (regs : bvmap 5 word) (mem : word -> option byte) : Prop := AtE3 {
  e3_regs  : regs_ok (E10 sp draw argv envp uid hw a tid c) SR_E3 regs;
  e3_know  : know_ok SEGS (E10 sp draw argv envp uid hw a tid c) mem KN_E3;
  e3_above : forall x : word, bv_unsigned sp <= bv_unsigned x -> mem x = wrap_mem PH sp argv envp uid hw draw x;
  e3_grows : mem_grows (wrap_mem PH sp argv envp uid hw draw) mem;
  e3_tls   : tls_ok sp a;
  e3_tid   : 0 < bv_unsigned tid < 4194304 }.

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let argv := in_argv inp.
  Let envp := in_envp inp.
  Let uid := in_uid inp.
  Let hw := in_hwcap inp.
  Let model0 := init_model (segments_reserved SEGS) brk mbase sp lim inp.

  #[using="draw VI VE"] Lemma VE48 : valid_sp sp /\ valid_brk SEGS brk /\ valid_mmap_base mbase /\ entry_stack_fits sp (in_argv inp) (in_envp inp).
  Proof. pose proof (valid_input_va_size _ VI) as Hsv48. pose proof VE as H. rewrite (valid_entry_sv48 _ _ _ Hsv48) in H. exact H. Qed.
  #[using="brk mbase draw inp VI VE"] Lemma Hsp : valid_sp sp. Proof. destruct VE48 as (H & _). exact H. Qed.
  #[using="VI"] Lemma Hva : valid_argv argv. Proof. destruct VI as (H & _). exact H. Qed.
  #[using="VI"] Lemma Hve : valid_envp envp. Proof. destruct VI as (_ & H & _). exact H. Qed.
  #[using="brk mbase draw VI VE"] Lemma Hfit : entry_stack_fits sp argv envp. Proof. destruct VE48 as (_ & _ & _ & H). exact H. Qed.
  #[using="VI"] Lemma Huid : valid_id uid. Proof. destruct VI as (_ & _ & _ & _ & [H _] & _). exact H. Qed.   (* [comment removed for export] *)

  #[using="Type"] Lemma init_config_eq :
    init_config SEGS PC0 PH sp brk mbase draw lim inp
    = mkCfg (mkst (R0 sp) (Z_to_bv 64 A_start) (MEM0 sp draw argv envp uid hw) ROM) model0.
  Proof. unfold init_config. rewrite init_mkst. reflexivity. Qed.

  #[using="Type"] Lemma model0_halted : m_halted model0 = None. Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_lazy : m_vm_lazy model0 = []. Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_tid : m_tid model0 = None. Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_fs : m_fs model0 = in_fs inp. Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_vm : m_vmmaps model0 = mkVmMapsFull (segments_reserved SEGS) [] [] brk brk lim mbase sp.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_mat : m_vm_materialized model0 = []. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition tls_clear (a : word) : bool :=
    (bv_unsigned a + 4096 <=? 0x7fff7000)%Z || (0x10007fff8000 <=? bv_unsigned a)%Z.

  #[using="VI VE model0"] Theorem boot_s1 : forall K, 4096 <= lim ->
    (forall a tid c R M, at_E3 sp draw argv envp uid hw a tid c R M -> tls_clear a = true ->
       srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) (M_E3 sp brk mbase lim inp a tid)) K) ->
    srealizes SEGS (init_config SEGS PC0 PH sp brk mbase draw lim inp) K.
  Proof.
    intros K Hlim HK. rewrite init_config_eq.
    pose proof Hsp as Hsp'. pose proof Hva as Hva'. pose proof Hve as Hve'. pose proof Hfit as Hfit'. pose proof Huid as Huid'.
    destruct (phase1 sp draw argv envp uid hw Hsp' Hva' Hve' Hfit' Huid') as (R1 & M1 & MS1 & HR1 & HK1 & A1 & G1).
    destruct (phase2 sp draw argv envp uid hw Hsp' Hva' Hve' Hfit' R1 M1 HR1 HK1 A1 G1) as (R2 & M2 & MS2 & HR2 & HK2 & A2 & G2).
    destruct (phase3 sp draw argv envp uid hw Hsp' R2 M2 HR2 HK2 A2 G2) as (R3 & M3 & MS3 & HR3 & HK3 & A3 & G3).
    eapply srz_msteps; [apply model0_halted | apply model0_lazy | eapply msteps_trans; [exact MS1 | eapply msteps_trans; [exact MS2 | exact MS3]] |].
    set (a := Z_to_bv 64 A_builtin_tls).
    assert (HT : tls_ok sp a) by exact (tls_ok_builtin sp argv envp Hsp').
    destruct (glue_tls sp draw argv envp uid hw R3 M3 a HR3 HK3) as (HR4 & HK4).
    eapply (srz_set_tid_lazy SEGS R3 (Z_to_bv 64 A_set_tid_ecall) M3 ROM model0 K ECALLW fetch_set_tid_ecall is_ecall_ECALLW model0_halted).
    - rewrite (HR4 17%bv). reflexivity.
    - apply model0_tid.
    - intros tid Htid.
      replace (v_addi (Z_to_bv 64 A_set_tid_ecall) 4) with (Z_to_bv 64 A_set_tid_ret) by (apply bv_eq; reflexivity).
      assert (Ht : tid_ok tid) by (unfold tid_ok; unfold PID_MAX_ENVELOPE in Htid; cbn in Htid; lia).
      destruct (glue_settid sp draw argv envp uid hw a tid R3 M3 Ht HR4 HK4) as [HR5 HK5].
      destruct (phase5 sp draw argv envp uid hw Hsp' a tid _ M3 HT Ht HR5 HK5 A3 G3) as (c & R7 & M7 & MS7 & HR7 & HK7 & A7 & G7).
      destruct (phase6 sp draw argv envp uid hw Hsp' a tid c R7 M7 HT HR7 HK7 A7 G7) as (R8 & M8 & MS8 & HR8 & HK8 & A8 & G8).
      assert (Mh2 : m_halted (with_tid tid model0) = None) by (rewrite with_tid_halted; apply model0_halted).
      assert (Ml2 : m_vm_lazy (with_tid tid model0) = []) by (rewrite with_tid_lazy; apply model0_lazy).
      eapply srz_msteps; [exact Mh2 | exact Ml2 | eapply msteps_trans; [exact MS7 | exact MS8] |].
      apply (HK a tid c R8 M8).
      + constructor; [exact HR8 | exact HK8 | exact A8 | exact G8 | exact HT | exact Ht].
      + unfold tls_clear, a. rewrite u_small by (unfold A_builtin_tls; lia). unfold A_builtin_tls. reflexivity.
  Qed.
End Theorems.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodesBoot.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot3.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boots1_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* The model at the first ASan internal mmap: the initial model with the tid set (no TLS mapping: the
   TLS block is builtin_tls in .bss). *)
Definition M_E3 (sp brk mbase : word) (lim : Z) (inp : ProcInput) (a tid : word) : Model :=
  with_tid tid (init_model (segments_reserved SEGS) brk mbase sp lim inp).

(* [comment removed for export] *)
Record at_E3 (sp : word) (draw : EntryDraw) (argv envp : list (list byte)) (uid hw a tid c : word)
                (regs : bvmap 5 word) (mem : word -> option byte) : Prop := AtE3 {
  e3_regs  : regs_ok (E10 sp draw argv envp uid hw a tid c) SR_E3 regs;
  e3_know  : know_ok SEGS (E10 sp draw argv envp uid hw a tid c) mem KN_E3;
  e3_above : forall x : word, bv_unsigned sp <= bv_unsigned x -> mem x = wrap_mem PH sp argv envp uid hw draw x;
  e3_grows : mem_grows (wrap_mem PH sp argv envp uid hw draw) mem;
  e3_tls   : tls_ok sp a;
  e3_tid   : 0 < bv_unsigned tid < 4194304 }.

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let argv := in_argv inp.
  Let envp := in_envp inp.
  Let uid := in_uid inp.
  Let hw := in_hwcap inp.
  Let model0 := init_model (segments_reserved SEGS) brk mbase sp lim inp.

  #[using="draw VI VE"] Lemma VE48 : valid_sp sp /\ valid_brk SEGS brk /\ valid_mmap_base mbase /\ entry_stack_fits sp (in_argv inp) (in_envp inp).
  Proof. pose proof (valid_input_va_size _ VI) as Hsv48. pose proof VE as H. rewrite (valid_entry_sv48 _ _ _ Hsv48) in H. exact H. Qed.
  #[using="brk mbase draw inp VI VE"] Lemma Hsp : valid_sp sp. Proof. destruct VE48 as (H & _). exact H. Qed.
  #[using="VI"] Lemma Hva : valid_argv argv. Proof. destruct VI as (H & _). exact H. Qed.
  #[using="VI"] Lemma Hve : valid_envp envp. Proof. destruct VI as (_ & H & _). exact H. Qed.
  #[using="brk mbase draw VI VE"] Lemma Hfit : entry_stack_fits sp argv envp. Proof. destruct VE48 as (_ & _ & _ & H). exact H. Qed.
  #[using="VI"] Lemma Huid : valid_id uid. Proof. destruct VI as (_ & _ & _ & _ & [H _] & _). exact H. Qed.   (* [comment removed for export] *)

  #[using="Type"] Lemma init_config_eq :
    init_config SEGS PC0 PH sp brk mbase draw lim inp
    = mkCfg (mkst (R0 sp) (Z_to_bv 64 A_start) (MEM0 sp draw argv envp uid hw) ROM) model0.
  Proof. unfold init_config. rewrite init_mkst. reflexivity. Qed.

  #[using="Type"] Lemma model0_halted : m_halted model0 = None. Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_lazy : m_vm_lazy model0 = []. Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_tid : m_tid model0 = None. Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_fs : m_fs model0 = in_fs inp. Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_vm : m_vmmaps model0 = mkVmMapsFull (segments_reserved SEGS) [] [] brk brk lim mbase sp.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma model0_mat : m_vm_materialized model0 = []. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition tls_clear (a : word) : bool :=
    (bv_unsigned a + 4096 <=? 0x7fff7000)%Z || (0x10007fff8000 <=? bv_unsigned a)%Z.

  #[using="VI VE model0"] Theorem boot_s1 : forall K, 4096 <= lim ->
    (forall a tid c R M, at_E3 sp draw argv envp uid hw a tid c R M -> tls_clear a = true ->
       srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) (M_E3 sp brk mbase lim inp a tid)) K) ->
    srealizes SEGS (init_config SEGS PC0 PH sp brk mbase draw lim inp) K.
  Proof.
    intros K Hlim HK. rewrite init_config_eq.
    pose proof Hsp as Hsp'. pose proof Hva as Hva'. pose proof Hve as Hve'. pose proof Hfit as Hfit'. pose proof Huid as Huid'.
    destruct (phase1 sp draw argv envp uid hw Hsp' Hva' Hve' Hfit' Huid') as (R1 & M1 & MS1 & HR1 & HK1 & A1 & G1).
    destruct (phase2 sp draw argv envp uid hw Hsp' Hva' Hve' Hfit' R1 M1 HR1 HK1 A1 G1) as (R2 & M2 & MS2 & HR2 & HK2 & A2 & G2).
    destruct (phase3 sp draw argv envp uid hw Hsp' R2 M2 HR2 HK2 A2 G2) as (R3 & M3 & MS3 & HR3 & HK3 & A3 & G3).
    eapply srz_msteps; [apply model0_halted | apply model0_lazy | eapply msteps_trans; [exact MS1 | eapply msteps_trans; [exact MS2 | exact MS3]] |].
    set (a := Z_to_bv 64 A_builtin_tls).
    assert (HT : tls_ok sp a) by exact (tls_ok_builtin sp argv envp Hsp').
    destruct (glue_tls sp draw argv envp uid hw R3 M3 a HR3 HK3) as (HR4 & HK4).
    eapply (srz_set_tid_lazy SEGS R3 (Z_to_bv 64 A_set_tid_ecall) M3 ROM model0 K ECALLW fetch_set_tid_ecall is_ecall_ECALLW model0_halted).
    - rewrite (HR4 17%bv). reflexivity.
    - apply model0_tid.
    - intros tid Htid.
      replace (v_addi (Z_to_bv 64 A_set_tid_ecall) 4) with (Z_to_bv 64 A_set_tid_ret) by (apply bv_eq; reflexivity).
      assert (Ht : tid_ok tid) by (unfold tid_ok; unfold PID_MAX_ENVELOPE in Htid; cbn in Htid; lia).
      destruct (glue_settid sp draw argv envp uid hw a tid R3 M3 Ht HR4 HK4) as [HR5 HK5].
      destruct (phase5 sp draw argv envp uid hw Hsp' a tid _ M3 HT Ht HR5 HK5 A3 G3) as (c & R7 & M7 & MS7 & HR7 & HK7 & A7 & G7).
      destruct (phase6 sp draw argv envp uid hw Hsp' a tid c R7 M7 HT HR7 HK7 A7 G7) as (R8 & M8 & MS8 & HR8 & HK8 & A8 & G8).
      assert (Mh2 : m_halted (with_tid tid model0) = None) by (rewrite with_tid_halted; apply model0_halted).
      assert (Ml2 : m_vm_lazy (with_tid tid model0) = []) by (rewrite with_tid_lazy; apply model0_lazy).
      eapply srz_msteps; [exact Mh2 | exact Ml2 | eapply msteps_trans; [exact MS7 | exact MS8] |].
      apply (HK a tid c R8 M8).
      + constructor; [exact HR8 | exact HK8 | exact A8 | exact G8 | exact HT | exact Ht].
      + unfold tls_clear, a. rewrite u_small by (unfold A_builtin_tls; lia). unfold A_builtin_tls. reflexivity.
  Qed.
End Theorems.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
