(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: Vdso is imported, the run's initial model is model0_of (with_vdso, the vDSO pair in its reserved list, vdso_free_low added), at_E3, VE48 and the phase calls take the launch's inputs, entry_launch_ok_va and CONFIG_RSEQ value, and the #[using] attributes are dropped, in both copies. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
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

(* The launch's vDSO pair ([State.init_reserved]) sits below [min mbase (sp - stack_max_size)],
   far above the ASan shadow: a range that ends at or below the shadow's top misses it. *)
Lemma vdso_free_low : forall kb (mbase sp lo n : word),
  valid_mmap_base mbase -> 0x7fff80000000 <= bv_unsigned sp ->
  bv_unsigned lo + bv_unsigned n <= 0x10007fff8000 ->
  region_free (vdso_reserved kb (page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)))) lo n = true.
Proof.
  intros kb mbase sp lo n [Hm _] Hsp Hb. apply RefNodes.region_free_intro. intros b s Hin.
  pose proof (u64_range mbase) as Rm. pose proof (u64_range sp) as Rs.
  set (x := Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)) in *.
  assert (X : mmap_base_min <= x) by (unfold x, mmap_base_min, stack_max_size in *; lia).
  assert (T : x - 4096 < page_round_down_Z x <= x) by (unfold page_round_down_Z, page_size, mmap_base_min in *; Z.div_mod_to_equations; lia).
  assert (Ht : page_round_down_Z x < two_pow_64) by (unfold two_pow_64, x in *; lia).
  destruct (vdso_reserved_above kb _ b s Ht Hin) as [H1 _].
  pose proof (vdso_len_bounds kb) as VL. left. unfold mmap_base_min, page_size in *. lia.
Qed.

(* The model of the run's start ([Run.init_config]: the initial model with the launch's vDSO
   draw), and the model at the first ASan internal mmap: the same with the tid set (no TLS
   mapping: the TLS block is builtin_tls in .bss). *)
Definition model0_of (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput) : Model :=
  with_vdso (vdso_run_init (ed_vdso draw)) (init_model (segments_reserved SEGS) brk mbase sp lim inp).
Definition M_E3 (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput) (a tid : word) : Model :=
  with_tid tid (model0_of sp brk mbase draw lim inp).

(* [comment removed for export] *)
Record at_E3 (inp : ProcInput) (mb entry sp : word) (draw : EntryDraw) (a tid c : word)
                (regs : bvmap 5 word) (mem : word -> option byte) : Prop := AtE3 {
  e3_regs  : regs_ok (E10 inp mb entry sp draw a tid c) SR_E3 regs;
  e3_know  : know_ok SEGS (E10 inp mb entry sp draw a tid c) mem KN_E3;
  e3_above : forall x : word, bv_unsigned sp <= bv_unsigned x -> mem x = wrap_mem inp mb PH entry sp draw x;
  e3_grows : mem_grows (wrap_mem inp mb PH entry sp draw) mem;
  e3_tls   : tls_ok sp a;
  e3_tid   : 0 < bv_unsigned tid < 4194304 }.

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let entry := Z_to_bv 64 (Z.of_N PC0).
  Let model0 := model0_of sp brk mbase draw lim inp.

  Lemma VE48 : valid_sp sp /\ valid_brk SEGS brk /\ valid_mmap_base mbase /\ entry_stack_fits sp (in_argv inp) (in_envp inp)
               /\ entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp.
  Proof. pose proof (valid_input_va_size _ VI) as Hsv48. pose proof VE as H. rewrite (valid_entry_sv48 _ _ _ Hsv48) in H. exact H. Qed.
  Lemma Hsp : valid_sp sp. Proof. destruct VE48 as (H & _). exact H. Qed.
  Lemma Hva : valid_argv (in_argv inp). Proof. destruct VI as (H & _). exact H. Qed.
  Lemma Hve : valid_envp (in_envp inp). Proof. destruct VI as (_ & H & _). exact H. Qed.
  Lemma Hvl : valid_launch inp. Proof. exact (valid_input_launch _ VI). Qed.
  Lemma Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp. Proof. destruct VE48 as (_ & _ & _ & _ & H). exact H. Qed.
  Lemma Huid : valid_id (in_uid inp). Proof. destruct VI as (_ & _ & _ & _ & _ & [H _] & _). exact H. Qed.   (* [comment removed for export] *)

  Lemma init_config_eq :
    init_config SEGS PC0 PH sp brk mbase draw lim inp
    = mkCfg (mkst (R0 sp) (Z_to_bv 64 A_start) (MEM0 inp mbase entry sp draw) ROM) model0.
  Proof. unfold init_config. rewrite init_mkst. reflexivity. Qed.

  Lemma model0_halted : m_halted model0 = None. Proof. reflexivity. Qed.
  Lemma model0_lazy : m_vm_lazy model0 = []. Proof. reflexivity. Qed.
  Lemma model0_tid : m_tid model0 = None. Proof. reflexivity. Qed.
  Lemma model0_fs : m_fs model0 = in_fs inp. Proof. reflexivity. Qed.
  Lemma model0_vm : m_vmmaps model0 = mkVmMapsFull (init_reserved (segments_reserved SEGS) mbase sp (in_kernel inp)) [] [] brk brk lim mbase sp.
  Proof. reflexivity. Qed.
  Lemma model0_mat : m_vm_materialized model0 = []. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition tls_clear (a : word) : bool :=
    (bv_unsigned a + 4096 <=? 0x7fff7000)%Z || (0x10007fff8000 <=? bv_unsigned a)%Z.

  (* The launch's CONFIG_RSEQ value picks the chain of BootKn1__A3.v; the two chains meet at
     [KN6e]/[SR6e] (Boot3.v [phase5]). *)
  Theorem boot_s1 : forall K, 4096 <= lim ->
    (forall a tid c R M, at_E3 inp mbase entry sp draw a tid c R M -> tls_clear a = true ->
       srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) (M_E3 sp brk mbase draw lim inp a tid)) K) ->
    srealizes SEGS (init_config SEGS PC0 PH sp brk mbase draw lim inp) K.
  Proof.
    intros K Hlim HK. rewrite init_config_eq.
    pose proof Hsp as Hsp'. pose proof Hva as Hva'. pose proof Hve as Hve'. pose proof Hvl as Hvl'. pose proof Hlau as Hlau'. pose proof Huid as Huid'.
    set (rs := kb_rseq (in_kernel inp)).
    destruct (phase1 inp mbase entry sp brk draw Hsp' Hva' Hve' Hvl' Hlau' Huid' rs eq_refl) as (R1 & M1 & MS1 & HR1 & HK1 & A1 & G1).
    destruct (phase2 inp mbase entry sp brk draw Hsp' Hva' Hve' Hvl' Hlau' rs R1 M1 HR1 HK1 A1 G1) as (R2 & M2 & MS2 & HR2 & HK2 & A2 & G2).
    destruct (phase3 inp mbase entry sp draw Hsp' Hva' Hve' rs R2 M2 HR2 HK2 A2 G2) as (R3 & M3 & MS3 & HR3 & HK3 & A3 & G3).
    eapply srz_msteps; [apply model0_halted | apply model0_lazy | eapply msteps_trans; [exact MS1 | eapply msteps_trans; [exact MS2 | exact MS3]] |].
    set (a := Z_to_bv 64 A_builtin_tls).
    assert (HT : tls_ok sp a) by exact (tls_ok_builtin sp Hsp').
    destruct (glue_tls inp mbase entry sp draw rs R3 M3 a HR3 HK3) as (HR4 & HK4).
    eapply (srz_set_tid_lazy SEGS R3 (Z_to_bv 64 A_set_tid_ecall) M3 ROM model0 K ECALLW fetch_set_tid_ecall is_ecall_ECALLW model0_halted).
    - rewrite (HR4 17%bv). destruct rs; reflexivity.
    - apply model0_tid.
    - intros tid Htid.
      replace (v_addi (Z_to_bv 64 A_set_tid_ecall) 4) with (Z_to_bv 64 A_set_tid_ret) by (apply bv_eq; reflexivity).
      assert (Ht : tid_ok tid) by (unfold tid_ok; unfold PID_MAX_ENVELOPE in Htid; cbn in Htid; lia).
      destruct (glue_settid inp mbase entry sp draw rs a tid R3 M3 Ht HR4 HK4) as [HR5 HK5].
      destruct (phase5 inp mbase entry sp draw Hsp' rs a tid _ M3 HT Ht HR5 HK5 A3 G3) as (c & R7 & M7 & MS7 & HR7 & HK7 & A7 & G7).
      destruct (phase6 inp mbase entry sp draw Hsp' a tid c R7 M7 HT HR7 HK7 A7 G7) as (R8 & M8 & MS8 & HR8 & HK8 & A8 & G8).
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
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Vdso LinuxProcessSemantics.LinuxProcessSem.Run.
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

(* The launch's vDSO pair ([State.init_reserved]) sits below [min mbase (sp - stack_max_size)],
   far above the ASan shadow: a range that ends at or below the shadow's top misses it. *)
Lemma vdso_free_low : forall kb (mbase sp lo n : word),
  valid_mmap_base mbase -> 0x7fff80000000 <= bv_unsigned sp ->
  bv_unsigned lo + bv_unsigned n <= 0x10007fff8000 ->
  region_free (vdso_reserved kb (page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)))) lo n = true.
Proof.
  intros kb mbase sp lo n [Hm _] Hsp Hb. apply RefNodes.region_free_intro. intros b s Hin.
  pose proof (u64_range mbase) as Rm. pose proof (u64_range sp) as Rs.
  set (x := Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)) in *.
  assert (X : mmap_base_min <= x) by (unfold x, mmap_base_min, stack_max_size in *; lia).
  assert (T : x - 4096 < page_round_down_Z x <= x) by (unfold page_round_down_Z, page_size, mmap_base_min in *; Z.div_mod_to_equations; lia).
  assert (Ht : page_round_down_Z x < two_pow_64) by (unfold two_pow_64, x in *; lia).
  destruct (vdso_reserved_above kb _ b s Ht Hin) as [H1 _].
  pose proof (vdso_len_bounds kb) as VL. left. unfold mmap_base_min, page_size in *. lia.
Qed.

(* The model of the run's start ([Run.init_config]: the initial model with the launch's vDSO
   draw), and the model at the first ASan internal mmap: the same with the tid set (no TLS
   mapping: the TLS block is builtin_tls in .bss). *)
Definition model0_of (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput) : Model :=
  with_vdso (vdso_run_init (ed_vdso draw)) (init_model (segments_reserved SEGS) brk mbase sp lim inp).
Definition M_E3 (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput) (a tid : word) : Model :=
  with_tid tid (model0_of sp brk mbase draw lim inp).

(* [comment removed for export] *)
Record at_E3 (inp : ProcInput) (mb entry sp : word) (draw : EntryDraw) (a tid c : word)
                (regs : bvmap 5 word) (mem : word -> option byte) : Prop := AtE3 {
  e3_regs  : regs_ok (E10 inp mb entry sp draw a tid c) SR_E3 regs;
  e3_know  : know_ok SEGS (E10 inp mb entry sp draw a tid c) mem KN_E3;
  e3_above : forall x : word, bv_unsigned sp <= bv_unsigned x -> mem x = wrap_mem inp mb PH entry sp draw x;
  e3_grows : mem_grows (wrap_mem inp mb PH entry sp draw) mem;
  e3_tls   : tls_ok sp a;
  e3_tid   : 0 < bv_unsigned tid < 4194304 }.

Section Theorems.
  Variables (sp brk mbase : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
  Hypothesis VI : valid_input inp.
  Hypothesis VE : valid_entry IMG (mkEntry sp brk mbase draw) inp.

  Let entry := Z_to_bv 64 (Z.of_N PC0).
  Let model0 := model0_of sp brk mbase draw lim inp.

  Lemma VE48 : valid_sp sp /\ valid_brk SEGS brk /\ valid_mmap_base mbase /\ entry_stack_fits sp (in_argv inp) (in_envp inp)
               /\ entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp.
  Proof. pose proof (valid_input_va_size _ VI) as Hsv48. pose proof VE as H. rewrite (valid_entry_sv48 _ _ _ Hsv48) in H. exact H. Qed.
  Lemma Hsp : valid_sp sp. Proof. destruct VE48 as (H & _). exact H. Qed.
  Lemma Hva : valid_argv (in_argv inp). Proof. destruct VI as (H & _). exact H. Qed.
  Lemma Hve : valid_envp (in_envp inp). Proof. destruct VI as (_ & H & _). exact H. Qed.
  Lemma Hvl : valid_launch inp. Proof. exact (valid_input_launch _ VI). Qed.
  Lemma Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp. Proof. destruct VE48 as (_ & _ & _ & _ & H). exact H. Qed.
  Lemma Huid : valid_id (in_uid inp). Proof. destruct VI as (_ & _ & _ & _ & _ & [H _] & _). exact H. Qed.   (* [comment removed for export] *)

  Lemma init_config_eq :
    init_config SEGS PC0 PH sp brk mbase draw lim inp
    = mkCfg (mkst (R0 sp) (Z_to_bv 64 A_start) (MEM0 inp mbase entry sp draw) ROM) model0.
  Proof. unfold init_config. rewrite init_mkst. reflexivity. Qed.

  Lemma model0_halted : m_halted model0 = None. Proof. reflexivity. Qed.
  Lemma model0_lazy : m_vm_lazy model0 = []. Proof. reflexivity. Qed.
  Lemma model0_tid : m_tid model0 = None. Proof. reflexivity. Qed.
  Lemma model0_fs : m_fs model0 = in_fs inp. Proof. reflexivity. Qed.
  Lemma model0_vm : m_vmmaps model0 = mkVmMapsFull (init_reserved (segments_reserved SEGS) mbase sp (in_kernel inp)) [] [] brk brk lim mbase sp.
  Proof. reflexivity. Qed.
  Lemma model0_mat : m_vm_materialized model0 = []. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition tls_clear (a : word) : bool :=
    (bv_unsigned a + 4096 <=? 0x7fff7000)%Z || (0x10007fff8000 <=? bv_unsigned a)%Z.

  (* The launch's CONFIG_RSEQ value picks the chain of BootKn1__A3.v; the two chains meet at
     [KN6e]/[SR6e] (Boot3.v [phase5]). *)
  Theorem boot_s1 : forall K, 4096 <= lim ->
    (forall a tid c R M, at_E3 inp mbase entry sp draw a tid c R M -> tls_clear a = true ->
       srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 A_internal_mmap_ecall) M ROM) (M_E3 sp brk mbase draw lim inp a tid)) K) ->
    srealizes SEGS (init_config SEGS PC0 PH sp brk mbase draw lim inp) K.
  Proof.
    intros K Hlim HK. rewrite init_config_eq.
    pose proof Hsp as Hsp'. pose proof Hva as Hva'. pose proof Hve as Hve'. pose proof Hvl as Hvl'. pose proof Hlau as Hlau'. pose proof Huid as Huid'.
    set (rs := kb_rseq (in_kernel inp)).
    destruct (phase1 inp mbase entry sp brk draw Hsp' Hva' Hve' Hvl' Hlau' Huid' rs eq_refl) as (R1 & M1 & MS1 & HR1 & HK1 & A1 & G1).
    destruct (phase2 inp mbase entry sp brk draw Hsp' Hva' Hve' Hvl' Hlau' rs R1 M1 HR1 HK1 A1 G1) as (R2 & M2 & MS2 & HR2 & HK2 & A2 & G2).
    destruct (phase3 inp mbase entry sp draw Hsp' Hva' Hve' rs R2 M2 HR2 HK2 A2 G2) as (R3 & M3 & MS3 & HR3 & HK3 & A3 & G3).
    eapply srz_msteps; [apply model0_halted | apply model0_lazy | eapply msteps_trans; [exact MS1 | eapply msteps_trans; [exact MS2 | exact MS3]] |].
    set (a := Z_to_bv 64 A_builtin_tls).
    assert (HT : tls_ok sp a) by exact (tls_ok_builtin sp Hsp').
    destruct (glue_tls inp mbase entry sp draw rs R3 M3 a HR3 HK3) as (HR4 & HK4).
    eapply (srz_set_tid_lazy SEGS R3 (Z_to_bv 64 A_set_tid_ecall) M3 ROM model0 K ECALLW fetch_set_tid_ecall is_ecall_ECALLW model0_halted).
    - rewrite (HR4 17%bv). destruct rs; reflexivity.
    - apply model0_tid.
    - intros tid Htid.
      replace (v_addi (Z_to_bv 64 A_set_tid_ecall) 4) with (Z_to_bv 64 A_set_tid_ret) by (apply bv_eq; reflexivity).
      assert (Ht : tid_ok tid) by (unfold tid_ok; unfold PID_MAX_ENVELOPE in Htid; cbn in Htid; lia).
      destruct (glue_settid inp mbase entry sp draw rs a tid R3 M3 Ht HR4 HK4) as [HR5 HK5].
      destruct (phase5 inp mbase entry sp draw Hsp' rs a tid _ M3 HT Ht HR5 HK5 A3 G3) as (c & R7 & M7 & MS7 & HR7 & HK7 & A7 & G7).
      destruct (phase6 inp mbase entry sp draw Hsp' a tid c R7 M7 HT HR7 HK7 A7 G7) as (R8 & M8 & MS8 & HR8 & HK8 & A8 & G8).
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
