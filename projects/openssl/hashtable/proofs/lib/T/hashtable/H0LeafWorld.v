(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the world section takes the output channel's reader, the launch's mmap base and process input, and argv[1]'s place from the launch; the ledger premise is [res_vm], the launch's reserved ledger with the vDSO/vvar pair). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import H0Lim.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.hashtable.images Require Import Plain.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  Spec H0MainEntryDefs H0ReadBase H0World H0TargetPre H0PilotOOM_defs H0PilotOOM ExistsRun PhaseG.
From OSSVerify.Proofs.openssl.hashtable.lib Require H0W65x.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

Section LeafWorld.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable inp : ProcInput.
  Variable entry : word.
  Variable tid : word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Variable lim : Z.                              (* [comment removed for export] *)
  Hypothesis lim_ge : (LIM <= lim)%Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  (* LPS 727298f3: the launch's mmap base, below which the vDSO/vvar pair sits ([State.init_reserved]) *)
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hplen : (length path <= 4095)%nat.
  (* LPS 08b1429: a write to a channel with no reader raises SIGPIPE.
     [stdin0] is [amb_of inp] at every call site, so the run supplies this through
     [valid_input_channel_reader] (Run.v:4951).  A SEPARATE hypothesis, never a new conjunct. *)
  Hypothesis Hrdr : ia_channel_reader stdin0 = true.
  (* [comment removed for export] *)
  Hypothesis Hhi0 : exists s : Z, (bv_unsigned sp0 + 192 <= s < 2 ^ 47 - 32)%Z /\ (s mod 8 = 0)%Z /\ mem0 (Z_to_bv 64 s) = Some (Z_to_bv 8 0).
  (* LPS 727298f3: argv[1]'s place, from the launch ([main_str] at the caller) *)
  Hypothesis Hp1 : (0x7fff80000000 <= bv_unsigned (p1 a0s path envv rdraw inp) <= 0x800000400000)%Z.
  (* [comment removed for export] *)
  Variable mode : bool.
  Variable Q : config -> Prop.

  (* [comment removed for export] *)
  Definition vm_small (VM : VmMaps) (gm : word) : Prop :=
    res_vm VM /\ (LIM <= vm_limit VM)%Z   (* [comment removed for export] *)
    /\ (length (vm_maps VM) <= 4)%nat
    /\ In (gm, Z_to_bv 64 69632) (vm_maps VM)
    /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 69632)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM)
    /\ seps (vm_maps VM).                                   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition after_malloc (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb bw gm can sec : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->                    (* [comment removed for export] *)
      bv_unsigned bw = brkv ->                               (* [comment removed for export] *)
      read_pre sp0 (p1 a0s path envv rdraw inp) mb bw gm can sec R M ->
      world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned can) (bv_unsigned sec) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb bw gm -> vm_small VM gm ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xdd0f8) M (seg_rom RSEGS))
                               (model_pre path VM stdin0 fs0 tid)).

  (* [comment removed for export] *)
  Lemma brk_ok_sem : forall K, after_malloc K ->
    brk_ok_branch_M sp0 a0s path envv rdraw inp tid mem0 brk mbase fs0 stdin0 lim mode Q K.     (* [comment removed for export] *)
  Proof using lim_ge Hva Hve Hvsp Htid Hbrk Hmb Hfile Hpne Hplen Hrdr Hhi0 Hp1.
    intros K AM. exact (H0W65x.brk_ok_sem sp0 a0s path envv rdraw inp tid mem0 brk mbase fs0 stdin0 lim lim_ge Hva Hve Hvsp Htid Hbrk Hmb Hplen Hrdr Hp1 Hhi0 mode Q K AM).
  Qed.

  (* [comment removed for export] *)
End LeafWorld.
