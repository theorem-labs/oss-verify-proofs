(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Amb PropExec CatExec CatSim SeqExec StepTac StoreOk ShapeAlg Hoare WalkTac SumWalkTac Frame MemSplit Nodes MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec RefNodes RefMemcpyLib RefLayout UbStartup UbMainEntry MallocDefs UbEnframeBase UbReadDefs UbReadBase UbWorld UbTargetPre UbReadStage UbReadChunkW Ub_code_1299c_12db8 Ub_code_1735c_17f20 Ub_code_1e6dc_1f0b8 UbPilotOOM SymAbove.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymXfer.
Unset Nia Cache.  (* [comment removed for export] *)

Module UbW65_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMainEntry OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPilotOOM.UbPilotOOM_defs.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymXfer.
Unset Lia Cache.
Import ListNotations. Import SX2. Import SX2S.

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Definition STOPS_W : list Z := 0x180e4%Z :: STOPS.
Definition runW (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_W scr ss [].

Definition bx : expr := EVar 70.

(* [comment removed for export] *)
Definition knW0 : list kentry := Eval vm_compute in
  (KZero (SA bx 0) (ELit 4096) :: KZero (SA bx 4096) (ELit 4096)
   :: KWr (SA bx 0) 4096 :: KWr (SA bx 4096) 4096
   :: kn_xfer knD2 bx 0 8192 true).
Definition srW0 : list expr := Eval vm_compute in sr_upd srD2 (ridx 10) (EAlu ALU_ADD bx (ELit 8192)).
Definition rW1 := Eval vm_compute in run scr0 (SS 0x180c4 srW0 [] knW0 71).
Definition srW1 : list expr := Eval vm_compute in s_regs (fst (fst rW1)).
Definition knW1 : list kentry := Eval vm_compute in kn_after rW1 knW0.

(* [comment removed for export] *)
Definition knU : list kentry := Eval vm_compute in kn_xfer knW1 bx 0 4096 false.
Definition srO0 := Eval vm_compute in sr_upd srW1 (ridx 10) bx.
Definition rO := Eval vm_compute in runW scr0 (SS 0x191d8 srO0 [] knU 71).
Definition srO1 : list expr := Eval vm_compute in s_regs (fst (fst rO)).
Definition knO1 : list kentry := Eval vm_compute in kn_after rO knU.

(* [comment removed for export] *)
Definition srM : list expr := Eval vm_compute in sr_upd srO1 (ridx 10) (EVar 71).
Definition knM : list kentry := knO1.

(* [comment removed for export] *)
Definition rW2 := Eval vm_compute in run scr0 (SS 0x180e4 srM [] knM 72).
Definition srW2 : list expr := Eval vm_compute in s_regs (fst (fst rW2)).
Definition knW2 : list kentry := Eval vm_compute in kn_after rW2 knM.


(* [comment removed for export] *)
Definition gx : expr := EVar 72.
(* [comment removed for export] *)
Definition knG00 : list kentry :=
  KAlign gx 4096 :: KRange gx 0x52000 (0x7fffff800000 - 69632)
  :: KDisj (SA (EVar 0) (-8388608)) 0x800000000000 (SA gx 0) 69632
  :: KDisj (SA bx 0) 8192 (SA gx 0) 69632 :: knW2.
Definition knG0 : list kentry := Eval vm_compute in
  (KZero (SA gx 0) (ELit 69632) :: KWr (SA gx 0) 69632 :: kn_xfer knG00 gx 0 69632 true).
Definition srG0 : list expr := Eval vm_compute in sr_upd srW2 (ridx 10) gx.
Definition scrG : scripts := SCR [true] [] [].   (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG (SS 0x191d8 srG0 [] knG0 73).
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.


(* [comment removed for export] *)
Definition LOGE : list sentry :=
  [SE (SA gx 29) 1 (ELit 160); SE (SA gx 69624) 4 (ELit 4060); SE (SA gx 69623) 1 (ELit 0);
   SE (SA gx 65568) 1 (ELit 0); SE (SA gx 30) 2 (ELit 1); SE (SA gx 29) 1 (ELit 0);
   SE (SA gx 28) 1 (ELit 0); SE (SA gx 14) 2 (ELit 1); SE (SA gx 13) 1 (ELit 224)].
(* [comment removed for export] *)
Definition knZ : list kentry := Eval vm_compute in fst (fst (carry LOGE knG [])).
Definition srZ : list expr := Eval vm_compute in
  sr_upd (sr_after_call_j srG (map ridx callee_saved) 73) (ridx 10) (EAlu ALU_ADD gx (ELit 32)).

(* [comment removed for export] *)
Lemma itinerary_w65 :
  (s_pc (fst (fst rW1)), snd (fst rW1)) = (0x191d4%Z, [])
  /\ (s_pc (fst (fst rO)), snd (fst rO)) = (0x180e4%Z, [])
  /\ (s_pc (fst (fst rW2)), snd (fst rW2)) = (0x191d4%Z, [])
  /\ (s_pc (fst (fst rG)), snd (fst rG)) = (0x18e44%Z, [SCBr true BC_NE (EAlu ALU_XOR gx (ELit (-1))) (ELit 0)]).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma carry_LOGE_ok : snd (fst (carry LOGE knG [])) = [].
Proof. vm_compute. reflexivity. Qed.
End WithFP1.

End UbW65_defs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SimInv ExitSim ShapeLaws SpecConsts LibKnowFrame LibWritev UbEnframe.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbAboveBand.
From Stdlib Require Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PerfWalkBz.

Module UbW65.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SimInv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ExitSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeLaws OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SpecConsts OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWritev OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStartup OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMainEntry OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadBase.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPilotOOM.UbPilotOOM_defs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPilotOOM.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymAbove OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbAboveBand UbW65_defs.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.
Tactic Notation "run_blockW" constr(scr) constr(NX) := run_block_gen FUEL STOPS_W scr NX false.
Tactic Notation "run_blockW_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_W scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Lemma bt_ne_not : forall (x : word), (bv_unsigned x < 2 ^ 64 - 1)%Z ->
  branch_taken BC_NE (alu64 ALU_XOR x (Z_to_bv 64 (-1))) (Z_to_bv 64 0) = true.
Proof.
  intros x Hx. cbn [branch_taken]. apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq.
  change (alu64 ALU_XOR x (Z_to_bv 64 (-1))) with (bv_xor x (Z_to_bv 64 (-1))).
  pose proof (u64_range x).
  rewrite bv_xor_unsigned. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  change ((-1) mod 2 ^ 64)%Z with (2 ^ 64 - 1)%Z. change (0 mod 2 ^ 64)%Z with 0%Z.
  intros E. apply Z.lxor_eq in E. lia.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_set_have : forall E sr R (rd : reg) v e,
  regs_ok E sr R -> getr R rd = v -> edenot E e = v -> rd <> 0%bv ->
  regs_ok E (sr_upd sr (ridx rd) e) R.
Proof.
  intros E sr R rd v e HR Hv He Hrd r.
  pose proof (regs_ok_set E sr R rd v e HR Hrd He r) as H.
  rewrite <- H. destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hrd. exact Hv.
  - rewrite getr_other by exact Hne. reflexivity.
Qed.

Lemma callee_saved_no0 : ~ In (0%bv : reg) callee_saved.
Proof.
  unfold callee_saved. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.

Definition is_kzero_cov (b : expr) (k n : Z) (K : kentry) : bool :=
  match K with
  | KZero (SA b' k') (ELit n') => expr_eqb b b' && Z.leb k' k && Z.leb (k + n) (k' + n')
  | _ => false
  end.
End WithFP1.


Section WithFP2. Context {FP : PropExec.FPState}.
Section World.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rndb : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid rndb regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : path <> dot_path.
  Hypothesis Hplen : (length path <= 4095)%nat.
  (* [comment removed for export] *)
  Variable fd3 : FdEntry.
  (* [comment removed for export] *)
  Variable SI : (word -> option byte) -> Prop.
  Hypothesis SI_step : forall M M' : word -> option byte,
    (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M' a = M a) -> SI M -> SI M'.

  #[local] Notation ENVv := (ENV a0s path).
  (* [comment removed for export] *)
  #[local] Notation RES := (segments_reserved RSEGS).

  (* [comment removed for export] *)
  Ltac si_block HSI Rn Mn :=
    lazymatch goal with
    | EQM : ?M' = mem_denot ?E ?Mo ?log, HK : know_ok ?segs ?E ?M' ?kn, HR : regs_ok ?E _ ?R' |- _ =>
        let H := fresh "HSI" in
        assert (H : SI M');
        [ apply (SI_step Mo M'); [| exact HSI]; intros xa Hxa; rewrite EQM;
          apply (mem_denot_above_band segs E M' Mo kn log 0%nat 0x52000 0x7fff7f800000 xa HK);
          [ vm_compute; reflexivity | lia | cbn [ev ENV]; pins; lia | cbn [ev ENV]; pins; lia | lia | lia ]
        | clear HSI EQM; try clear Mn; rename H into HSI; try rename M' into Mn; try clear Rn; try rename R' into Rn ]
    end.

  (* [comment removed for export] *)
  Ltac si_fill HSI :=
    lazymatch goal with
    | |- SI (zfill ?a ?n ?M) => apply (SI_step M); [| exact HSI]; intros xa Hxa; apply zfill_out; rewrite ?u64_lit by lia; lia
    | |- SI (unfill ?a ?n ?M) => apply (SI_step M); [| exact HSI]; intros xa Hxa; apply unfill_outside; rewrite ?u64_lit by lia; lia
    end.

  (* [comment removed for export] *)
  Definition fdsV : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  Definition modelV (VM : VmMaps) : Model := mkModelC fdsV VM stdin0 fs0 None (Some tid) None.

  Lemma fdsV_2 : fd_lookup fdsV (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma mV_vmmaps : forall VM, m_vmmaps (modelV VM) = VM.  Proof. reflexivity. Qed.
  Lemma mV_fs : forall VM, m_fs (modelV VM) = fs0.  Proof. reflexivity. Qed.
  Lemma mV_fds : forall VM, m_fds (modelV VM) = fdsV.  Proof. reflexivity. Qed.
  Lemma mV_fd2 : forall VM, fd_lookup (m_fds (modelV VM)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition model1V : Model := mkModelC fdsV (mkVmMapsFull RES [] [] brk brk LIM mbase sp0) stdin0 fs0 None (Some tid) None.

  Definition brk_ok_entry (KB : TSet) : Prop :=
    forall vals R M,
      length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid ->
      regs_ok (ENVv vals) srD2 R -> know_ok RSEGS (ENVv vals) M knD2 -> SI M ->
      realizes RSEGS
        (mkCfg (mkst (regupd R 10 (Z_to_bv 64 (bv_unsigned brk + 8192))) (Z_to_bv 64 0x180c4)
                     (zfill brk (Z_to_bv 64 8192) M) (seg_rom RSEGS))
               (mkModelC fdsV (mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk
                                            (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0)
                        stdin0 fs0 None (Some tid) None)) KB.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variable K : TSet.

  (* [comment removed for export] *)
(* [comment removed for export] *)
  Definition w65_vm (VM : VmMaps) (mb gm : word) : Prop :=
    vm_reserved VM = RES /\ vm_limit VM = LIM /\ vm_init_sp VM = sp0 /\
    vm_maps VM = [(gm, Z_to_bv 64 69632); (mb, Z_to_bv 64 8192)]
    /\ (bv_unsigned gm + 69632 <= bv_unsigned mb \/ bv_unsigned mb + 8192 <= bv_unsigned gm)%Z.

  Definition exitG_branch : Prop :=
    forall vals R M VM,
      length vals = 105%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
      regs_ok (ENVv vals) srZ R -> know_ok RSEGS (ENVv vals) M knZ ->
      vm_pre VM sp0 brk (vals_ev vals 72) -> w65_vm VM brk (vals_ev vals 72) -> SI M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b3c) M (seg_rom RSEGS)) (modelV VM)) K.

  Lemma w65_G : forall vals R M VM,
    exitG_branch ->
    length vals = 73%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
    regs_ok (ENVv vals) srG0 R -> know_ok RSEGS (ENVv vals) M knG0 ->
    vm_pre VM sp0 brk (vals_ev vals 72) -> w65_vm VM brk (vals_ev vals 72) -> SI M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x191d8) M (seg_rom RSEGS)) (modelV VM)) K.
  Proof.
    intros vals R M VM EXIT HL P0 P2 P70 P5 HR HK HVM HVS HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ knG0 ltac:(let i := kidx knG0 (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV] in Kgm.
    pose proof (know_nth RSEGS _ _ knG0 ltac:(let i := kidx knG0 (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV] in Kga.
    pose proof (know_nth RSEGS _ _ knG0 ltac:(let i := kidx knG0 (is_kdisj bx gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ev ENV] in Kgd; rewrite P70 in Kgd.
    set (gm := vals_ev vals 72) in *.
    (* [comment removed for export] *)
    run_block_keep scrG 73%nat.
    { unfold sc_denot. cbn [edenot ev ENV]. apply bt_ne_not. subst gm. lia. }
    si_block HSI R M.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?MG ?kn =>
      krdv HK 70%nat 4136%Z 8%nat Hmem; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P70; lia|];
      krdv HK 70%nat 4152%Z 8%nat Hmw; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P70; lia|];
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kzero_cov gx 9 8) in exact i) _ HK eq_refl) as Kz;
      cbn [kentry_ok] in Kz; unfold elenZ, estart in Kz; cbn [a_base a_off edenot ev ENV] in Kz;
      pose proof (kwr_store_ok RSEGS E _ kn ltac:(let i := kidx kn (is_kwr_cov gx 13 69615) in exact i)
                    _ _ _ 13 (Z.to_nat 69615) HK eq_refl ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as Hok;
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kimg_cov 66752 96) in exact i) _ HK eq_refl) as Kimg;
      cbn [kentry_ok] in Kimg
    end.
    fold gm in Kz, Hmem, Hmw, Hok.
    unfold adenot, v_addi in Hmem, Hmw, Hok. cbn [a_base a_off edenot ev ENV] in Hmem, Hmw, Hok.
    rewrite P70 in Hmem, Hmw. fold gm in Hok.
    change (bv_unsigned (Z_to_bv 64 69623)) with 69623%Z in Kz.
    assert (EF : efH M (Z_to_bv 64 1) (bv_unsigned brk + 4120) (bv_unsigned gm) 72480 0 65536 0 0 69616
                     (bv_unsigned gm + 16) 1).
    { constructor.
      - vm_compute. reflexivity.
      - unfold slot_start, UNIT. lia.
      - vm_compute. reflexivity.
      - pose proof (u64_range brk). lia.
      - pose proof (u64_range gm). lia.
      - lia.
      - lia.
      - lia.
      - intros _. vm_compute. reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - replace (bv_unsigned brk + 4120 + 16)%Z with (bv_unsigned brk + 4136)%Z by lia.
        rewrite Hmem. subst gm. rewrite Z_to_bv_bv_unsigned. reflexivity.
      - replace (bv_unsigned brk + 4120 + 32)%Z with (bv_unsigned brk + 4152)%Z by lia. exact Hmw.
      - replace (bv_unsigned gm + 16 - 4)%Z with (bv_unsigned gm + 9 + 3)%Z by lia. apply (proj2 Kz). lia.
      - replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 9 + 4)%Z by lia. apply (proj2 Kz). lia.
      - intros C. exfalso. apply C. reflexivity.
      - replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 13)%Z by lia.
        replace (Z.to_nat (69616 - 1)) with (Z.to_nat 69615) by reflexivity. exact Hok.
      - intros j Hj. unfold SCT. apply (proj2 (proj2 Kimg)). lia. }
    assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b3c)) by (apply bv_eq; vm_compute; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0x12b3c) by (regv HR (1:reg); reflexivity).
    assert (G10 : getr R 10 = Z_to_bv 64 (bv_unsigned brk + 4120)).
    { regv HR (10:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
      rewrite P70. reflexivity. }
    assert (G11 : getr R 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity).
    assert (G12 : getr R 12 = Z_to_bv 64 65536) by (regv HR (12:reg); reflexivity).
    assert (G13 : getr R 13 = Z_to_bv 64 1) by (regv HR (13:reg); reflexivity).
    destruct (enframe_run M (Z_to_bv 64 1) _ _ _ _ _ _ _ _ _ _ EF R (seg_rom RSEGS) (Z_to_bv 64 0x12b3c)
                G1 RT G10 G11 G12 G13) as (R2 & Hms & Hkeep & HA0).
    clear RT G1 G10 G11 G12 G13.
    replace (Z_to_bv 64 101956) with (0x18e44 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
    (* [comment removed for export] *)
    replace (memF M 0 65536 69616 (bv_unsigned gm + 16) 1) with (mem_denot (ENVv vals) M LOGE).
    2:{ unfold memF. cbv delta [mF mE mE1 mD] beta zeta.
        replace (69616 - 4 - 65536 - 16 * 1)%Z with 4060%Z by reflexivity.
        replace (69616 * 0 / 16 + 1)%Z with 1%Z by reflexivity.
        change (1 =? 0)%Z with false. change (4060 =? 0)%Z with false. change (4060 <? 5)%Z with false.
        cbv iota.
        replace (0 + 32 * res_code 4060)%Z with 160%Z by reflexivity.
        replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 13)%Z by lia.
        replace (bv_unsigned gm + 16 - 2)%Z with (bv_unsigned gm + 14)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 4)%Z with (bv_unsigned gm + 28)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 3)%Z with (bv_unsigned gm + 29)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 2)%Z with (bv_unsigned gm + 30)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 + 65536)%Z with (bv_unsigned gm + 65568)%Z by lia.
        replace (bv_unsigned gm + 16 + 69616 - 4 - 5)%Z with (bv_unsigned gm + 69623)%Z by lia.
        replace (bv_unsigned gm + 16 + 69616 - 4 - 4)%Z with (bv_unsigned gm + 69624)%Z by lia.
        unfold LOGE. cbn [mem_denot]. unfold adenot. cbn [a_base a_off edenot gx ev ENV]. fold gm. unfold v_addi.
        change (word_to_le_bytes 1 (Z_to_bv 64 160)) with [Z_to_bv 8 160].
        change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
        change (word_to_le_bytes 1 (Z_to_bv 64 224)) with [Z_to_bv 8 224].
        reflexivity. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?MG ?kn =>
      pose proof (carry_after RSEGS E MG LOGE kn [] knZ [] _ ltac:(vm_compute; reflexivity)
                    ltac:(cbn [log_flat LOGE]; unfold flat, estart; cbn [a_base a_off edenot gx ev ENV]; fold gm;
                          repeat split; lia)
                    HK ltac:(constructor)) as HK2
    end.
    (* [comment removed for export] *)
    assert (HSI2 : SI (mem_denot (ENVv vals) M LOGE)).
    { apply (SI_step M); [|exact HSI]. intros xa Hxa.
      apply (mem_denot_above_band RSEGS (ENVv vals) _ M knZ LOGE 0%nat 0x52000 0x7fff7f800000 xa HK2);
        [vm_compute; reflexivity | lia | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia | lia]. }
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr _ =>
      pose proof (regs_after_keeps vals _ sr R R2 callee_saved ltac:(rewrite HL; vm_compute; reflexivity)
                    HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR.
    set (vals2 := vals ++ junk_vals R2) in *.
    assert (HL2 : length vals2 = 105%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
    assert (Q72 : vals_ev vals2 72 = gm) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
    change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2.
    pose proof (regs_ok_set_have (ENVv vals2) _ R2 10 _ (EAlu ALU_ADD gx (ELit 32)) HR2 HA0
                  ltac:(rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot gx ev ENV];
                        rewrite Q72; f_equal; lia) ltac:(discriminate)) as HR3.
    clear HR2.
    lazymatch type of HR3 with regs_ok _ ?sr _ => replace sr with srZ in HR3 by (vm_compute; reflexivity) end.
    lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
    clear HK2 HK.
    change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HK3.
    change (mem_denot (Env (vals_ev vals) (blobs_ev (blobs0 a0s path))) M LOGE) with (mem_denot (ENVv vals) M LOGE) in HSI2.
    apply (EXIT vals2 R2 _ VM HL2 Q0 Q2 Q70 Q5 HR3 HK3); [rewrite Q72; exact HVM | rewrite Q72; exact HVS | exact HSI2].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition VMk : VmMaps :=
    mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0.
  Definition VMo : VmMaps :=
    mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [(brk, Z_to_bv 64 4096)] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0.
  Definition vm_mid (VM : VmMaps) : Prop := VM = VMo.

  Lemma RES_eq : RES = [(Z_to_bv 64 65536, Z_to_bv 64 8192); (Z_to_bv 64 73728, Z_to_bv 64 57344);
                        (Z_to_bv 64 131072, Z_to_bv 64 4096); (Z_to_bv 64 135168, Z_to_bv 64 200704)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma vm_mid_grant_exists : forall hint VM, vm_mid VM -> exists a, grant_ok hint (modelV VM) a (page_round_up_Z 69632) = true.
  Proof.
    intros hint VM HV. unfold vm_mid in HV. subst VM. pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi.
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
    change (page_round_up_Z 69632) with 69632%Z.
    apply grant_exists.
    - lia.
    - rewrite mV_vmmaps. cbn [VMo vm_reserved vm_maps]. rewrite RES_eq. cbn [app].
      repeat constructor; cbn [snd]; rewrite ?u64_lit by lia; lia.
    - rewrite mV_vmmaps. cbn [VMo vm_reserved vm_maps]. rewrite RES_eq. cbn [length app Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - apply grant_budget_intro; [reflexivity | reflexivity |]. rewrite mV_vmmaps.
      unfold vm_live_bytes. cbn [VMo vm_maps vm_limit live_bytes fst snd]. rewrite ?u64_lit by lia. pose proof LIM_ge. lia.
    - rewrite mV_vmmaps, alloc_top_val. cbn [VMo vm_init_sp]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vm_mid_grant : forall hint VM a, vm_mid VM -> grant_ok hint (modelV VM) a 69632 = true ->
    (bv_unsigned a mod 4096 = 0 /\ 0x52000 <= bv_unsigned a /\ bv_unsigned a + 69632 <= bv_unsigned sp0 - 8388608
     /\ (bv_unsigned brk + 8192 <= bv_unsigned a \/ bv_unsigned a + 69632 <= bv_unsigned brk))%Z.
  Proof.
    intros hint VM a HV Hg. unfold vm_mid in HV. subst VM. pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi.
    destruct (grant_ok_unpack _ _ _ _ Hg) as (Hal & Hpos & Hce & Hrf & Hlive).
    rewrite mV_vmmaps in Hrf, Hce. rewrite alloc_top_val in Hce. cbn [VMo vm_reserved vm_maps vm_init_sp] in Hrf, Hce.
    rewrite RES_eq in Hrf.
    unfold page_size in Hal. pose proof (u64_range a) as Ha.
    assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
    pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 8192) Hrf ltac:(cbn [In app]; tauto)) as D1.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 135168) (Z_to_bv 64 200704) Hrf ltac:(cbn [In app]; tauto)) as D4.
    pose proof (region_free_In _ _ _ brk (Z_to_bv 64 8192) Hrf ltac:(cbn [In app]; tauto)) as D5.
    rewrite Hn in D1, D4, D5. rewrite !u64_lit in D1 by lia. rewrite !u64_lit in D4 by lia. rewrite (u64_lit 8192) in D5 by lia.
    repeat split; lia.
  Qed.

  Lemma w65_mid : forall vals R M VM,
    exitG_branch ->
    length vals = 72%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
    regs_ok (ENVv vals) srM R -> know_ok RSEGS (ENVv vals) M knM -> vm_mid VM -> SI M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x180e4) M (seg_rom RSEGS)) (modelV VM)) K.
  Proof.
    intros vals R M VM EXIT HL P0 P2 P70 P5 HR HK HV HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    run_block_keep scr0 72%nat. si_block HSI R M.
    (* [comment removed for export] *)
    eapply (rz_mmap_anon RSEGS _ _ _ (modelV VM) ECALLW 69632).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (11 : reg). reflexivity.
    - lia.
    - regv HR (12 : reg). reflexivity.
    - regv HR (13 : reg). reflexivity.
    - regv HR (14 : reg). apply bv_eq. reflexivity.
    - regv HR (15 : reg). reflexivity.
    - apply vm_mid_grant_exists. exact HV.
    - (* [comment removed for export] *)
      intros a Hg. rewrite v_addi_pc4 by lia. change (0x191d4 + 4)%Z with 0x191d8%Z.
      change (page_round_up_Z 69632) with 69632%Z in Hg |- *.
      destruct (vm_mid_grant _ VM a HV Hg) as (Gal & Glo & Ghi & Gdj).
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [a] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [a] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      clear HR HK.
      set (vals2 := vals ++ [a]) in *.
      assert (HL2 : length vals2 = 73%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
      assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
      assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (Q72 : vals_ev vals2 72 = a).
      { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
      clearbody vals2. clear HL P0 P2 P70 P5 vals. rename HL2 into HL.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2, HK2.
      pose proof (regs_set_a0 (ENVv vals2) _ _ a gx HR2 ltac:(cbn [edenot gx ev ENV]; exact Q72)) as HR. clear HR2.
      (* [comment removed for export] *)
      lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
        assert (HK3 : know_ok RSEGS (ENVv vals2) Mc knG00) end.
      { unfold knG00. apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]]]].
        - apply kalign_intro; [lia|]. cbn [edenot gx ev ENV]. rewrite Q72. exact Gal.
        - apply krange_intro. cbn [edenot gx ev ENV]. rewrite Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot gx ev ENV]. rewrite Q0, Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot bx gx ev ENV]. rewrite Q70, Q72. lia. }
      clear HK2.
      pose proof (xfer_zfill RSEGS (ENVv vals2) _ knG00 gx 0 a 69632 HK3
                    ltac:(unfold estart; cbn [a_base a_off edenot gx ev ENV]; rewrite Q72; lia)
                    ltac:(lia) ltac:(lia)) as HK.
      clear HK3.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knG0 in HK by (vm_compute; reflexivity) end.
      apply (w65_G vals2 _ _ _ EXIT HL Q0 Q2 Q70 Q5 HR HK).
      3:{ si_fill HSI. }
      2:{ rewrite Q72. unfold vm_mid in HV. subst VM.
          unfold w65_vm, mmap_model. rewrite ?with_vmmaps_vm, ?mV_vmmaps.
          cbn [VMo vm_reserved vm_limit vm_maps vm_init_sp].
          split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. lia. }
      (* [comment removed for export] *)
      rewrite Q72. unfold vm_mid in HV. subst VM.
      unfold vm_pre, mmap_model. rewrite ?with_vmmaps_vm, ?mV_vmmaps.
      cbn [VMo vm_reserved vm_limit vm_maps vm_noaccess vm_start_brk vm_brk vm_init_sp].
      assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
      assert (Hn8 : bv_unsigned (Z_to_bv 64 8192) = 8192%Z) by (apply u64_lit; lia).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply map_has_head|].
      split.
      { constructor; [cbn [fst snd]; rewrite ?Hn; lia|]. constructor; [|constructor].
        cbn [fst snd]. rewrite Hn8. lia. }
      split; [cbn; lia|].
      split; [cbn [live_bytes fst snd]; rewrite Hn, Hn8; lia|].
      split.
      { exists (brk, Z_to_bv 64 8192). split; [cbn [In]; tauto|]. cbn [fst snd].
        split; [intros Emp; apply (f_equal bv_unsigned) in Emp; lia|]. rewrite Hn8. lia. }
      (* [comment removed for export] *)
      constructor; [|constructor; [constructor | constructor]].
      constructor; [|constructor]. unfold UbTargetPre.iv_disjoint. cbn [fst snd]. rewrite Hn, Hn8. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac guard_tail EXIT HL P0 P1 P2 P70 P5 VMX HSI Rn Mn :=
    run_blockW_keep scr0 71%nat; si_block HSI Rn Mn;
    lazymatch goal with
    | HR' : regs_ok _ ?sr ?R', HK' : know_ok _ _ ?M' ?kn |- _ =>
      (* [comment removed for export] *)
      pose proof (env_app_regs _ [getr R' 10] _ sr R' ltac:(rewrite HL; vm_compute; reflexivity) HR') as HR2;
      pose proof (env_app_know RSEGS _ [getr R' 10] _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK') as HK2;
      clear HR' HK';
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst _ _ _ _) _) _ =>
        lazymatch type of HL with length ?vals = _ =>
        set (vals2 := vals ++ [getr R' 10]) in *;
        assert (HL2 : length vals2 = 72%nat) by (subst vals2; rewrite length_app, HL; reflexivity);
        assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0);
        assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2);
        assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70);
        assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5);
        assert (Q71 : vals_ev vals2 71 = getr R' 10)
          by (subst vals2; rewrite <- HL; rewrite <- (Nat.add_0_r (length vals)); rewrite vals_ev_app_r; reflexivity);
        change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2, HK2;
        pose proof (regs_ok_set_have (ENVv vals2) _ R' 10 _ (EVar 71) HR2 eq_refl
                      ltac:(cbn [edenot ev ENV]; exact Q71) ltac:(discriminate)) as HR3;
        clear HR2;
        lazymatch type of HR3 with regs_ok _ ?sr3 _ => replace sr3 with srM in HR3 by (vm_compute; reflexivity) end;
        pose proof (know_ok_sub RSEGS (ENVv vals2) M' kn knM ltac:(vm_compute; reflexivity) HK2) as HK3;
        clear HK2;
        apply (w65_mid vals2 R' M' VMX EXIT HL2 Q0 Q2 Q70 Q5 HR3 HK3); [ | exact HSI ]
        end
      end
    end.

  Theorem brk_ok_worldV : exitG_branch -> brk_ok_entry K.
  Proof.
    intros EXIT vals R M HL P0 P70 P1 P2 P5 HR HK HSI0.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    assert (HSI : SI (zfill brk (Z_to_bv 64 8192) M)) by si_fill HSI0. clear HSI0.
    (* [comment removed for export] *)
    pose proof (regs_set_a0 (ENVv vals) _ _ (Z_to_bv 64 (bv_unsigned brk + 8192)) (EAlu ALU_ADD bx (ELit 8192)) HR
                  ltac:(rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot bx ev ENV];
                        rewrite P70; reflexivity)) as HR1. clear HR.
    lazymatch type of HR1 with regs_ok _ ?sr _ => replace sr with srW0 in HR1 by (vm_compute; reflexivity) end.
    (* [comment removed for export] *)
    pose proof (xfer_zfill RSEGS (ENVv vals) M knD2 bx 0 brk 8192 HK
                  ltac:(unfold estart; cbn [a_base a_off edenot bx ev ENV]; rewrite P70; lia) ltac:(lia)
                  ltac:(pose proof (u64_range brk); lia)) as HK0. clear HK.
    pose proof (kderive_all_sound RSEGS (ENVv vals) _ _ knW0 HK0 ltac:(vm_compute; reflexivity)) as HK1. clear HK0.
    rename HR1 into HR. rename HK1 into HK.
    change (mkModelC fdsV (mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0)
                    stdin0 fs0 None (Some tid) None) with (modelV VMk).
    (* [comment removed for export] *)
    run_block_keep scr0 71%nat. si_block HSI R M.
    (* [comment removed for export] *)
    eapply (rz_mmap_fixed_noaccess RSEGS _ _ _ (modelV VMk) ECALLW brk 4096).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). cbn [edenot bx ev ENV]. exact P70.
    - exact Bal.
    - lia.
    - regv HR (11 : reg). reflexivity.
    - lia.
    - change (page_round_up_Z 4096) with 4096%Z. rewrite mV_vmmaps, alloc_top_val. cbn [VMk vm_init_sp]. lia.
    - regv HR (12 : reg). reflexivity.
    - regv HR (13 : reg). reflexivity.
    - regv HR (14 : reg). apply bv_eq. reflexivity.
    - regv HR (15 : reg). reflexivity.
    - rewrite mV_vmmaps. cbn [VMk vm_reserved]. apply region_free_above_top. rewrite rtop. lia.
    - rewrite mV_vmmaps. cbn [VMk vm_maps]. change (page_round_up_Z 4096) with 4096%Z.
      apply map_contains_head; rewrite ?u64_lit by lia; lia.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x191d4 + 4)%Z with 0x191d8%Z.
      change (page_round_up_Z 4096) with 4096%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc brk bx HR ltac:(cbn [edenot bx ev ENV]; exact P70)) as HR1 end.
      clear HR. rename HR1 into HR.
      lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
        pose proof (xfer_unfill RSEGS E Mc kn bx 0 brk 4096 HK
                      ltac:(unfold estart; cbn [a_base a_off edenot bx ev ENV]; rewrite P70; lia) ltac:(lia)
                      ltac:(pose proof (u64_range brk); lia)) as HK1 end.
      clear HK. rename HK1 into HK.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knU in HK by (vm_compute; reflexivity) end.
      change (fixed_noaccess_model brk (Z_to_bv 64 4096) (modelV VMk)) with (modelV VMo).
      lazymatch type of HK with know_ok _ _ ?Mc _ => assert (HSI2 : SI Mc) by si_fill HSI end.
      clear HSI. rename HSI2 into HSI.
      guard_tail EXIT HL P0 P1 P2 P70 P5 VMo HSI R M. reflexivity.
  Qed.
End World.

(* [comment removed for export] *)
Theorem brk_ok_world_g {AMB : Amb} sp0 a0s path envv tid mem0 brk mbase fs0 stdin0
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) fd3 K :
  exitG_branch sp0 a0s path envv tid brk fs0 stdin0 fd3 (above_eq sp0 mem0) K ->
  brk_ok_branch_g sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 fd3 K.
Proof.
  intros EXIT. exact (brk_ok_worldV sp0 a0s path envv tid brk mbase fs0 stdin0 Hvsp Htid Hbrk Hplen fd3
                        (above_eq sp0 mem0) (above_eq_step sp0 mem0) K EXIT).
Qed.

Theorem brk_ok_world {AMB : Amb} sp0 a0s path envv tid mem0 brk mbase fs0 stdin0
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) K :
  exitG_branch sp0 a0s path envv tid brk fs0 stdin0 (FdFile path (Z_to_bv 64 0)) (above_eq sp0 mem0) K ->
  brk_ok_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 K.
Proof. exact (brk_ok_world_g sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 Hvsp Htid Hbrk Hplen (FdFile path (Z_to_bv 64 0)) K). Qed.
End WithFP2.
End UbW65.

Module UbW65x.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SimInv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ExitSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWritev OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefLayout OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStartup OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbMainEntry OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbWorld OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetPre.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPilotOOM.UbPilotOOM_defs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPilotOOM.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymAbove OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbAboveBand UbW65_defs UbW65.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Definition off_image (x : Z) : Prop := (x + 1 <= 0x10000 \/ 0x52000 <= x)%Z.

Lemma find_segment_skip : forall seg rest a n,
  (0 < n)%Z ->
  (a < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) < a + n)%Z ->
  find_segment (seg :: rest) a n = find_segment rest a n.
Proof.
  intros seg rest a n Hn H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base seg)) a); destruct (Z.leb_spec (a + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)));
    cbn [andb]; try reflexivity. lia.
Qed.

Lemma find_segment_off : forall a n, (0 < n)%Z -> (a + n <= 0x10000 \/ 0x52000 <= a)%Z ->
  find_segment RSEGS a n = None.
Proof.
  intros a n Hn H. unfold Ubsan.M.loaded_segments, Ubsan_loaded_segments.
  rewrite 4 find_segment_skip; [reflexivity | exact Hn | | exact Hn | | exact Hn | | exact Hn |];
    cbn [seg_base seg_size Ubsan_segment_000 Ubsan_segment_001 Ubsan_segment_002 Ubsan_segment_003]; lia.
Qed.

Lemma seg_rom_off : forall x : word, off_image (bv_unsigned x) -> seg_rom RSEGS x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. rewrite find_segment_off; [reflexivity | cbn; lia | unfold off_image in Hx; cbn; lia].
Qed.

Lemma wview_off : forall M (x : word), off_image (bv_unsigned x) -> wview RSEGS M x = M x.
Proof.
  intros M x Hx. unfold wview. destruct (M x); [reflexivity|].
  rewrite find_segment_off; [reflexivity | lia | unfold off_image in Hx; lia].
Qed.

Lemma rdn1_off : forall M (x : word) b, off_image (bv_unsigned x) ->
  rdn RSEGS M x 1 = Some [b] -> M x = Some b.
Proof.
  intros M x b Hx H. cbn [rdn] in H. rewrite (seg_rom_off x Hx) in H.
  destruct (M x) as [b0|]; [|discriminate]. injection H as ->. reflexivity.
Qed.

Lemma store_ok1_off : forall M (x : word), off_image (bv_unsigned x) ->
  store_ok RSEGS M x 1 = true -> M x <> None.
Proof.
  intros M x Hx H. cbn [store_ok] in H. rewrite (wview_off M x Hx) in H.
  destruct (M x); [discriminate | discriminate].
Qed.

Lemma u64_lit' : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

Lemma u0 : bv_unsigned (Z_to_bv 64 0) = 0%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cell_intro : forall M (x : word) n (v : word) (a z : Z),
  rdn RSEGS M x n = Some (word_to_le_bytes n v) ->
  x = Z_to_bv 64 a -> v = Z_to_bv 64 z -> cell M a n z.
Proof. intros M x n v a z H -> ->. exact H. Qed.

Lemma zero_bytes_intro : forall E M b k n a,
  kentry_ok RSEGS E M (KZero (SA b k) (ELit n)) -> (0 <= n < 2 ^ 64)%Z ->
  (bv_unsigned (edenot E b) + k)%Z = a -> zero_bytes M a n.
Proof.
  intros E M b k n a [Hf Hz] Hn Ha i Hi. unfold estart, elenZ in Hz. cbn [a_base a_off edenot] in Hz.
  rewrite u64_lit' in Hz by lia. rewrite <- Ha. apply Hz. lia.
Qed.

Lemma def_intro : forall E M b kk len a n,
  kentry_ok RSEGS E M (KWr (SA b kk) len) ->
  (bv_unsigned (edenot E b) + kk <= a)%Z -> (a + n <= bv_unsigned (edenot E b) + kk + len)%Z ->
  (a + n <= 0x10000 \/ 0x52000 <= a)%Z -> (0 <= a)%Z -> (a + n <= 2 ^ 64)%Z ->
  forall i, (0 <= i < n)%Z -> M (Z_to_bv 64 (a + i)) <> None.
Proof.
  intros E M b kk len a n [Hf Hst] H1 H2 Hoff H0 H64 i Hi.
  unfold estart in Hst. cbn [a_base a_off] in Hst.
  specialize (Hst (a + i - (bv_unsigned (edenot E b) + kk))%Z 1%nat ltac:(lia) ltac:(cbn; lia)).
  replace (bv_unsigned (edenot E b) + kk + (a + i - (bv_unsigned (edenot E b) + kk)))%Z with (a + i)%Z in Hst by lia.
  refine (store_ok1_off M _ _ Hst). unfold off_image; rewrite u64_lit' by lia; lia.
Qed.

Lemma byte_intro : forall M a v,
  cell M a 1 v -> word_to_le_bytes 1 (Z_to_bv 64 v) = [Z_to_bv 8 v] ->
  (0 <= a)%Z -> (a + 1 <= 2 ^ 64)%Z -> (a + 1 <= 0x10000 \/ 0x52000 <= a)%Z ->
  M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros M a v Hc Hw H0 H64 Hoff. unfold cell in Hc. rewrite Hw in Hc.
  apply rdn1_off; [unfold off_image; rewrite u64_lit' by lia; lia | exact Hc].
Qed.

Lemma img_clear_of_know : forall E M ivs,
  know_ok RSEGS E M (map (fun iv => KImg (fst iv) (snd iv)) ivs) ->
  Forall (fun iv => img_clear M (fst iv) (snd iv)) ivs.
Proof.
  intros E M ivs HK. unfold know_ok in HK. rewrite Forall_map in HK.
  eapply Forall_impl; [|exact HK]. intros [lo hi] (A & B & C). exact C.
Qed.

(* [comment removed for export] *)
Lemma errno_some : forall M, exists bs,
  rdn RSEGS M (Z_to_bv 64 0x31434) 4 = Some bs /\ length bs = 4%nat.
Proof.
  intros M. cbn [rdn].
  repeat match goal with
  | |- context [match M ?x with _ => _ end] =>
      destruct (M x); [| let r := eval vm_compute in (seg_rom RSEGS x) in change (seg_rom RSEGS x) with r]
  end; eexists; split; reflexivity.
Qed.
End WithFP1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac addr_split a :=
  lazymatch a with
  | bv_unsigned ?x =>
      lazymatch x with
      | vals_ev _ ?i => constr:((EVar i, 0%Z))
      | _ => lazymatch goal with P : vals_ev _ ?i = x |- _ => constr:((EVar i, 0%Z)) end
      end
  | (?y + ?c)%Z =>
      lazymatch y with
      | context [bv_unsigned _] =>
          lazymatch addr_split y with (?b, ?k) => let k' := eval vm_compute in (k + c)%Z in constr:((b, k')) end
      | _ => let a' := eval vm_compute in a in constr:((ELit 0, a'))
      end
  | (?y - ?c)%Z =>
      lazymatch y with
      | context [bv_unsigned _] =>
          lazymatch addr_split y with (?b, ?k) => let k' := eval vm_compute in (k - c)%Z in constr:((b, k')) end
      | _ => let a' := eval vm_compute in a in constr:((ELit 0, a'))
      end
  | _ => let a' := eval vm_compute in a in constr:((ELit 0, a'))
  end.

(* [comment removed for export] *)
Ltac kside :=
  rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV gx bx]; rewrite ?u0; pins;
  rewrite ?ext_val_zx_id by (cbn; lia);
  first [ reflexivity
        | symmetry; apply Z_to_bv_bv_unsigned
        | rewrite Z_to_bv_bv_unsigned; (reflexivity || assumption || (symmetry; assumption))
        | f_equal; lia
        | lia ].

(* [comment removed for export] *)
Ltac kcell HK :=
  lazymatch goal with |- cell ?M ?a ?n ?z =>
  lazymatch type of HK with know_ok ?segs ?E M ?kn =>
  lazymatch addr_split a with (?b, ?k) =>
    let r := eval vm_compute in (kread segs kn b k n) in
    lazymatch r with
    | Some ?v =>
        apply (cell_intro M (adenot E (SA b k)) n (edenot E v) a z);
        [ apply (kread_rdn segs E M kn b k n v HK); [vm_compute; reflexivity | cbn; lia | cbn; lia
          | apply flat_intro; cbn [edenot ev ENV gx bx]; rewrite ?u0; pins; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ]
        | kside
        | kside ]
    | None => fail "kcell: knowledge does not determine" b k n
    end end end end.

(* [comment removed for export] *)
Ltac krdn HK :=
  lazymatch goal with |- rdn _ ?M (Z_to_bv 64 ?a) ?n = Some (word_to_le_bytes _ (Z_to_bv 64 ?z)) =>
    change (cell M a n z); kcell HK end.

(* [comment removed for export] *)
Ltac kzero HK :=
  lazymatch goal with |- zero_bytes ?M ?a ?n =>
  lazymatch type of HK with know_ok ?segs ?E M ?kn =>
  lazymatch addr_split a with (?b, ?k) =>
    let n' := eval vm_compute in n in
    apply (zero_bytes_intro E M b k n' a);
    [ apply (kderive_sound segs E M kn (KZero (SA b k) (ELit n')) HK); vm_compute; reflexivity
    | lia
    | cbn [edenot ev ENV gx bx]; rewrite ?u0; pins; lia ]
  end end end.

(* [comment removed for export] *)
Ltac kbyte HK :=
  lazymatch goal with |- ?M (Z_to_bv 64 ?a) = Some (Z_to_bv 8 ?v) =>
    apply (byte_intro M a v); [kcell HK | reflexivity | pins; lia | pins; lia | pins; lia] end.

(* [comment removed for export] *)
Ltac kdef HK b kk len :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
    apply (def_intro E M b kk len);
    [ apply (kderive_sound segs E M kn (KWr (SA b kk) len) HK); vm_compute; reflexivity
    | cbn [edenot ev ENV gx bx]; pins; lia
    | cbn [edenot ev ENV gx bx]; pins; lia
    | cbn [edenot ev ENV gx bx]; pins; lia
    | cbn [edenot ev ENV gx bx]; pins; lia
    | cbn [edenot ev ENV gx bx]; pins; lia ]
  end.

(* [comment removed for export] *)
Section WithFP2. Context {FP : PropExec.FPState}.
Lemma cell_join : forall M a n1 n2 v1 v2 v,
  cell M a n1 v1 -> cell M (a + Z.of_nat n1) n2 v2 ->
  word_to_le_bytes n1 (Z_to_bv 64 v1) ++ word_to_le_bytes n2 (Z_to_bv 64 v2) = word_to_le_bytes (n1 + n2) (Z_to_bv 64 v) ->
  (0 <= a)%Z -> (a + Z.of_nat n1 < 2 ^ 64)%Z -> cell M a (n1 + n2) v.
Proof.
  unfold cell. intros M a n1 n2 v1 v2 v H1 H2 Hw Ha Hn. rewrite <- Hw.
  apply rdn_app; [exact H1|]. rewrite w_add_nat, u_small by lia. exact H2.
Qed.

(* [comment removed for export] *)
Lemma kwr_window : forall E M kn b kk len base,
  know_ok RSEGS E M kn -> kderive RSEGS kn (KWr (SA b kk) len) = true ->
  (bv_unsigned (edenot E b) + kk)%Z = base ->
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= len)%Z -> store_ok RSEGS M (Z_to_bv 64 (base + d)) m = true.
Proof.
  intros E M kn b kk len base HK Hd Hb d m H0 Hm.
  destruct (kderive_sound RSEGS E M kn _ HK Hd) as [Hf Hst]. unfold estart in Hst. cbn [a_base a_off] in Hst.
  rewrite Hb in Hst. apply Hst; assumption.
Qed.

(* [comment removed for export] *)
Definition fG (i : nat) : nat := if Nat.eqb i 2 then 70%nat else if Nat.eqb i 3 then 72%nat else i.
End WithFP2.


(* [comment removed for export] *)
Ltac kreg HR :=
  lazymatch goal with |- getr ?R ?r = _ =>
  lazymatch type of HR with regs_ok ?E ?sr R =>
    let e := eval vm_compute in (sr_get sr r) in
    rewrite (reg_val E sr R r HR); change (sr_get sr r) with e; kside
  end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithFP3. Context {FP : PropExec.FPState}.
Section World.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rndb : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid rndb regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : path <> dot_path.
  Hypothesis Hplen : (length path <= 4095)%nat.
  Variable fd3 : FdEntry.      (* [comment removed for export] *)
  Variable SI : (word -> option byte) -> Prop.   (* [comment removed for export] *)
  Hypothesis SI_step : forall M M' : word -> option byte,
    (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M' a = M a) -> SI M -> SI M'.

  #[local] Notation ENVv := (ENV a0s path).
  #[local] Notation modelV := (modelV tid fs0 stdin0 fd3).

  (* [comment removed for export] *)
  Definition vm_small (VM : VmMaps) (gm : word) : Prop :=
    vm_reserved VM = segments_reserved RSEGS /\ vm_limit VM = LIM
    /\ (length (vm_maps VM) <= 4)%nat
    /\ In (gm, Z_to_bv 64 69632) (vm_maps VM)
    /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 69632)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM)
    /\ seps (vm_maps VM).

  (* [comment removed for export] *)
  Definition after_malloc (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm sec cnr : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->
      read_pre sp0 (p1 sp0 a0s path envv) mb gm sec cnr R M ->
      world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb gm -> vm_small VM gm ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b3c) M (seg_rom RSEGS))
                              (model_pre path VM stdin0 fs0 tid)) K.

  (* [comment removed for export] *)
  Definition after_malloc_gen (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm sec cnr : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->
      read_pre sp0 (p1 sp0 a0s path envv) mb gm sec cnr R M ->
      world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb gm -> vm_small VM gm -> SI M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b3c) M (seg_rom RSEGS))
                              (mkModelC (fdsV fd3) VM stdin0 fs0 None (Some tid) None)) K.

  Lemma modelV_eq : forall VM, modelV VM = mkModelC (fdsV fd3) VM stdin0 fs0 None (Some tid) None.
  Proof. intros VM. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma p1_range : (0x7fff80000000 <= bv_unsigned (p1 sp0 a0s path envv) <= 0x800000400000)%Z.
  Proof.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *.
    unfold p1. rewrite (u_cat_argv_ptr Ubsan.M.phdrs sp0 [a0s; path] envv a_uid a_hwcap rndb Hva Hve) by (cbn; lia || (unfold sp_window_lo, sp_window_hi; cbn; lia)).
    pose proof (struct_av_bound Ubsan.M.phdrs sp0 [a0s; path] envv a_uid a_hwcap rndb Hva Hve).
    pose proof (CatExec.total_arg_bytes_firstn_le 1 [a0s; path]). lia.
  Qed.

  Variable K : TSet.

  Lemma w65_exitG : after_malloc_gen K -> exitG_branch sp0 a0s path envv tid brk fs0 stdin0 fd3 SI K.
  Proof.
    intros AM vals R M VM HL P0 P2 P70 P5 HR HK HVM HVS HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV gx bx] in Kgm.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV gx bx] in Kga.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_kdisj bx gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ev ENV gx bx] in Kgd; rewrite P70 in Kgd.
    pose proof p1_range as P1r.
    pose proof (u64_range brk) as Bu. pose proof (u64_range sp0) as Su.
    rewrite modelV_eq.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_kdisj (EVar 0) gx) in exact i) _ HK eq_refl)
      as Kband; cbn [kentry_ok] in Kband; unfold estart in Kband; cbn [a_base a_off edenot ev ENV gx bx] in Kband; rewrite P0 in Kband.
    apply (AM R M VM brk (vals_ev vals 72) (vals_ev vals 7) (vals_ev vals 8) (bv_unsigned brk + 4096)%Z (bv_unsigned brk + 8192)%Z 0%Z).
    - reflexivity.
    - (* [comment removed for export] *)
      constructor.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + lia.
      + exact P1r.
      + lia.
      + lia.
      + lia.
      + unfold stack_writable. apply (kwr_window (ENVv vals) M knZ (EVar 0) (-8388608) 8388608); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV gx bx]; pins; lia].
      + unfold group_writable. apply (kwr_window (ENVv vals) M knZ gx 0 69632); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV gx bx]; pins; lia].
      + unfold meta_writable. apply (kwr_window (ENVv vals) M knZ bx 4096 4096); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV gx bx]; pins; lia].
      + destruct (errno_some M) as (bs & Hbs & Hlen). exists (Z_to_bv 64 (bytes_le_to_Z bs)).
        rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + intros x0 x1 x4 x5 x6 extra ebs.
        apply (know_ok_ren RSEGS (ENVv vals) _ M fG [2;3;7;8]%nat kn_M1).
        * intros i Hi. destruct Hi as [<-|[<-|[<-|[<-|[]]]]]; cbn [ev ENV fG Nat.eqb vals_ev nth app]; pins; reflexivity.
        * vm_compute. reflexivity.
        * apply (kderive_all_sound RSEGS _ M knZ); [exact HK | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      constructor.
      all: try kcell HK.
      all: try kzero HK.
      + apply (cell_join M _ 4 4 101 0); [kcell HK | kcell HK | reflexivity | lia | lia].
      + apply (cell_join M _ 4 4 0 0); [kcell HK | kcell HK | reflexivity | lia | lia].
      + kdef HK bx 4096%Z 4096%Z.
      + (* [comment removed for export] *)
        constructor; cbn zeta.
        * kbyte HK.
        * kbyte HK.
        * krdn HK.
        * intros _. kbyte HK.
        * intros _. kbyte HK.
        * intros _. krdn HK.
        * intros _. kbyte HK.
        * intros _. krdn HK.
        * change (69616 * 0 / 16 + 1)%Z with 1%Z. lia.
      + kdef HK gx 0%Z 69632%Z.
      + replace (bv_unsigned brk + 4096)%Z with (bv_unsigned brk + 1 * 4096)%Z by lia. rewrite Z_mod_plus_full. exact Bal.
      + exact (proj2 Kga).
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + exact Htid.
      + destruct (errno_some M) as (bs & Hbs & Hlen). exists (bytes_le_to_Z bs).
        pose proof (SX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb.
        split; [cbn in Hb; lia|]. unfold cell. rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + apply (img_clear_of_know (ENVv vals)). apply (kderive_all_sound RSEGS _ M knZ); [exact HK | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      constructor. all: kcell HK.
    - exact HVM.
    - (* [comment removed for export] *)
      destruct HVS as (Hr & Hl & Hsp & Hm & Hdj). unfold vm_small. rewrite Hr, Hl.
      split; [reflexivity|]. split; [reflexivity|].
      assert (U1 : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by reflexivity.
      assert (U2 : bv_unsigned (Z_to_bv 64 8192) = 8192%Z) by reflexivity.
      rewrite Hm. cbn [length In fst snd].
      (split; [lia|]); (split; [left; reflexivity|]); split;
        [ repeat constructor; cbn [fst snd]; rewrite ?U1, ?U2, ?u64_lit' by lia; lia
        | apply seps_cons; [constructor; [unfold iv_disjoint; cbn [fst snd]; rewrite ?U1, ?U2, ?u64_lit' by lia; lia | constructor]
                          | apply seps_cons; [constructor | apply seps_nil]] ].
    - exact HSI.
  Qed.

  (* [comment removed for export] *)
  Theorem brk_ok_semV : after_malloc_gen K ->
    brk_ok_entry sp0 a0s path envv tid brk mbase fs0 stdin0 fd3 SI K.
  Proof. intros AM. apply brk_ok_worldV; try assumption. apply w65_exitG, AM. Qed.
End World.

(* [comment removed for export] *)
Theorem brk_ok_sem_g {AMB : Amb} sp0 a0s path envv tid (rndb : EntryDraw) mem0 brk mbase fs0 stdin0
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) fd3 K :
  after_malloc_gen sp0 a0s path envv tid fs0 stdin0 fd3 (above_eq sp0 mem0) K ->
  brk_ok_branch_g sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 fd3 K.
Proof.
  intros AM. exact (brk_ok_semV sp0 a0s path envv tid rndb brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hplen fd3
                      (above_eq sp0 mem0) (above_eq_step sp0 mem0) K AM).
Qed.

(* [comment removed for export] *)
Theorem brk_ok_sem {AMB : Amb} sp0 a0s path envv tid (rndb : EntryDraw) mem0 brk mbase fs0 stdin0
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) K :
  after_malloc sp0 a0s path envv tid fs0 stdin0 K ->
  brk_ok_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 K.
Proof.
  intros AM. apply (brk_ok_sem_g sp0 a0s path envv tid rndb mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hplen).
  intros R M VM mb gm sec cnr area brkv mas EA RP W MF VP VS _. exact (AM R M VM mb gm sec cnr area brkv mas EA RP W MF VP VS).
Qed.
End WithFP3.

End UbW65x.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import Amb PropExec CatExec CatSim SeqExec StepTac StoreOk ShapeAlg Hoare WalkTac SumWalkTac Frame MemSplit Nodes MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec RefNodes RefMemcpyLib RefLayout UbStartup UbMainEntry MallocDefs UbEnframeBase UbReadDefs UbReadBase UbWorld UbTargetPre UbReadStage UbReadChunkW Ub_code_1299c_12db8 Ub_code_1735c_17f20 Ub_code_1e6dc_1f0b8. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbPilotOOM. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbPilotOOM.UbPilotOOM_defs. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import UbPilotOOM SymAbove. Import UbW65_defs. Import UbW65. Import UbW65x.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.

Lemma store_ok_wbytes : forall segs m (b : word) bs (a : word) n,
  store_ok segs m a n = true -> store_ok segs (wbytes m b bs) a n = true.
Proof. intros segs m b bs a n H. eapply store_ok_mono; [apply wbytes_grows | exact H]. Qed.

(* [comment removed for export] *)
Definition loopE_kept : list reg := [3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Lemma walkE : forall regs mem rom (sp0 : Z) (s0v : word),
  getr regs 1 = Z_to_bv 64 0x1f0ac -> getr regs 2 = Z_to_bv 64 (sp0 - 144) ->
  getr regs 10 = Z_to_bv 64 (2 ^ 64 - 21) -> getr regs 4 = Z_to_bv 64 0x314d8 -> getr regs 8 = s0v ->
  (0x60000 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12bd0)) ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  store_ok RSEGS (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x12bd0))) (Z_to_bv 64 (sp0 - 144)) 8 = true ->
  store_ok RSEGS (wbytes (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x12bd0)))
                                (Z_to_bv 64 (sp0 - 144)) (word_to_le_bytes 8 s0v)) (Z_to_bv 64 0x31434) 4 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x1f004 : word) mem rom)
                 (mkst regs' (0x12d14 : word)
                       (wbytes (wbytes (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x12bd0)))
                                       (Z_to_bv 64 (sp0 - 144)) (word_to_le_bytes 8 s0v))
                               (Z_to_bv 64 0x31434) (word_to_le_bytes 4 (Z_to_bv 64 21))) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ (forall r, In r loopE_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 s0v Hra Hsp Ha0 Htp Hs0 SPlo SPhi RD SOK1 SOK2 SOK3.
  eexists. split.
  - stepret F_1f004 D_1f004 (0x1f0ac : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepLD8 F_1f0ac D_1f0ac (Z_to_bv 64 0x12bd0).
    stepn F_1f0b0 D_1f0b0. rewrite Hsp. sp_renorm.
    stepn F_1f0b4 D_1f0b4.
    (* [comment removed for export] *)
    stepn F_1771c D_1771c. stepn F_17720 D_17720.
    stepb_ft F_17724 D_17724 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_17728 D_17728. sp_renorm.
    stepST F_1772c D_1772c (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x12bd0) ltac:(exact SOK1).
    stepST F_17730 D_17730 (Z_to_bv 64 (sp0 - 144)) s0v ltac:(exact SOK2).
    (* [comment removed for export] *)
    stepn F_17734 D_17734. rewrite Ha0.
    stepn F_17738 D_17738.
    stepn F_17754 D_17754. rewrite Htp.
    stepn F_17758 D_17758.
    stepret F_1775c D_1775c (0x1773c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepST F_1773c D_1773c (Z_to_bv 64 0x31434) (Z_to_bv 64 21) ltac:(exact SOK3).
    (* [comment removed for export] *)
    stepn F_17740 D_17740.
    stepLD8 F_17744 D_17744 (Z_to_bv 64 0x12bd0).
    stepLD8 F_17748 D_17748 s0v.
    stepn F_1774c D_1774c. sp_renorm.
    stepret F_17750 D_17750 (0x12bd0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepb_tk F_12bd0 D_12bd0 ltac:(cond_compute).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia).
    intros r Hr; cbv [loopE_kept In] in Hr;
      repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; assumption | assumption] |]); destruct Hr.
Qed.

End WithFP1.

Section WithFP2. Context {FP : PropExec.FPState}.

(* [comment removed for export] *)
Definition re_ivs : list (Z * Z) :=
  [(0x10000,0x21380); (0x21381,0x213c9); (0x313c9,0x31408); (0x514e0,0x51500); (0x3143c,0x31488); (0x31490,0x314a8);
   (0x314b0,0x314c8); (0x314d8,0x314e8); (0x314f0,0x514e0); (0x51518,0x51744); (0x51750,0x51758); (0x51769,0x51770);
   (0x51778,0x51780); (0x51790,0x51798); (0x517a0,0x517d0); (0x517d8,0x517e0);
   (0x51830,0x51990); (0x51998,0x51b10); (0x51b18,0x51b70); (0x51b71,0x51b78); (0x51b88,0x52000)]%Z.

Ltac in_lit := idtac; repeat (first [left; reflexivity | right]).

Lemma re_ivs_incl : incl re_ivs img_clear_ivs.
Proof.
  unfold re_ivs, img_clear_ivs. intros x Hx.
  repeat (destruct Hx as [<-|Hx]; [in_lit|]). destruct Hx.
Qed.

Lemma re_ivs_of_world : forall M,
  Forall (fun iv => img_clear M (fst iv) (snd iv)) img_clear_ivs ->
  Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
Proof. intros M H. eapply incl_Forall; [apply re_ivs_incl | exact H]. Qed.

Lemma img_clear_transport : forall M M' ivs,
  Forall (fun iv => img_clear M (fst iv) (snd iv)) ivs ->
  (forall lo hi i, In (lo, hi) ivs -> (lo <= i < hi)%Z -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  Forall (fun iv => img_clear M' (fst iv) (snd iv)) ivs.
Proof.
  intros M M' ivs H HE. apply Forall_forall. intros [lo hi] Hin. pose proof (proj1 (Forall_forall _ _) H _ Hin) as C.
  cbn [fst snd] in *. intros i Hi. rewrite (HE lo hi i Hin Hi). apply C. exact Hi.
Qed.

(* [comment removed for export] *)
Record dir_tail_pre {AMB : Amb} (sp0 p1 : word) (tid cnr : Z) (mem0 : word -> option byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := DIR_TAIL_PRE {
  dt_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  dt_gp : getr R 3 = Z_to_bv 64 0x10800;
  dt_tp : getr R 4 = Z_to_bv 64 0x314d8;
  dt_s2 : getr R 18 = p1;                                  (* [comment removed for export] *)
  dt_stack : stack_writable M sp0;
  dt_img : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs;
  dt_tid : cell M 0x31430 4 tid;
  dt_tidr : (0 < tid < 2 ^ 22)%Z;
  dt_self : cell M 0x31410 8 0x31410;
  dt_canary : cell M 0x51748 8 cnr;
  dt_pagesz : cell M 0x51798 8 4096;
  dt_above : forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a
}.

Section DirMid.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rndb : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; dot_path] envv tid rndb regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.

  Lemma dot_len : (length dot_path <= 4095)%nat.
  Proof. cbn. lia. Qed.

  (* [comment removed for export] *)
  Definition modelDir (VM : VmMaps) : Model :=
    mkModelC (fd_insert fds0 (Z_to_bv 64 3) FdDir) VM stdin0 fs0 None (Some tid) None.

  (* [comment removed for export] *)
  Definition after_malloc_dir (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm sec cnr : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->
      read_pre sp0 (p1 sp0 a0s dot_path envv) mb gm sec cnr R M ->
      world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb gm -> vm_small VM gm ->
      above_eq sp0 mem0 M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b3c) M (seg_rom RSEGS)) (modelDir VM)) K.

  Theorem dir_brk : forall K, after_malloc_dir K ->
    brk_ok_branch_g sp0 a0s dot_path envv tid mem0 brk mbase fs0 stdin0 FdDir K.
  Proof.
    intros K AM. exact (brk_ok_sem_g sp0 a0s dot_path envv tid rndb mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk dot_len FdDir K AM).
  Qed.

  (* [comment removed for export] *)
  Theorem dir_read : forall K,
    (forall R' M' VM' (cnr : word), dir_tail_pre sp0 (p1 sp0 a0s dot_path envv) (bv_unsigned tid) (bv_unsigned cnr) mem0 R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x12d14) M' (seg_rom RSEGS)) (modelDir VM')) K) ->
    after_malloc_dir K.
  Proof.
    intros K TAIL R M VM mb gm sec cnr area brkv mas EA RP W MF VP VS HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *.
    pose proof RP as [Rsp Rgp Rtp Rs0 Ra0 Rs2 Rs4 Rs5 Hsp Hp1 Hb Hgm Hgb Hst Hgr Hmw Her Hkm].
    pose proof (u64_range sp0) as Usp.
    (* [comment removed for export] *)
    destruct (walkF R M (seg_rom RSEGS) (bv_unsigned gm + 32) Ra0 Rs5 ltac:(lia))
      as (R1 & RUN1 & A9 & A23 & A19 & A22 & AK).
    replace (Z_to_bv 64 0x12b3c) with (0x12b3c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact RUN1 |]. clear RUN1.
    (* [comment removed for export] *)
    assert (SOKra : store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = true).
    { replace (bv_unsigned sp0 - 136)%Z with (bv_unsigned sp0 - 8388608 + (8388608 - 136))%Z by lia. apply Hst; lia. }
    destruct (walkA R1 M (seg_rom RSEGS) (bv_unsigned sp0) 0 65536
                ltac:(rewrite (AK 2%bv) by in_lit; exact Rsp) A19 ltac:(rewrite (AK 21%bv) by in_lit; exact Rs5)
                ltac:(rewrite (AK 20%bv) by in_lit; exact Rs4) A22 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOKra)
      as (R2 & RUN2 & G17 & G10 & G11 & G12 & G1 & G2 & G9 & G19 & GK).
    eapply rz_msteps; [reflexivity | reflexivity | exact RUN2 |]. clear RUN2.
    set (M2 := wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x12bd0))) in *.
    (* [comment removed for export] *)
    eapply (rz_read_dir RSEGS R2 (0x1f000 : word) M2 (modelDir VM) ECALLW (Z_to_bv 64 3) K).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - exact G17.
    - exact G10.
    - reflexivity.
    - reflexivity.
    - rewrite G11, G12. apply Z.leb_le. vm_compute. reflexivity.
    - replace (v_addi (0x1f000 : word) 4) with (0x1f004 : word) by (apply bv_eq; reflexivity).
      (* [comment removed for export] *)
      assert (Ra2 : getr (regupd R2 10 (errno_ret EISDIR)) 1 = Z_to_bv 64 0x1f0ac) by (rewrite getr_other by discriminate; exact G1).
      assert (Sp2 : getr (regupd R2 10 (errno_ret EISDIR)) 2 = Z_to_bv 64 (bv_unsigned sp0 - 144)) by (rewrite getr_other by discriminate; exact G2).
      assert (A02 : getr (regupd R2 10 (errno_ret EISDIR)) 10 = Z_to_bv 64 (2 ^ 64 - 21)) by (rewrite getr_same by discriminate; apply bv_eq; reflexivity).
      assert (Tp2 : getr (regupd R2 10 (errno_ret EISDIR)) 4 = Z_to_bv 64 0x314d8).
      { rewrite getr_other by discriminate. rewrite (GK 4%bv) by in_lit. rewrite (AK 4%bv) by in_lit. exact Rtp. }
      assert (RD2 : rdn RSEGS M2 (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12bd0))).
      { subst M2. apply rdn_wbytes_hit8. rewrite u_small by lia. lia. }
      set (s0v := getr (regupd R2 10 (errno_ret EISDIR)) 8).
      assert (SOK1 : store_ok RSEGS M2 (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = true).
      { subst M2. apply store_ok_wbytes.
        replace (bv_unsigned sp0 - 136)%Z with (bv_unsigned sp0 - 8388608 + (8388608 - 136))%Z by lia. apply Hst; lia. }
      set (M3 := wbytes M2 (Z_to_bv 64 (bv_unsigned sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x12bd0))).
      assert (SOK2 : store_ok RSEGS M3 (Z_to_bv 64 (bv_unsigned sp0 - 144)) 8 = true).
      { subst M3 M2. apply store_ok_wbytes. apply store_ok_wbytes.
        replace (bv_unsigned sp0 - 144)%Z with (bv_unsigned sp0 - 8388608 + (8388608 - 144))%Z by lia. apply Hst; lia. }
      set (M4 := wbytes M3 (Z_to_bv 64 (bv_unsigned sp0 - 144)) (word_to_le_bytes 8 s0v)).
      assert (SOK3 : store_ok RSEGS M4 (Z_to_bv 64 0x31434) 4 = true) by (apply data_store_ok; lia).
      destruct (walkE (regupd R2 10 (errno_ret EISDIR)) M2 (seg_rom RSEGS) (bv_unsigned sp0) s0v
                  Ra2 Sp2 A02 Tp2 eq_refl ltac:(lia) ltac:(lia) RD2 SOK1 SOK2 SOK3)
        as (R3 & RUN3 & H2 & HK3).
      eapply rz_msteps; [reflexivity | reflexivity | exact RUN3 |]. clear RUN3.
      change (wbytes (wbytes (wbytes M2 (Z_to_bv 64 (bv_unsigned sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x12bd0)))
                             (Z_to_bv 64 (bv_unsigned sp0 - 144)) (word_to_le_bytes 8 s0v))
                     (Z_to_bv 64 0x31434) (word_to_le_bytes 4 (Z_to_bv 64 21))) with
             (wbytes M4 (Z_to_bv 64 0x31434) (word_to_le_bytes 4 (Z_to_bv 64 21))).
      set (M5 := wbytes M4 (Z_to_bv 64 0x31434) (word_to_le_bytes 4 (Z_to_bv 64 21))).
      (* [comment removed for export] *)
      assert (OFF : forall x : word,
                 ~ (bv_unsigned sp0 - 144 <= bv_unsigned x < bv_unsigned sp0 - 128)%Z ->
                 ~ (0x31434 <= bv_unsigned x < 0x31438)%Z -> M5 x = M x).
      { intros x Hx1 Hx2. subst M5 M4 M3 M2.
        rewrite !wbytes_outside; [reflexivity | ..];
          rewrite ?length_N_to_le_bytes; rewrite ?u_small by lia; try lia. }
      replace (Z_to_bv 64 0x12d14) with (0x12d14 : word) by (apply bv_eq; reflexivity).
      replace (0x12d14 : word) with (Z_to_bv 64 0x12d14) by (apply bv_eq; reflexivity).
      apply (TAIL R3 M5 VM cnr).
      destruct W.
      constructor.
      + exact H2.
      + rewrite (HK3 3%bv) by in_lit. rewrite getr_other by discriminate.
        rewrite (GK 3%bv) by in_lit. rewrite (AK 3%bv) by in_lit. exact Rgp.
      + rewrite (HK3 4%bv) by in_lit. exact Tp2.
      + rewrite (HK3 18%bv) by in_lit. rewrite getr_other by discriminate.
        rewrite (GK 18%bv) by in_lit. rewrite (AK 18%bv) by in_lit. exact Rs2.
      + (* [comment removed for export] *)
        intros d m Hd Hm. subst M5 M4 M3 M2. repeat apply store_ok_wbytes. apply Hst; lia.
      + (* [comment removed for export] *)
        apply (img_clear_transport M M5 re_ivs (re_ivs_of_world M w_img)).
        intros lo hi i Hin Hi. apply OFF; rewrite u_small by (cbn in Hin; repeat destruct Hin as [Hin|Hin]; try injection Hin as <- <-; try lia; destruct Hin);
          cbn in Hin; repeat destruct Hin as [Hin|Hin]; try injection Hin as <- <-; try lia; destruct Hin.
      + refine (cell_agree M M5 _ _ _ _ _ _ w_tid); [cbn; lia | lia | intros i Hi; apply OFF; rewrite u_small by lia; cbn in Hi; lia].
      + exact w_tidr.
      + refine (cell_agree M M5 _ _ _ _ _ _ w_self); [cbn; lia | lia | intros i Hi; apply OFF; rewrite u_small by lia; cbn in Hi; lia].
      + refine (cell_agree M M5 _ _ _ _ _ _ w_canary); [cbn; lia | lia | intros i Hi; apply OFF; rewrite u_small by lia; cbn in Hi; lia].
      + refine (cell_agree M M5 _ _ _ _ _ _ w_pagesz); [cbn; lia | lia | intros i Hi; apply OFF; rewrite u_small by lia; cbn in Hi; lia].
      + intros xa Hxa. rewrite OFF; [apply HA; exact Hxa | lia | lia].
  Qed.
End DirMid.
End WithFP2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
