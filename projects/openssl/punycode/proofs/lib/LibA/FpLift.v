(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition mkstF (regs F : bvmap 5 word) (fc : bv 32) (pc : word) (mem rom : word -> option byte) : machine_state :=
  {| ms_regs := regs; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := None; ms_resv := None; ms_fcsr := fc;
     ms_mem := mem; ms_rom := rom |}.

Lemma mkst_mkstF : forall regs pc M rom, mkst regs pc M rom = mkstF regs bvmap_empty (Z_to_bv 32 0) pc M rom.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition int_instr (i : instr) : bool :=
  match i with
  | Lui _ _ | Auipc _ _ | Jal _ _ | Jalr _ _ _ | Branch _ _ _ _ | Load _ _ _ _ _ | Store _ _ _ _ | OpImm _ _ _ _
  | ShiftImm _ _ _ _ | Op _ _ _ _ | OpImm32 _ _ _ | ShiftImm32 _ _ _ _ | Op32 _ _ _ _ | Fence _ _ _ _ _ | Mul _ _ _ _
  | Mul32 _ _ _ _ => true
  | _ => false
  end.

(* [comment removed for export] *)
Definition refp (F : bvmap 5 word) (fc : bv 32) (c : core) : core :=
  Core (c_regs c) F (c_pc c) fc (c_resv c).

Definition rmap (F : bvmap 5 word) (fc : bv 32) (r : machine_result (access_report (core * (word -> option byte))))
  : machine_result (access_report (core * (word -> option byte))) :=
  match r with
  | MachineOk rep => MachineOk (@mkAccessReport _ (refp F fc (fst (access_value _ rep)), snd (access_value _ rep))
                                               (accessed_ranges _ rep))
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.

Section Lift.
Variable segs : list Segment.

Lemma refp_rset : forall F fc rd v c, refp F fc (rset rd v c) = rset rd v (refp F fc c).
Proof. intros F fc rd v c. unfold rset. destruct (is_x0 rd); reflexivity. Qed.

(* [comment removed for export] *)
Lemma lift_done : forall F fc c (M : word -> option byte) c',
  c' = refp F fc c ->
  interp_eff_accesses segs (EDone c') M = rmap F fc (interp_eff_accesses segs (EDone c) M).
Proof. intros F fc c M c' ->. reflexivity. Qed.

Lemma lift_load : forall F fc n a (k k' : bv n -> eff) (M : word -> option byte),
  (forall v, interp_eff_accesses segs (k' v) M = rmap F fc (interp_eff_accesses segs (k v) M)) ->
  interp_eff_accesses segs (ELoad n a k') M = rmap F fc (interp_eff_accesses segs (ELoad n a k) M).
Proof.
  intros F fc n a k k' M H. cbn [interp_eff_accesses].
  destruct (ov_read_bytes segs M a (width_bytes n)) as [bs|]; [|reflexivity].
  rewrite H. destruct (interp_eff_accesses segs (k _) M) as [rep| |]; reflexivity.
Qed.

Lemma lift_store : forall F fc n a (v : bv n) (k k' : eff) (M : word -> option byte),
  (forall M1, interp_eff_accesses segs k' M1 = rmap F fc (interp_eff_accesses segs k M1)) ->
  interp_eff_accesses segs (EStore n a v k') M = rmap F fc (interp_eff_accesses segs (EStore n a v k) M).
Proof.
  intros F fc n a v k k' M H. cbn [interp_eff_accesses].
  destruct (store_ok segs M a (width_bytes n)); [|reflexivity].
  rewrite H. destruct (interp_eff_accesses segs k _) as [rep| |]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exec_int_frame : forall sz i R pc (M : word -> option byte) F fc F0 fc0, int_instr i = true ->
  interp_eff_accesses segs (exec sz i (Core R F pc fc None)) M
  = rmap F fc (interp_eff_accesses segs (exec sz i (Core R F0 pc fc0 None)) M).
Proof.
  intros sz i R pc M F fc F0 fc0 Hi.
  destruct i; try discriminate Hi; cbn [exec c_pc].
  - apply lift_done. rewrite refp_rset. reflexivity.
  - apply lift_done. rewrite refp_rset. reflexivity.
  - apply lift_done. rewrite refp_rset. reflexivity.
  - apply lift_done. rewrite refp_rset. reflexivity.
  - apply lift_done. reflexivity.
  - unfold load_val. destruct sz0; apply lift_load; intros v; apply lift_done; rewrite refp_rset; reflexivity.
  - unfold store_val. destruct sz0; apply lift_store; intros M1; apply lift_done; reflexivity.
  - apply lift_done. rewrite refp_rset. reflexivity.
  - apply lift_done. rewrite refp_rset. reflexivity.
  - apply lift_done. rewrite refp_rset. reflexivity.
  - apply lift_done. rewrite refp_rset. reflexivity.
  - apply lift_done. rewrite refp_rset. reflexivity.
  - apply lift_done. rewrite refp_rset. reflexivity.
  - apply lift_done. reflexivity.
  - apply lift_done. rewrite refp_rset. reflexivity.
  - apply lift_done. rewrite refp_rset. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepF_unfold : forall regs F fc pc (M rom : word -> option byte) w i sz,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (i, sz) ->
  RiscvSemantics.step segs (mkstF regs F fc pc M rom) =
  match interp_eff_accesses segs (exec (Z_to_bv 64 sz) i (Core regs F pc fc None)) M with
  | MachineOk rep =>
      MachineOk {| ms_regs := c_regs (fst (access_value _ rep)); ms_fregs := c_fregs (fst (access_value _ rep));
                   ms_pc_val := c_pc (fst (access_value _ rep)); ms_svc_pending := None;
                   ms_resv := c_resv (fst (access_value _ rep)); ms_fcsr := c_fcsr (fst (access_value _ rep));
                   ms_mem := snd (access_value _ rep); ms_rom := rom |}
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.
Proof.
  intros regs F fc pc M rom w i sz Hf He Hd.
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkstF]. rewrite Hf.
  unfold drop_access_report, decode_exec_accesses. rewrite He, Hd.
  cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom mkstF].
  destruct (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i _) M) as [[[c m'] rs]| |]; reflexivity.
Qed.

(* [comment removed for export] *)
Theorem step_lift : forall regs pc (M rom : word -> option byte) w i sz regs' pc' M' F fc,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (i, sz) -> int_instr i = true ->
  RiscvSemantics.step segs (mkst regs pc M rom) = MachineOk (mkst regs' pc' M' rom) ->
  RiscvSemantics.step segs (mkstF regs F fc pc M rom) = MachineOk (mkstF regs' F fc pc' M' rom).
Proof.
  intros regs pc M rom w i sz regs' pc' M' F fc Hf He Hd Hi Hst.
  rewrite mkst_mkstF in Hst. rewrite (stepF_unfold _ _ _ _ _ _ w i sz Hf He Hd) in Hst.
  rewrite (stepF_unfold _ _ _ _ _ _ w i sz Hf He Hd).
  rewrite (exec_int_frame _ i regs pc M F fc bvmap_empty (Z_to_bv 32 0) Hi).
  destruct (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i (Core regs bvmap_empty pc (Z_to_bv 32 0) None)) M)
    as [[[c m'] rs]| |]; [| discriminate Hst | discriminate Hst].
  cbn [rmap access_value accessed_ranges fst snd refp c_regs c_fregs c_pc c_fcsr c_resv] in *.
  unfold mkst, mkstF in *. injection Hst as E1 E2 E3 E4 E5 E6. subst. rewrite E4. reflexivity.
Qed.

End Lift.
