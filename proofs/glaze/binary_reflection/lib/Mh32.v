(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OssFuzzTheorems.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.ExitSim OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.PropExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.CatExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.Hoare OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
From Ltac2 Require Ltac2.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module DrainSim.
(* [comment removed for export] *)

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite.
Import OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.ExitSim OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.PropExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.CatExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.AllocSim.WallSim OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Proc.
Context {A : Type}.
Variable f : A -> byte -> option A.

Fixpoint procs (a : A) (bs : list byte) : option A :=
  match bs with
  | [] => Some a
  | b :: rest => match f a b with Some a' => procs a' rest | None => None end
  end.

End Proc.


(* [comment removed for export] *)
Definition reads_ch (rch : word) (blocks : list (list byte)) : list event :=
  flat_map (fun bs => map (ReadEv rch) bs) blocks.


(* [comment removed for export] *)
Definition reads (blocks : list (list byte)) : list event :=
  reads_ch (Z_to_bv 64 0) blocks.


Section Traces.
Context {A : Type}.
Variable cnt : word.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.














End Traces.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Drain.
Context {A : Type}.
Variable segs : list Segment.
Variable cnt : word.
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.
Hypothesis Hec : (bv_unsigned ec < 256)%Z.
Variable LH : A -> machine_state -> Prop.

(* [comment removed for export] *)
Definition lh_next (a : A) (ms : machine_state) : Prop :=
  exists ms', msteps segs ms ms' /\ LH a ms'.

(* [comment removed for export] *)
Definition WrFin (bs : list byte) (ms : machine_state) : Prop :=
  (1 <= length bs)%nat /\
  to_wall segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)).

(* [comment removed for export] *)
Inductive to_out : list byte -> machine_state -> Prop :=
| tout_exit : forall ms, to_exit segs (Z_to_bv 64 0) ms -> to_out [] ms
| tout_wr : forall bs ms, WrFin bs ms -> to_out bs ms
| tout_step : forall bs ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_out bs ms' -> to_out bs ms.

(* [comment removed for export] *)
Definition ReadPend (a : A) (ms : machine_state) : Prop :=
  exists buf x8,
  ms_svc_pending ms = Some x8 /\
  bv_unsigned x8 = 63%Z /\
  ms_gpr ms 0 = Z_to_bv 64 0 /\
  ms_gpr ms 1 = buf /\
  ms_gpr ms 2 = cnt /\
  (exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt
             = Some w) /\
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true /\
  to_out (out a) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
  (* [comment removed for export] *)
  buf_modeled (out a) /\
  (forall bs,
     (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
     match procs f a bs with
     | Some a' => lh_next a'
         (advance_past_svc (apply_effect ms
            (mkEffect (len_word bs) [(buf, bs)] [])))
     | None => to_exit segs ec
         (advance_past_svc (apply_effect ms
            (mkEffect (len_word bs) [(buf, bs)] [])))
     end).

(* [comment removed for export] *)
Inductive to_rd : A -> machine_state -> Prop :=
| trd_here : forall a ms, ReadPend a ms -> to_rd a ms
| trd_step : forall a ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_rd a ms' -> to_rd a ms.

Lemma msteps_to_rd : forall a ms ms',
  msteps segs ms ms' -> to_rd a ms' -> to_rd a ms.
Proof.
  intros a ms ms' H; induction H; [auto|].
  intro Hrd. eapply trd_step; eauto.
Qed.

Lemma msteps_to_out : forall bs ms ms',
  msteps segs ms ms' -> to_out bs ms' -> to_out bs ms.
Proof.
  intros bs ms ms' H; induction H; [auto|].
  intro Ho. eapply tout_step; eauto.
Qed.


(* [comment removed for export] *)
Variable H_LH : forall a ms, LH a ms -> to_rd a ms.




























End Drain.


End DrainSim.
Require OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.MmapSim LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module StepTac.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.ExitSim OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.PropExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.CatExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.MmapSim OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.AllocSim.WallSim OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim DrainSim.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP1.
Ltac chain_step :=
  first [ eapply mst_step
        | eapply tw_step
        | eapply twm_step
        | eapply MmapSim.twmt_step
        | eapply tmw_step
        | eapply AllocSim.StreamSim.twr_step
        | eapply AllocSim.StreamSim.trd_step
        | eapply AllocSim.WallSim.twt_step
        | eapply AllocSim.WallSim.twe_step
        | eapply DrainSim.tout_step
        | eapply DrainSim.trd_step
        | eapply te_step ].

Section WithFP2.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP2.
Ltac step_intro := chain_step.

Section WithFP3.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP3.
Ltac expand_ctx_defs p :=
  match goal with
  | H := _ |- _ =>
      lazymatch p with
      | context [H] => let p' := eval unfold H in p in expand_ctx_defs p'
      end
  | _ => p
  end.

Section WithFP4.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP4.
Ltac check_closed_term p :=
  let p' := expand_ctx_defs p in
  tryif has_evar p' then
    fail 0 "check_closed_term:" p "contains an evar"
  else tryif match goal with
             | H : _ |- _ => lazymatch p' with context [H] => idtac end
             end
  then fail 0 "check_closed_term:" p "mentions a context variable"
  else idtac.

Section WithFP5.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP5.
Ltac vm_eval t :=
  let _ := match goal with _ => check_closed_term t end in
  eval vm_compute in t.

Section WithFP6.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP6.
Ltac word_lit p :=
  let u := vm_eval (bv_unsigned p) in
  constr:(@BV 64 u ltac:(vm_compute; exact I)).

Section WithFP7.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP7.
Ltac wlit_replace p :=
  let l := word_lit p in
  replace p with l by (apply bv_eq; vm_compute; reflexivity).

Section WithFP8.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP8.
Ltac wlit p :=
  try (lazymatch p with
       | @BV _ _ _ => idtac
       | _ => wlit_replace p
       end).

Section WithFP9.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP9.
Ltac wlits :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_replace (v_addi a b)
  | |- context [btgt ?a ?b] => wlit_replace (btgt a b)
  | |- context [v_jalr ?a ?b] => wlit_replace (v_jalr a b)
  | |- context [v_auipc ?a ?b] => wlit_replace (v_auipc a b)
  end.

Section WithFP10.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP10.
Ltac norm_pc_state st :=
  tryif has_evar st then idtac
  else lazymatch st with
       | mkst _ ?p _ _ => wlit p
       | _ => idtac
       end.
Ltac norm_pc :=
  try lazymatch goal with
  | |- msteps _ ?st _ => norm_pc_state st
  | |- to_wexit _ ?st _ _ => norm_pc_state st
  | |- twm _ ?st _ _ _ => norm_pc_state st
  | |- MmapSim.twm_pend _ ?st _ _ _ _ => norm_pc_state st
  | |- MmapSim.twm_tail _ ?st _ _ _ _ => norm_pc_state st
  | |- tmw _ ?st _ _ _ _ _ => norm_pc_state st
  | |- AllocSim.StreamSim.to_wr _ _ _ ?st => norm_pc_state st
  | |- AllocSim.StreamSim.to_rd _ _ _ ?st => norm_pc_state st
  | |- AllocSim.WallSim.to_wall _ _ ?st _ _ => norm_pc_state st
  | |- AllocSim.WallSim.to_wall_tail _ _ ?st _ _ => norm_pc_state st
  | |- AllocSim.WallSim.to_wallexit _ _ _ _ ?st => norm_pc_state st
  | |- to_exit _ _ ?st => norm_pc_state st
  | |- DrainSim.to_out _ _ ?st => norm_pc_state st
  | |- DrainSim.to_rd _ _ _ _ _ _ _ ?st => norm_pc_state st
  end.

Section WithFP12.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP12.
Ltac reduce_bv_eqb_ifs :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?x else ?y] =>
      lazymatch a with
      | @BV _ _ _ =>
          lazymatch b with
          | @BV _ _ _ =>
              let v := eval vm_compute in (bv_eqb a b) in
              lazymatch v with
              | true => change (if bv_eqb a b then x else y) with x
              | false => change (if bv_eqb a b then x else y) with y
              end
          end
      end
  end.

Section WithFP13.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP13.
Ltac step_simpl := reduce_bv_eqb_ifs; rewrite ?skipn_O; norm_pc.

Section WithFP14.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP14.
Ltac stepi_search F D :=
  first
    [ exact (step_addi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_add _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sub _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_auipc _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_lui _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_addiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_andi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sltiu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_xori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mul _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_ori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_subw _ _ _ _ _ _ _ _ _ F eq_refl D)
    (* [comment removed for export] *)
    | exact (step_slti _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srai _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_and _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_or _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_xor _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sll _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srl _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sra _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slt _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sltu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_addw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sllw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srlw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sraw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sraiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulh _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulhsu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulhu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_div _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_rem _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_divw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_divuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_remw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_remuw _ _ _ _ _ _ _ _ _ F eq_refl D) ].

Section WithFP15.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP15.
Ltac stepi F D :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (OpImm ALU_ADD _ _ _, _) =>
        exact (step_addi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_AND _ _ _, _) =>
        exact (step_andi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_OR _ _ _, _) =>
        exact (step_ori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_XOR _ _ _, _) =>
        exact (step_xori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_SLT _ _ _, _) =>
        exact (step_slti _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_SLTU _ _ _, _) =>
        exact (step_sltiu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_ADD _ _ _, _) =>
        exact (step_add _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SUB _ _ _, _) =>
        exact (step_sub _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_AND _ _ _, _) =>
        exact (step_and _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_OR _ _ _, _) =>
        exact (step_or _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_XOR _ _ _, _) =>
        exact (step_xor _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLL _ _ _, _) =>
        exact (step_sll _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SRL _ _ _, _) =>
        exact (step_srl _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SRA _ _ _, _) =>
        exact (step_sra _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLT _ _ _, _) =>
        exact (step_slt _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLTU _ _ _, _) =>
        exact (step_sltu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_ADD _ _ _, _) =>
        exact (step_addw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SUB _ _ _, _) =>
        exact (step_subw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SLL _ _ _, _) =>
        exact (step_sllw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SRL _ _ _, _) =>
        exact (step_srlw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SRA _ _ _, _) =>
        exact (step_sraw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm32 _ _ _, _) =>
        exact (step_addiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) =>
        exact (step_slli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) =>
        exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SRA _ _ _, _) =>
        exact (step_srai _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SLL _ _ _, _) =>
        exact (step_slliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SRL _ _ _, _) =>
        exact (step_srliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SRA _ _ _, _) =>
        exact (step_sraiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Auipc _ _, _) =>
        exact (step_auipc _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Lui _ _, _) =>
        exact (step_lui _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MUL _ _ _, _) =>
        exact (step_mul _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULH _ _ _, _) =>
        exact (step_mulh _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULHSU _ _ _, _) =>
        exact (step_mulhsu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULHU _ _ _, _) =>
        exact (step_mulhu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_DIV _ _ _, _) =>
        exact (step_div _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_REM _ _ _, _) =>
        exact (step_rem _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_DIVU _ _ _, _) =>
        eapply step_divu;
        [ exact F | reflexivity | exact D | try first [ assumption | lia ] ]
    | decode_any _ = Some (Mul M_REMU _ _ _, _) =>
        eapply step_remu;
        [ exact F | reflexivity | exact D | try first [ assumption | lia ] ]
    | decode_any _ = Some (Mul32 M_MUL _ _ _, _) =>
        exact (step_mulw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_DIV _ _ _, _) =>
        exact (step_divw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_DIVU _ _ _, _) =>
        exact (step_divuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_REM _ _ _, _) =>
        exact (step_remw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_REMU _ _ _, _) =>
        exact (step_remuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | _ => stepi_search F D
    end
  | step_simpl ].

Section WithFP16.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP16.
Ltac stepiv F D vv tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (OpImm ALU_ADD _ _ _, _) =>
        eapply step_addi_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_AND _ _ _, _) =>
        eapply step_andi_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_OR _ _ _, _) =>
        eapply step_ori_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_XOR _ _ _, _) =>
        eapply step_xori_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_SLTU _ _ _, _) =>
        eapply step_sltiu_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) =>
        eapply step_slli_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) =>
        eapply step_srli_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SRA _ _ _, _) =>
        eapply step_srai_at with (v := vv)
    | decode_any _ = Some (Op ALU_ADD _ _ _, _) =>
        eapply step_add_at with (v := vv)
    | decode_any _ = Some (Op ALU_SUB _ _ _, _) =>
        eapply step_sub_at with (v := vv)
    | decode_any _ = Some (OpImm32 _ _ _, _) =>
        eapply step_addiw_at with (v := vv)
    | decode_any _ = Some (Mul M_MUL _ _ _, _) =>
        eapply step_mul_at with (v := vv)
    | decode_any _ = Some (Lui _ _, _) =>
        eapply step_lui_at with (v := vv)
    | decode_any _ = Some (Auipc _ _, _) =>
        eapply step_auipc_at with (v := vv)
    | _ => eapply step_addi_at with (v := vv)
    end;
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section WithFP17.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP17.
Ltac stepiwv F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_addiw_at with (v := vv);
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section WithFP18.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP18.
Ltac stepj F D :=
  chain_step;
  [ reflexivity
  | first [ exact (step_jal_x0 _ _ _ _ _ _ _ F eq_refl D)
          | exact (step_jal_link _ _ _ _ _ _ _ _ F eq_refl D) ]
  | step_simpl ].

Section WithFP19.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP19.
Ltac stepjr F D tv tac :=
  chain_step;
  [ reflexivity
  | first [ eapply step_jalr_x0 with (tgt := tv);
            [ exact F | reflexivity | exact D | tac ]
          | eapply step_jalr_link with (tgt := tv);
            [ exact F | reflexivity | exact D | reflexivity | tac ] ]
  | step_simpl ].

Section WithFP20.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma u_Z2bv : forall z, (0 <= z)%Z -> (z < 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hlo Hhi. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. apply Z.mod_small. split; [exact Hlo|].
  exact Hhi.
Qed.

(* [comment removed for export] *)
Lemma v_addi_m1 : forall x, (1 <= bv_unsigned x)%Z ->
  v_addi x (-1) = Z_to_bv 64 (bv_unsigned x - 1).
Proof. intros x H1. apply (v_addi_m x 1); lia. Qed.

Lemma v_addi_m16 : forall x, (16 <= bv_unsigned x)%Z ->
  v_addi x (-16) = Z_to_bv 64 (bv_unsigned x - 16).
Proof. intros x H16. apply (v_addi_m x 16); lia. Qed.

Lemma v_addi_m32 : forall x, (32 <= bv_unsigned x)%Z ->
  v_addi x (-32) = Z_to_bv 64 (bv_unsigned x - 32).
Proof. intros x H32. apply (v_addi_m x 32); lia. Qed.

Lemma v_addi_m48 : forall x, (48 <= bv_unsigned x)%Z ->
  v_addi x (-48) = Z_to_bv 64 (bv_unsigned x - 48).
Proof. intros x H48. apply (v_addi_m x 48); lia. Qed.

Lemma v_addi_m64 : forall x, (64 <= bv_unsigned x)%Z ->
  v_addi x (-64) = Z_to_bv 64 (bv_unsigned x - 64).
Proof. intros x H64. apply (v_addi_m x 64); lia. Qed.

Lemma v_addi_m80 : forall x, (80 <= bv_unsigned x)%Z ->
  v_addi x (-80) = Z_to_bv 64 (bv_unsigned x - 80).
Proof. intros x H80. apply (v_addi_m x 80); lia. Qed.

(* [comment removed for export] *)
Lemma v_addi_nneg_t : forall x imm, (0 <= imm)%Z ->
  (bv_unsigned x + imm < 2^64)%Z ->
  v_addi x imm = Z_to_bv 64 (bv_unsigned x + imm).
Proof. intros x imm _ _. reflexivity. Qed.

(* [comment removed for export] *)
End WithFP20.
Ltac u_norm := repeat rewrite u_Z2bv by lia.

Section WithFP21.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP21.
Ltac imm_norm :=
  repeat match goal with
  | |- context [bv_signed ?b] =>
      lazymatch b with
      | @BV _ _ _ =>
          let v := eval vm_compute in (bv_signed b) in
          change (bv_signed b) with v
      end
  | |- context [bv_unsigned ?b] =>
      lazymatch b with
      | @BV _ _ _ =>
          let v := eval vm_compute in (bv_unsigned b) in
          change (bv_unsigned b) with v
      end
  end.

Section WithFP22.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP22.
Ltac sp_norm :=
  imm_norm;
  repeat (match goal with
  | |- context [v_addi ?x ?i] =>
      lazymatch x with
      | context [v_addi _ _] => fail
      | _ => first [ rewrite (v_addi_m80 x) by (u_norm; lia)
                   | rewrite (v_addi_m64 x) by (u_norm; lia)
                   | rewrite (v_addi_m48 x) by (u_norm; lia)
                   | rewrite (v_addi_m32 x) by (u_norm; lia)
                   | rewrite (v_addi_m16 x) by (u_norm; lia)
                   | rewrite (v_addi_m1 x) by (u_norm; lia)
                   | rewrite (v_addi_nneg_t x i) by (u_norm; lia) ]
      end
  end; u_norm; cbn [Z.to_N]).

Section WithFP23.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP23.
Ltac stepi_at F D val :=
  chain_step;
  [ reflexivity
  | eapply step_addi_at with (v := val);
    [ exact F | reflexivity | exact D
    | reflexivity
    | getr_resolve; regupd_resolve; reduce_bv_eqb_ifs; sp_norm;
      first [ reflexivity | lia | f_equal; lia
            | apply bv_eq;
              lazymatch goal with |- ?g => check_closed_term g end;
              vm_compute; reflexivity ] ]
  | step_simpl ].

Section WithFP24.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP24.
Ltac bveq :=
  apply bv_eq;
  lazymatch goal with
  | |- ?g =>
      tryif check_closed_term g then
        first
          [ (vm_compute; reflexivity)
          | fail 1 "bveq: vm_compute did not close this closed goal: "
                   "its two sides compute to different values." ]
      else tryif has_evar g then
        fail 1 "bveq: the goal contains an evar — vm_compute must not "
               "see it; instantiate the machine state (eexists / "
               "chain_step) before normalizing."
      else
        (* [comment removed for export] *)
        first
          [ reflexivity
          | fail 1 "bveq: the goal is OPEN (it mentions a context "
                   "variable) and kernel conversion did not close it — "
                   "resolve the register and memory projections first "
                   "(getr_resolve, regupd_resolve) and try again." ]
  end.

Section WithFP25.
Context {fx : FPState}.

(* [comment removed for export] *)
Goal v_addi (Z_to_bv 64 5) 3 = Z_to_bv 64 8.
Proof. bveq. Abort.
Goal forall regs (v : word), getr (regupd regs 11 v) 11 = v.
Proof. intros. assert_fails bveq. getr_resolve. reflexivity. Abort.

(* [comment removed for export] *)
Goal forall v : word, exists w : word, w = v.
Proof.
  intros v. eexists.
  check_closed_term (v_addi (Z_to_bv 64 5) 3).
  assert_fails (check_closed_term (v_addi v 4)).
  lazymatch goal with |- ?g => assert_fails (check_closed_term g) end.
  set (k := Z_to_bv 64 7).
  check_closed_term (v_addi k 1).
  set (k2 := v_addi v 1).
  assert_fails (check_closed_term (v_addi k2 1)).
  let u := vm_eval (bv_unsigned (v_addi (Z_to_bv 64 5) 3)) in
  lazymatch u with 8%Z => idtac end.
  (* [comment removed for export] *)
  try (let u := vm_eval (bv_unsigned (v_addi v 4)) in
       fail 1 "vm_eval accepted an open term").
Abort.

(* [comment removed for export] *)
Goal forall v : word, v_addi v 4 = v_addi v 4.
Proof. intros v. wlit (v_addi v 4). wlits. reflexivity. Abort.
Goal forall v : word,
  (v_addi (Z_to_bv 64 5) 3, v_addi v 4) = (Z_to_bv 64 8, v_addi v 4).
Proof.
  intros v. wlits.
  lazymatch goal with |- (@BV _ _ _, _) = _ => idtac end.
  f_equal. bveq.
Abort.

(* [comment removed for export] *)
End WithFP25.
Ltac stepw_addr :=
  getr_resolve; regupd_resolve; sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].
Ltac stepw_val :=
  getr_resolve; regupd_resolve; cbv beta; reduce_bv_eqb_ifs;
  first [ reflexivity | sp_norm; first [ reflexivity | f_equal; lia ] | bveq ].

(* [comment removed for export] *)
Ltac stepw_addr_hyps :=
  getr_resolve; regupd_resolve;
  repeat match goal with
  | H : Sem.reg_get ?R ?r = _ |- context [Sem.reg_get ?R ?r] => rewrite H
  end;
  imm_norm; rewrite ?v_addi_0;
  sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].

Section WithFP27.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP27.
Ltac stepw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val
        | reflexivity | oktac ]
    end
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepsd F D aexp vexp vtac oktac :=
  step_intro;
  [ reflexivity
  | eapply step_sd_at with (a := aexp) (v := vexp);
    [ exact F | reflexivity | exact D | stepw_addr_hyps | vtac | oktac ]
  | step_simpl ].

Ltac stepld F D aexp vexp readtac :=
  step_intro;
  [ reflexivity
  | eapply step_ld with (bs := word_to_le_bytes 8 vexp) (v := vexp);
    [ exact F | reflexivity | exact D
    | match goal with |- rdn _ _ ?ad _ = _ =>
        replace ad with aexp by stepw_addr_hyps
      end; readtac
    | exact (bytes_le_to_Z_8 _) ]
  | step_simpl ].

Section WithFP28.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP28.
Ltac vm_refl_bv :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section WithFP29.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP29.
Ltac wlit_closed p :=
  check_closed_term p;
  let u := vm_eval (bv_unsigned p) in
  replace p with (Z_to_bv 64 u) by bveq.

Section WithFP30.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP30.
Ltac wlits_closed :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_closed (v_addi a b)
  | |- context [v_add ?a ?b] => wlit_closed (v_add a b)
  | |- context [v_sub ?a ?b] => wlit_closed (v_sub a b)
  end.

Section WithFP32.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP32.
Ltac rdn_ext_lit :=
  erewrite rdn_ext;
    [ (* [comment removed for export] *)
    | imm_norm; u_norm; lia
    | let x := fresh "x" in
      let Hx := fresh "Hx" in
      intros x Hx; revert Hx; imm_norm; u_norm; intros Hx ].

Section WithFP33.
Context {fx : FPState}.







(* [comment removed for export] *)
Lemma word_add_nat : forall (a : word) (n : nat),
  a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp_r.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma word_add_nat_0 : forall x : word, x + nat_to_word 0 = x.
Proof.
  intro x. apply bv_eq. rewrite word_add_nat.
  rewrite u_Z2bv by (pose proof (u64_range x); lia). lia.
Qed.



(* [comment removed for export] *)
Lemma v_add_comm : forall x y : word, v_add x y = y + x.
Proof.
  intros x y. apply bv_eq.
  change (v_add x y) with (x + y).
  rewrite !bv_add_unsigned. f_equal. lia.
Qed.





(* [comment removed for export] *)
Lemma bsb_bound : forall ph (sp : word) (a e : list (list byte)) uid hw rnd,
  valid_argv a -> valid_envp e ->
  (Z.of_nat (length (build_stack_bytes ph sp a e uid hw rnd)) <= 2240000)%Z.
Proof.
  intros ph sp a e uid hw rnd Hva Hve.
  pose proof (build_stack_bytes_within_span ph sp a e uid hw rnd).
  pose proof (entry_stack_span_bound a e Hva Hve).
  unfold entry_stack_span_max in *. lia.
Qed.




(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section DispatchSmoke.
  Variable segs : list Segment.
  Variable regs : bvmap 5 word.
  Variable mem rom : word -> option byte.

  (* [comment removed for export] *)
  Ltac smoke enc sh :=
    let F := fresh "F" in
    intro F;
    let D := fresh "D" in
    assert (D : decode_any enc = Some (sh, 4%Z)) by vm_refl_bv;
    eexists; stepi F D; apply mst_refl.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00152513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00152513 : bv 32) (OpImm ALU_SLT 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40155513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40155513 : bv 32) (ShiftImm ALU_SRA 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B57533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B57533 : bv 32) (Op ALU_AND 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B56533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B56533 : bv 32) (Op ALU_OR 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B54533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B54533 : bv 32) (Op ALU_XOR 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B51533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B51533 : bv 32) (Op ALU_SLL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B55533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B55533 : bv 32) (Op ALU_SRL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40B55533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40B55533 : bv 32) (Op ALU_SRA 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B52533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B52533 : bv 32) (Op ALU_SLT 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B53533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B53533 : bv 32) (Op ALU_SLTU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5053B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5053B : bv 32) (Op32 ALU_ADD 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5153B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5153B : bv 32) (Op32 ALU_SLL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5553B : bv 32) (Op32 ALU_SRL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40B5553B : bv 32) (Op32 ALU_SRA 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015051B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015051B : bv 32) (OpImm32 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015151B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015151B : bv 32) (ShiftImm32 ALU_SLL 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015551B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015551B : bv 32) (ShiftImm32 ALU_SRL 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x4015551B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x4015551B : bv 32) (ShiftImm32 ALU_SRA 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B51533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B51533 : bv 32) (Mul M_MULH 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B52533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B52533 : bv 32) (Mul M_MULHSU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B53533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B53533 : bv 32) (Mul M_MULHU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B54533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B54533 : bv 32) (Mul M_DIV 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B56533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B56533 : bv 32) (Mul M_REM 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5053B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5053B : bv 32) (Mul32 M_MUL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5453B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5453B : bv 32) (Mul32 M_DIV 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5553B : bv 32) (Mul32 M_DIVU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5653B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5653B : bv 32) (Mul32 M_REM 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5753B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5753B : bv 32) (Mul32 M_REMU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B55533 : bv 32) ->
    (bv_unsigned (getr regs 11) <> 0)%Z ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F NZ.
    assert (D : decode_any (0x02B55533 : bv 32)
                = Some (Mul M_DIVU 10 10 11, 4%Z)) by vm_refl_bv.
    eexists. stepi F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B57533 : bv 32) ->
    (bv_unsigned (getr regs 11) <> 0)%Z ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F NZ.
    assert (D : decode_any (0x02B57533 : bv 32)
                = Some (Mul M_REMU 10 10 11, 4%Z)) by vm_refl_bv.
    eexists. stepi F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00151513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x00151513 : bv 32)
                = Some (ShiftImm ALU_SLL 10 10 1, 4%Z)) by vm_refl_bv.
    eexists. stepiv F D (v_slli (getr regs 10) 1) ltac:(reflexivity).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00157513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x00157513 : bv 32)
                = Some (OpImm ALU_AND 10 10 1, 4%Z)) by vm_refl_bv.
    eexists. stepiv F D (v_andi (getr regs 10) 1) ltac:(reflexivity).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A13023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 8%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A13023 : bv 32)
                = Some (Store SZ8 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A12023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 4%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A12023 : bv 32)
                = Some (Store SZ4 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A11023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 2%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A11023 : bv 32)
                = Some (Store SZ2 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A10023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 1%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A10023 : bv 32)
                = Some (Store SZ1 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0080006F : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x0080006F : bv 32)
                = Some (Jal 0 8, 4%Z)) by vm_refl_bv.
    eexists. stepj F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x008000EF : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x008000EF : bv 32)
                = Some (Jal 1 8, 4%Z)) by vm_refl_bv.
    eexists. stepj F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00008067 : bv 32) ->
    getr regs 1 = (0x20000 : word) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F R.
    assert (D : decode_any (0x00008067 : bv 32)
                = Some (Jalr 0 1 0, 4%Z)) by vm_refl_bv.
    eexists. stepjr F D (0x20000 : word) ltac:(exact R).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x000500E7 : bv 32) ->
    getr regs 10 = (0x20000 : word) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F R.
    assert (D : decode_any (0x000500E7 : bv 32)
                = Some (Jalr 1 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepjr F D (0x20000 : word) ltac:(exact R).
    apply mst_refl.
  Abort.

End DispatchSmoke.
End WithFP33.
(* [comment removed for export] *)
Ltac wd_lenlit :=
  repeat match goal with
         | |- context [ @length ?A (word_to_le_bytes ?n ?v) ] => change (@length A (word_to_le_bytes n v)) with n
         | |- context [ @length ?A (@repeat ?B ?b ?n) ] => change (@length A (@repeat B b n)) with n
         end.

(* [comment removed for export] *)
Module WdT20.
Import Ltac2.Ltac2.
Ltac2 rec vars_of (acc : ident list) (c : constr) : ident list :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var id => if List.exist (fun x => Ident.equal x id) acc then acc else id :: acc
  | Constr.Unsafe.App f args => Array.fold_left vars_of (vars_of acc f) args
  | Constr.Unsafe.Prod b t => vars_of (vars_of acc (Constr.Binder.type b)) t
  | Constr.Unsafe.Lambda b t => vars_of (vars_of acc (Constr.Binder.type b)) t
  | Constr.Unsafe.LetIn b v t => vars_of (vars_of (vars_of acc (Constr.Binder.type b)) v) t
  | Constr.Unsafe.Cast c _ t => vars_of (vars_of acc c) t
  | Constr.Unsafe.Case _ _ _ x bl => Array.fold_left vars_of (vars_of acc x) bl
  | Constr.Unsafe.Proj _ _ c => vars_of acc c
  | Constr.Unsafe.Evar _ args => Array.fold_left vars_of acc args
  | Constr.Unsafe.Fix _ _ tys bds => Array.fold_left vars_of (Array.fold_left (fun a b => vars_of a (Constr.Binder.type b)) acc tys) bds
  | _ => acc
  end.
(* [comment removed for export] *)
Ltac2 droppable () : ident list :=
  let hs := List.rev (Control.hyps ()) in
  let keep0 := vars_of [] (Control.goal ()) in
  let rec go (hs : (ident * constr option * constr) list) (keep : ident list) (drop : ident list) :=
    match hs with
    | [] => drop
    | h :: rest =>
        match h with (id, b, t) =>
          if List.exist (fun x => Ident.equal x id) keep then
            let keep := vars_of keep t in
            let keep := match b with Some v => vars_of keep v | None => keep end in
            go rest keep drop
          else go rest keep (id :: drop)
        end
    end in
  go hs keep0 [].
Ltac2 wd_gate := 30.
Ltac2 wd_tauto_goal () :=
  Control.plus (fun () => Control.once (fun () => ltac1:(solve [ repeat (first [ left; reflexivity | right ]) ])))
  (fun _ =>
    let hs := Control.hyps () in
    if Int.lt (List.length hs) wd_gate then ltac1:(intuition fail) else
    Control.plus (fun () => Control.once (fun () =>
        let d := droppable () in
        match d with [] => Control.zero Not_found | _ => Std.clear d end;
        ltac1:(intuition fail)))
      (fun _ => ltac1:(intuition fail))).
End WdT20.
Ltac wd_tauto := idtac; ltac2:(Control.enter WdT20.wd_tauto_goal).
End StepTac.
Module ArgvEnv.
(* [comment removed for export] *)

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.PropExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.CatExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Section Scaffold.

  (* [comment removed for export] *)
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Variable ph : PhdrInfo.

  Variable sp : word.
  Variable av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.

  (* [comment removed for export] *)
  Variable rnd : EntryDraw.

  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma sp_lo_num : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. exact Hsp_lo. Qed.

  Lemma sp_hi_num : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. exact Hsp_hi. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition argcN : word := len_word av.

  Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
  Proof.
    pose proof (valid_argv_len av Hva).
    unfold argcN, len_word. apply u_Z2bv; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma bsb_nw :
    (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z.
  Proof.
    pose proof (bsb_bound ph sp av ev uid hw rnd Hva Hve). pose proof sp_hi_num. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition envp_ptr : word :=
    Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat (length av) + 8).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition wmem : word -> option byte := wrap_mem ph sp av ev uid hw rnd.

  (* [comment removed for export] *)
  Lemma rdn_wmem_stack : forall (a : word) n,
    (bv_unsigned sp <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs wmem a n
    = rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd)) a n.
  Proof. intros a n Ha Hn. unfold wmem. apply rdn_wrap_stack_above; assumption. Qed.

  (* [comment removed for export] *)
  Lemma read_argc_w :
    rdn segs wmem sp 8%nat = Some (word_le8 argcN).
  Proof.
    pose proof sp_hi_num.
    rewrite rdn_wmem_stack by lia.
    apply read_argc. exact bsb_nw.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma argv_ptr_bounds_at : forall k, (k < length av)%nat ->
    (bv_unsigned sp <= bv_unsigned (cat_argv_ptr sp av ev k))%Z /\
    (bv_unsigned (cat_argv_ptr sp av ev k)
       + Z.of_nat (length (nth k av [])) + 1 < 2^64)%Z.
  Proof.
    intros k Hk. apply argv_ptr_bounds; try assumption.
    pose proof sp_hi_num. unfold argv_layout_slack. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma read_argv_ptr_w : forall k, (k < length av)%nat ->
    rdn segs wmem (sp + nat_to_word (8 + 8 * k)) 8%nat
    = Some (word_le8 (cat_argv_ptr sp av ev k)).
  Proof.
    intros k Hk. pose proof sp_lo_num. pose proof sp_hi_num.
    pose proof (valid_argv_len av Hva) as Hal.
    rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
    apply read_argv_ptr_k; [ exact Hk | exact bsb_nw ].
  Qed.

End Scaffold.
End ArgvEnv.
Module LibMaskBits.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.PropExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma testbit_high : forall n a k, 0 <= n -> 0 <= a < 2^n -> n <= k -> Z.testbit a k = false.
Proof. intros. eapply Z_testbit_high; eauto. Qed.

Lemma testbit_pow2 : forall n k, 0 <= n -> 0 <= k -> Z.testbit (2^n) k = (n =? k).
Proof.
  intros n k Hn Hk. rewrite <- (Z.shiftl_1_l n), Z.shiftl_spec by lia.
  destruct (Z.eqb_spec n k) as [->|Hne].
  - rewrite Z.sub_diag. reflexivity.
  - destruct (Z.lt_ge_cases (k - n) 0) as [Hl|Hg].
    + apply Z.testbit_neg_r. lia.
    + rewrite Z.bits_above_log2; [reflexivity | lia |]. apply Z.log2_lt_pow2; [lia|].
      apply Z.lt_le_trans with (2^1)%Z; [simpl; lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Lemma testbit_add_high : forall a m k, 0 <= a < 2^32 -> 0 <= m -> 0 <= k < 32 ->
  Z.testbit (a + 2^32 * m) k = Z.testbit a k.
Proof.
  intros a m k Ha Hm Hk.
  rewrite <- (Z.lxor_spec a (2^32 * m) k) || idtac.
  assert (Hd : Z.land a (2^32 * m) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 32) as [Hl|Hg].
    - replace (2^32 * m) with (Z.shiftl m 32) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite (testbit_high 32 a i) by lia. reflexivity. }
  rewrite (Z.add_nocarry_lxor a (2^32 * m) Hd). rewrite Z.lxor_spec.
  replace (2^32 * m) with (Z.shiftl m 32) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.shiftl_spec_low by lia. apply xorb_false_r.
Qed.

Lemma testbit_add_high2 : forall a m k, 0 <= a < 2^32 -> 0 <= m -> 32 <= k ->
  Z.testbit (a + 2^32 * m) k = Z.testbit m (k - 32).
Proof.
  intros a m k Ha Hm Hk.
  assert (Hd : Z.land a (2^32 * m) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 32) as [Hl|Hg].
    - replace (2^32 * m) with (Z.shiftl m 32) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite (testbit_high 32 a i) by lia. reflexivity. }
  rewrite (Z.add_nocarry_lxor a (2^32 * m) Hd). rewrite Z.lxor_spec.
  rewrite (testbit_high 32 a k) by lia.
  replace (2^32 * m) with (Z.shiftl m 32) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.shiftl_spec_high by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_ones_mod : forall x k, 0 <= x -> 0 <= k -> Z.land x (2^k - 1) = x mod 2^k.
Proof. intros x k Hx Hk. rewrite <- (Z.land_ones x k) by lia. unfold Z.ones. rewrite Z.shiftl_1_l. f_equal; lia. Qed.

(* [comment removed for export] *)
Lemma land_pagemask : forall x, 0 <= x < 2^64 -> Z.land x (2^64 - 4096) = x - x mod 4096.
Proof.
  intros x Hx. apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec.
  assert (Em : 2^64 - 4096 = Z.shiftl (2^52 - 1) 12) by reflexivity. rewrite Em.
  assert (Ex : x - x mod 4096 = Z.shiftl (x / 2^12) 12).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. lia. }
  rewrite Ex.
  destruct (Z.lt_ge_cases k 12) as [Hl|Hg].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia.
    destruct (Z.lt_ge_cases k 64) as [Hl2|Hg2].
    + assert (Ht : Z.testbit (2^52 - 1) (k - 12) = true).
      { replace (2^52 - 1) with (Z.ones 52) by reflexivity. apply Z.ones_spec_low. lia. }
      rewrite Ht, andb_true_r. rewrite Z.div_pow2_bits by lia. f_equal. lia.
    + rewrite (testbit_high 64 x k) by lia.
      rewrite (testbit_high 52 (x / 2^12) (k - 12)); [reflexivity | lia | | lia].
      change (2^12) with 4096. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sc_extract : forall W, 0 <= W < 2^64 ->
  Z.shiftr ((Z.shiftl W 52) mod 2^64) 58 = (W / 64) mod 64.
Proof.
  intros W HW. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace (2^64) with (2^12 * 2^52) by reflexivity.
  rewrite Z.mul_mod_distr_r by lia.
  replace (2^58) with (2^6 * 2^52) by reflexivity.
  rewrite Z.div_mul_cancel_r by lia.
  change (2^12) with 4096. change (2^6) with 64. lia.
Qed.

(* [comment removed for export] *)
Lemma sc2_extract : forall W, 0 <= W -> Z.land (Z.shiftr W 5) 126 = 2 * ((W / 64) mod 64).
Proof.
  intros W HW. rewrite Z.shiftr_div_pow2 by lia.
  apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec.
  replace (2 * ((W / 64) mod 64)) with (Z.shiftl ((W / 2^6) mod 2^6) 1)
    by (rewrite Z.shiftl_mul_pow2 by lia; change (2^6) with 64; lia).
  assert (E126 : 126 = Z.shiftl (Z.ones 6) 1) by reflexivity. rewrite E126.
  destruct (Z.lt_ge_cases k 1) as [Hl|Hg].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia.
    destruct (Z.lt_ge_cases (k - 1) 6) as [Hl6|Hg6].
    + rewrite Z.ones_spec_low, andb_true_r by lia.
      rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.ones_spec_low, andb_true_r by lia.
      rewrite !Z.div_pow2_bits by lia. f_equal. lia.
    + rewrite Z.ones_spec_high, andb_false_r by lia.
      rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.ones_spec_high, andb_false_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma swrap32_cases : forall a, 0 <= a < 2^32 ->
  (a < 2^31 /\ bv_swrap 32 a = a) \/ (2^31 <= a /\ bv_swrap 32 a = a - 2^32).
Proof.
  intros a Ha. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.lt_ge_cases a (2^31)) as [Hl|Hg].
  - left. split; [lia|]. rewrite Z.mod_small by lia. lia.
  - right. split; [lia|]. rewrite <- (Z.mod_unique (a + 2^31) (2^32) 1 (a + 2^31 - 2^32)); lia.
Qed.

Lemma u_lw_lo : forall a, 0 <= a < 2^31 -> bv_unsigned (v_lw (Z_to_bv 64 a)) = a.
Proof.
  intros a Ha. unfold v_lw. rewrite (u_Z2bv a) by lia.
  destruct (swrap32_cases a ltac:(lia)) as [[_ E]|[? _]]; [|lia]. rewrite E. apply u_Z2bv; lia.
Qed.

Lemma u_lw_hi : forall a, 2^31 <= a < 2^32 -> bv_unsigned (v_lw (Z_to_bv 64 a)) = a + 2^32 * (2^32 - 1).
Proof.
  intros a Ha. unfold v_lw. rewrite (u_Z2bv a) by lia.
  destruct (swrap32_cases a ltac:(lia)) as [[? _]|[_ E]]; [lia|]. rewrite E.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite <- (Z.mod_unique (a - 2^32) (2^64) (-1) (a + 2^32 * (2^32 - 1))); lia.
Qed.

Lemma u_sllw1 : forall idx, 0 <= idx <= 31 ->
  bv_unsigned (v_sllw (Z_to_bv 64 1) (Z_to_bv 64 idx)) =
  if idx =? 31 then 2^31 + 2^32 * (2^32 - 1) else 2^idx.
Proof.
  intros idx Hi. unfold v_sllw. rewrite (u_Z2bv 1), (u_Z2bv idx) by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftl_1_l.
  assert (Hp : 0 < 2^idx <= 2^31).
  { split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
  destruct (Z.eqb_spec idx 31) as [->|Hne].
  - destruct (swrap32_cases (2^31) ltac:(simpl; lia)) as [[? _]|[_ E]]; [simpl in *; lia|]. rewrite E.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    rewrite <- (Z.mod_unique (2^31 - 2^32) (2^64) (-1) (2^31 + 2^32 * (2^32 - 1))); lia.
  - assert (2^idx < 2^31) by (apply Z.pow_lt_mono_r; lia).
    destruct (swrap32_cases (2^idx) ltac:(lia)) as [[_ E]|[? _]]; [|lia]. rewrite E. apply u_Z2bv; lia.
Qed.

Lemma land_pow2_testbit : forall a n, 0 <= a -> 0 <= n ->
  Z.land a (2^n) = 0 <-> Z.testbit a n = false.
Proof.
  intros a n Ha Hn. split.
  - intros H. apply (f_equal (fun z => Z.testbit z n)) in H.
    rewrite Z.land_spec, Z.bits_0, testbit_pow2, Z.eqb_refl, andb_true_r in H by lia. exact H.
  - intros H. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0, testbit_pow2 by lia.
    destruct (Z.eqb_spec n k) as [<-|Hne]; [rewrite H; reflexivity | apply andb_false_r].
Qed.

(* [comment removed for export] *)
Lemma mask_test_clear : forall mask idx,
  0 <= mask < 2^32 -> 0 <= idx <= 31 -> Z.testbit mask idx = false ->
  v_and (v_lw (Z_to_bv 64 mask)) (v_sllw (Z_to_bv 64 1) (Z_to_bv 64 idx)) = Z_to_bv 64 0.
Proof.
  intros mask idx Hm Hi Hb. unfold v_and. f_equal.
  rewrite u_sllw1 by lia.
  apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eqb_spec idx 31) as [->|Hne].
  - (* [comment removed for export] *)
    assert (Hlo : mask < 2^31).
    { destruct (Z.lt_ge_cases mask (2^31)) as [|Hge]; [assumption|]. exfalso.
      assert (Ht : Z.testbit mask 31 = true); [|congruence].
      apply Z.testbit_true; [lia|].
      assert (E : mask / 2^31 = 1) by (symmetry; apply Z.div_unique with (r := mask - 2^31); lia). rewrite E. reflexivity. }
    rewrite u_lw_lo by lia.
    destruct (Z.lt_ge_cases k 31) as [Hl|Hg].
    + replace (Z.testbit (2^31 + 2^32 * (2^32 - 1)) k) with false; [apply andb_false_r|].
      symmetry. replace (2^31 + 2^32 * (2^32 - 1)) with (Z.shiftl (2^33 - 1) 31) by reflexivity.
      apply Z.shiftl_spec_low. lia.
    + rewrite (testbit_high 31 mask k) by lia. reflexivity.
  - assert (Hp : 0 < 2^idx < 2^31) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
    rewrite testbit_pow2 by lia.
    destruct (Z.eqb_spec idx k) as [<-|Hnk]; [|apply andb_false_r].
    rewrite andb_true_r.
    destruct (Z.lt_ge_cases mask (2^31)) as [Hlo|Hhi].
    + rewrite u_lw_lo by lia. exact Hb.
    + rewrite u_lw_hi by lia. rewrite testbit_add_high by lia. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_andi_Z : forall x m, 0 <= x < 2^64 -> 0 <= m < 2^64 ->
  v_andi (Z_to_bv 64 x) m = Z_to_bv 64 (Z.land x m).
Proof. intros x m Hx Hm. unfold v_andi. rewrite u_Z2bv by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma v_and_Z : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  v_and (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.land x y).
Proof. intros. unfold v_and. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma v_slli_Z : forall x k, 0 <= x -> 0 <= k -> x * 2^k < 2^64 ->
  v_slli (Z_to_bv 64 x) k = Z_to_bv 64 (x * 2^k).
Proof.
  intros x k Hx Hk Hb. unfold v_slli. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  rewrite u_Z2bv by nia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma v_srli_Z : forall x k, 0 <= x < 2^64 -> 0 <= k ->
  v_srli (Z_to_bv 64 x) k = Z_to_bv 64 (x / 2^k).
Proof. intros x k Hx Hk. unfold v_srli. rewrite u_Z2bv by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma v_mul_Z : forall x y, 0 <= x -> 0 <= y -> x < 2^64 -> y < 2^64 ->
  v_mul (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x * y).
Proof. intros. unfold v_mul. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma v_add_ZZ : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof. intros. unfold v_add. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma v_sub_ZZ : forall x y, 0 <= y <= x -> x < 2^64 ->
  v_sub (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof. intros. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma c_ltu_Z : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  c_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros. unfold c_ltu, bv_ltu. rewrite !u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma Z_to_bv_mod64 : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2^64).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_mod by lia. reflexivity. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End LibMaskBits.
Require LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude LinuxProcessSemantics.Riscv.Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MuslCall.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.
Import OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.ExitSim OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.PropExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.CatExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec StepTac OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.Hoare OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.AllocSim.WallSim.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP1.
Ltac at_fold :=
  repeat match goal with
  | |- context [at_ ?b (?x + ?y)] =>
      let z := eval cbv in (x + y)%Z in change (x + y)%Z with z
  end.

Section WithFP2.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP2.
Ltac gres :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ];
  rewrite ?getr_zero.

Ltac apc := reduce_bv_eqb_ifs; imm_norm; rewrite ?at_addi, ?at_btgt; at_fold.

Section WithFP4.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP4.
Ltac hstepv F D vv tac :=
  eapply mst_step;
  [ reflexivity
  | eapply step_addi_at with (v := vv);
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | apc ].

Section WithFP5.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition Wsp16m : bv 32 := 4278255891.   (* [comment removed for export] *)
Definition Wmv_a3a2 : bv 32 := 394899.
Definition Wli_a6_0 : bv 32 := 2067.
Definition Wmv_a2a1 : bv 32 := 362003.
Definition Wli_a5_0 : bv 32 := 1939.
Definition Wmv_a1a0 : bv 32 := 329107.
Definition Wli_a4_0 : bv 32 := 1811.
Definition Wli_a0_64 : bv 32 := 67110163.
Definition Wsd_ra8 : bv 32 := 1127459.
Definition Wjal_cp : bv 32 := 113246447.   (* [comment removed for export] *)
Definition Wld_ra8 : bv 32 := 8466563.
Definition Wsp16p : bv 32 := 16843027.     (* [comment removed for export] *)
Definition Wj4 : bv 32 := 4194415.         (* [comment removed for export] *)
Definition Wlui_a5 : bv 32 := 4294965175.  (* [comment removed for export] *)
Definition Wbltu : bv 32 := 11002979.      (* [comment removed for export] *)
Definition Wret : bv 32 := 32871.          (* [comment removed for export] *)
Definition Wmv_a7a0 : bv 32 := 329875.
Definition Wmv_a0a1 : bv 32 := 361747.
Definition Wmv_a1a2 : bv 32 := 394643.
Definition Wmv_a2a3 : bv 32 := 427539.
Definition Wmv_a3a4 : bv 32 := 460435.
Definition Wmv_a4a5 : bv 32 := 493331.
Definition Wmv_a5a6 : bv 32 := 526227.
Definition Wecall : bv 32 := 115.
Definition Wj_cpc : bv 32 := 4259311727.


























(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MuslWrite.

Variable segs : list Segment.
Variable B : word.

(* [comment removed for export] *)
Hypothesis F00 : fetch_word segs (at_ B 0x00) = Some Wsp16m.
Hypothesis F04 : fetch_word segs (at_ B 0x04) = Some Wmv_a3a2.
Hypothesis F08 : fetch_word segs (at_ B 0x08) = Some Wli_a6_0.
Hypothesis F0c : fetch_word segs (at_ B 0x0c) = Some Wmv_a2a1.
Hypothesis F10 : fetch_word segs (at_ B 0x10) = Some Wli_a5_0.
Hypothesis F14 : fetch_word segs (at_ B 0x14) = Some Wmv_a1a0.
Hypothesis F18 : fetch_word segs (at_ B 0x18) = Some Wli_a4_0.
Hypothesis F1c : fetch_word segs (at_ B 0x1c) = Some Wli_a0_64.
Hypothesis F20 : fetch_word segs (at_ B 0x20) = Some Wsd_ra8.
Hypothesis F24 : fetch_word segs (at_ B 0x24) = Some Wjal_cp.
Hypothesis F28 : fetch_word segs (at_ B 0x28) = Some Wld_ra8.
Hypothesis F2c : fetch_word segs (at_ B 0x2c) = Some Wsp16p.
Hypothesis F30 : fetch_word segs (at_ B 0x30) = Some Wj4.
Hypothesis F34 : fetch_word segs (at_ B 0x34) = Some Wlui_a5.
Hypothesis F38 : fetch_word segs (at_ B 0x38) = Some Wbltu.
Hypothesis F3c : fetch_word segs (at_ B 0x3c) = Some Wret.
Hypothesis F6c : fetch_word segs (at_ B 0x6c) = Some Wmv_a7a0.
Hypothesis F70 : fetch_word segs (at_ B 0x70) = Some Wmv_a0a1.
Hypothesis F74 : fetch_word segs (at_ B 0x74) = Some Wmv_a1a2.
Hypothesis F78 : fetch_word segs (at_ B 0x78) = Some Wmv_a2a3.
Hypothesis F7c : fetch_word segs (at_ B 0x7c) = Some Wmv_a3a4.
Hypothesis F80 : fetch_word segs (at_ B 0x80) = Some Wmv_a4a5.
Hypothesis F84 : fetch_word segs (at_ B 0x84) = Some Wmv_a5a6.
Hypothesis F88 : fetch_word segs (at_ B 0x88) = Some Wecall.
Hypothesis F8c : fetch_word segs (at_ B 0x8c) = Some Wret.
Hypothesis F90 : fetch_word segs (at_ B 0x90) = Some Wj_cpc.

(* [comment removed for export] *)
Definition musl_clob : regset :=
  fun r => r = 1 \/ r = 2 \/ r = 10 \/ r = 11 \/ r = 12 \/ r = 13
           \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17.

Ltac in_clob :=
  unfold musl_clob;
  repeat first [ left; reflexivity | right ]; reflexivity.









End MuslWrite.
End WithFP5.
End MuslCall.
Module RefLayout.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.PropExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.CatExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec StepTac ArgvEnv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_skipn : forall segs mem n (a : word) bs off k,
  rdn segs mem a n = Some bs -> (off + k <= n)%nat ->
  rdn segs mem (a + nat_to_word off) k = Some (firstn k (skipn off bs)).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs off k H Hk.
  - assert (off = 0%nat) by lia. assert (k = 0%nat) by lia. subst.
    rewrite word_add_0. cbn in H |- *. injection H as <-. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct off as [|off].
    + rewrite word_add_0. cbn [skipn].
      eapply rdn_firstn; [|exact Hk].
      cbn [rdn]. rewrite Eb, Er. reflexivity.
    + cbn [skipn].
      replace (a + nat_to_word (S off)) with (a + 1 + nat_to_word off)
        by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
      apply (IH (a+1) rest off k Er). lia.
Qed.

Lemma firstn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof.
  intros A l1 l2 n H. subst n. rewrite firstn_app, firstn_all, Nat.sub_diag.
  cbn. apply app_nil_r.
Qed.

Lemma skipn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> skipn n (l1 ++ l2) = l2.
Proof.
  intros A l1 l2 n H. subst n. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.




(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cat_envp_ptr (sp : word) (av ev : list (list byte)) (k : nat) : word :=
  nth k (fst (string_addrs (cat_env_base sp av ev) ev)) (Z_to_bv 64 0).

(* [comment removed for export] *)
Definition envp_off (av : list (list byte)) : nat := (8 + 8 * (length av + 1))%nat.
Definition auxv_off (av ev : list (list byte)) : nat :=
  (8 + 8 * (length av + 1) + 8 * (length ev + 1))%nat.

(* [comment removed for export] *)
Definition auxv_words (ph : PhdrInfo) (rnd uid hw : word) : list word :=
  flat_map (fun e => [fst e; snd e]) (auxv_entries ph rnd uid hw).

Lemma build_auxv_words : forall entries,
  build_auxv entries = flat_map word_le8 (flat_map (fun e => [fst e; snd e]) entries).
Proof.
  induction entries as [|[t v] es IH]; [reflexivity|].
  cbn [build_auxv flat_map fst snd app].
  change (build_auxv es) with
    (flat_map (fun e : bv 64 * bv 64 => word_le8 (fst e) ++ word_le8 (snd e)) es) in IH.
  rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma auxv_bytes_words : forall ph rnd uid hw,
  auxv_bytes ph rnd uid hw = flat_map word_le8 (auxv_words ph rnd uid hw).
Proof. intros. unfold auxv_bytes, auxv_words. apply build_auxv_words. Qed.

Lemma length_auxv_words : forall ph rnd uid hw, length (auxv_words ph rnd uid hw) = 20%nat.
Proof. reflexivity. Qed.

Section Layout.

  Variable segs : list Segment.
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.       (* [comment removed for export] *)

  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  Let bsb := build_stack_bytes ph sp av ev uid hw rdraw.
  (* [comment removed for export] *)
  Let stk := stack_to_mem sp (entry_stack_image ph sp av ev uid hw rdraw).

  Lemma lay_bsb_nw : (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z.
  Proof. exact (bsb_nw ph sp av ev uid hw rdraw Hva Hve Hsp_hi). Qed.



  (* [comment removed for export] *)
  Lemma bsb_decomp : exists strs_tail,
    bsb = (word_le8 (len_word av)
           ++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av)))
          ++ word_le8 (Z_to_bv 64 0)
          ++ flat_map word_le8 (fst (string_addrs (cat_env_base sp av ev) ev))
          ++ word_le8 (Z_to_bv 64 0)
          ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw
          ++ strs_tail.
  Proof.
    unfold bsb, build_stack_bytes, cat_env_base, cat_string_base, cat_struct_size.
    rewrite (string_addrs_pair av). cbv beta iota.
    rewrite (string_addrs_pair ev). cbv beta iota.
    eexists. rewrite <- !app_assoc. reflexivity.
  Qed.

  Lemma len_argc_argv :
    length (word_le8 (len_word av)
            ++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av)))
    = (8 + 8 * length av)%nat.
  Proof.
    rewrite length_app, length_n_to_le_8, length_flat_map_le8, length_string_addrs_fst. lia.
  Qed.

  Lemma len_envp_ptrs :
    length (flat_map word_le8 (fst (string_addrs (cat_env_base sp av ev) ev))) = (8 * length ev)%nat.
  Proof. rewrite length_flat_map_le8, length_string_addrs_fst. lia. Qed.

  (* [comment removed for export] *)
  Lemma read_argv_null :
    rdn segs stk (sp + nat_to_word (8 + 8 * length av)) 8%nat = Some (word_le8 (Z_to_bv 64 0)).
  Proof.
    destruct bsb_decomp as [tl E].
    pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw _ (word_le8 (Z_to_bv 64 0)) _ 8%nat E
                  (length_n_to_le_8 _) lay_bsb_nw) as H.
    rewrite len_argc_argv in H. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma read_envp_ptr_k : forall k, (k < length ev)%nat ->
    rdn segs stk (sp + nat_to_word (envp_off av + 8 * k)) 8%nat
    = Some (word_le8 (cat_envp_ptr sp av ev k)).
  Proof.
    intros k Hk.
    destruct bsb_decomp as [tl E].
    assert (Hk' : (k < length (fst (string_addrs (cat_env_base sp av ev) ev)))%nat)
      by (rewrite length_string_addrs_fst; exact Hk).
    rewrite (flat_map_le8_decomp _ k Hk') in E.
    rewrite <- !app_assoc in E.
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?p4 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3 ++ p4) mid rest 8%nat) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_n_to_le_8 _) lay_bsb_nw).
    rewrite !length_app in H.
    rewrite !length_flat_map_le8 in H.
    rewrite length_string_addrs_fst in H.
    rewrite firstn_length_le in H by (rewrite length_string_addrs_fst; lia).
    rewrite !length_n_to_le_8 in H.
    unfold envp_off, cat_envp_ptr.
    replace (8 + 8 * (length av + 1) + 8 * k)%nat with (8 + (8 * length av + (8 + 8 * k)))%nat by lia.
    exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma read_envp_null :
    rdn segs stk (sp + nat_to_word (envp_off av + 8 * length ev)) 8%nat
    = Some (word_le8 (Z_to_bv 64 0)).
  Proof.
    destruct bsb_decomp as [tl E].
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3) mid rest 8%nat) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_n_to_le_8 _) lay_bsb_nw).
    rewrite !length_app in H. rewrite len_envp_ptrs in H.
    rewrite !length_n_to_le_8 in H.
    rewrite length_flat_map_le8, length_string_addrs_fst in H.
    unfold envp_off.
    match type of H with
    | rdn _ _ (sp + nat_to_word ?n) 8 = _ =>
        replace (8 + 8 * (length av + 1) + 8 * length ev)%nat with n by lia
    end.
    exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma read_auxv_all :
    rdn segs stk (sp + nat_to_word (auxv_off av ev)) 160%nat
    = Some (auxv_bytes ph (at_random_ptr sp av ev) uid hw).
  Proof.
    destruct bsb_decomp as [tl E].
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?p4 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3 ++ p4) mid rest 160%nat) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_auxv_bytes _ _ _ _) lay_bsb_nw).
    rewrite !length_app in H. rewrite len_envp_ptrs in H.
    rewrite !length_n_to_le_8 in H.
    rewrite length_flat_map_le8, length_string_addrs_fst in H.
    unfold auxv_off.
    match type of H with
    | rdn _ _ (sp + nat_to_word ?n) _ = _ =>
        replace (8 + 8 * (length av + 1) + 8 * (length ev + 1))%nat with n by lia
    end.
    exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma read_auxv_word : forall j, (j < 20)%nat ->
    rdn segs stk (sp + nat_to_word (auxv_off av ev + 8 * j)) 8%nat
    = Some (word_le8 (nth j (auxv_words ph (at_random_ptr sp av ev) uid hw) (Z_to_bv 64 0))).
  Proof.
    intros j Hj.
    rewrite <- nat_to_word_add_merge.
    rewrite (rdn_skipn segs stk 160 _ _ (8 * j) 8 read_auxv_all) by lia.
    f_equal. rewrite auxv_bytes_words.
    rewrite (flat_map_le8_decomp _ j) by (rewrite length_auxv_words; exact Hj).
    rewrite skipn_app_exact
      by (rewrite length_flat_map_le8, firstn_length_le by (rewrite length_auxv_words; lia); lia).
    apply firstn_app_exact. apply length_n_to_le_8.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bsb_random_split : exists pre,
    bsb = pre ++ at_random_bytes (ed_random rdraw)
    /\ at_random_ptr sp av ev = sp + nat_to_word (length pre)
    /\ (Z.of_nat (length pre) mod 8 = 0)%Z.
  Proof.
    unfold bsb, build_stack_bytes, at_random_ptr.
    rewrite (string_addrs_pair av). cbv beta iota.
    rewrite (string_addrs_pair ev). cbv beta iota zeta.
    match goal with
    | |- exists pre, ?raw ++ repeat ?z ?pd ++ at_random_bytes (ed_random rdraw) = _ /\ _ /\ _ =>
        exists (raw ++ repeat z pd)
    end.
    split; [rewrite <- !app_assoc; reflexivity|].
    rewrite !length_app, !repeat_length, !length_flat_map_le8, !length_string_addrs_fst,
      !length_n_to_le_8, length_auxv_bytes, !length_flatten_strings.
    unfold auxv_size.
    match goal with
    | |- _ /\ (Z.of_nat (?L' + _) mod 8 = 0)%Z => set (L := L')
    end.
    replace (8 + (length av + 1) * 8 + (length ev + 1) * 8 + 160
             + total_arg_bytes_nat av + total_arg_bytes_nat ev)%nat with L by lia.
    assert (Hpd : (0 <= (8 - Z.of_nat L mod 8) mod 8 < 8)%Z) by (apply Z.mod_pos_bound; lia).
    split; [reflexivity|].
    rewrite Nat2Z.inj_add, Z2Nat.id by lia.
    rewrite <- Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r.
    replace (Z.of_nat L mod 8 + (8 - Z.of_nat L mod 8))%Z with 8%Z by lia.
    reflexivity.
  Qed.

  Lemma at_random_off : exists off : nat,
    at_random_ptr sp av ev = sp + nat_to_word off
    /\ (off + 16 = length bsb)%nat
    /\ (Z.of_nat off mod 8 = 0)%Z
    /\ forall j n, (j + n <= 16)%nat ->
         rdn segs stk (at_random_ptr sp av ev + nat_to_word j) n
         = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))).
  Proof.
    destruct bsb_random_split as [pre [E [Hp Hmod]]].
    pose proof (length_at_random_bytes (ed_random rdraw)) as HL.
    exists (length pre). split; [exact Hp|]. split.
    { unfold bsb in E |- *. rewrite E, length_app, HL. reflexivity. }
    split; [exact Hmod|].
    intros j n Hjn. rewrite Hp, nat_to_word_add_merge.
    rewrite <- (firstn_skipn j (at_random_bytes (ed_random rdraw))) in E.
    rewrite app_assoc in E.
    rewrite <- (firstn_skipn n (skipn j (at_random_bytes (ed_random rdraw)))) in E.
    pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (pre ++ firstn j (at_random_bytes (ed_random rdraw)))
                  (firstn n (skipn j (at_random_bytes (ed_random rdraw))))
                  (skipn n (skipn j (at_random_bytes (ed_random rdraw)))) n E) as H.
    assert (Hlen : length (pre ++ firstn j (at_random_bytes (ed_random rdraw))) = (length pre + j)%nat).
    { rewrite length_app, firstn_length_le by lia. reflexivity. }
    rewrite Hlen in H.
    apply H; [rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia] | exact lay_bsb_nw].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma lay_bsb_len : (Z.of_nat (length bsb) <= 2240000)%Z.
  Proof. exact (bsb_bound ph sp av ev uid hw rdraw Hva Hve). Qed.

  Lemma auxv_off_bound : (auxv_off av ev + 160 + 16 <= length bsb)%nat.
  Proof.
    unfold bsb, build_stack_bytes. cbv zeta.
    rewrite (string_addrs_pair av). cbv beta iota.
    rewrite (string_addrs_pair ev). cbv beta iota.
    rewrite !length_app, length_at_random_bytes, !repeat_length, !length_flat_map_le8,
      !length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
      !length_flatten_strings.
    unfold auxv_size, auxv_off. lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma cat_envp_ptr_eq : forall k, (k < length ev)%nat ->
    cat_envp_ptr sp av ev k
    = sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat av
                        + total_arg_bytes_nat (firstn k ev)).
  Proof.
    intros k Hk. unfold cat_envp_ptr. rewrite nth_string_addrs by exact Hk.
    unfold cat_env_base, cat_string_base. rewrite !nat_to_word_add_merge.
    rewrite Nat.add_assoc. reflexivity.
  Qed.

  Lemma total_firstn_ev_bound : forall k,
    (Z.of_nat (total_arg_bytes_nat (firstn k ev)) <= 131072)%Z.
  Proof.
    intros k. destruct Hve as [_ [Htot _]]. rewrite total_arg_bytes_Z in Htot.
    pose proof (total_arg_bytes_firstn_le k ev). lia.
  Qed.

  Lemma struct_av_bound :
    (Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat av) <= 2107576)%Z.
  Proof.
    destruct Hva as [[Hl0 Hl] [Hta _]]. destruct Hve as [Hle _].
    rewrite total_arg_bytes_Z in Hta. unfold cat_struct_size, auxv_size. lia.
  Qed.

  Lemma u_cat_envp_ptr : forall k, (k < length ev)%nat ->
    bv_unsigned (cat_envp_ptr sp av ev k)
    = (bv_unsigned sp + Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat av
                                 + total_arg_bytes_nat (firstn k ev)))%Z.
  Proof.
    intros k Hk. rewrite cat_envp_ptr_eq by exact Hk. rewrite word_add_nat.
    pose proof struct_av_bound. pose proof (total_firstn_ev_bound k).
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    apply u_Z2bv; lia.
  Qed.

  Lemma cat_envp_ptr_nz : forall k, (k < length ev)%nat ->
    bv_unsigned (cat_envp_ptr sp av ev k) <> 0%Z.
  Proof.
    intros k Hk. rewrite u_cat_envp_ptr by exact Hk. unfold sp_window_lo in Hsp_lo. lia.
  Qed.

  Lemma u_cat_argv_ptr : forall k, (k < length av)%nat ->
    bv_unsigned (cat_argv_ptr sp av ev k)
    = (bv_unsigned sp + Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat (firstn k av)))%Z.
  Proof.
    intros k Hk. rewrite cat_argv_ptr_offset by exact Hk. unfold cat_string_base.
    rewrite nat_to_word_add_merge, word_add_nat.
    pose proof struct_av_bound. pose proof (total_arg_bytes_firstn_le k av).
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    apply u_Z2bv; lia.
  Qed.


  (* [comment removed for export] *)
  Lemma auxv_words_eq : forall rnd,
    auxv_words ph rnd uid hw =
    [AT_PHDR; Z_to_bv 64 (Z.of_N (ph_addr ph)); AT_PHENT; Z_to_bv 64 (Z.of_N (ph_ent ph));
     AT_PHNUM; Z_to_bv 64 (Z.of_N (ph_num ph)); AT_HWCAP; hw; AT_PAGESZ; Z_to_bv 64 4096;
     AT_UID; uid; AT_EUID; uid; AT_SECURE; Z_to_bv 64 0;
     AT_RANDOM; rnd; AT_NULL; Z_to_bv 64 0].
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rnd_facts : forall (Hal : (bv_unsigned sp mod 16 = 0)%Z),
    (bv_unsigned sp <= bv_unsigned (at_random_ptr sp av ev))%Z
    /\ (bv_unsigned (at_random_ptr sp av ev) + 16 <= bv_unsigned sp + Z.of_nat (length bsb))%Z
    /\ (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z
    /\ (bv_unsigned (at_random_ptr sp av ev) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn segs stk (Z_to_bv 64 (bv_unsigned (at_random_ptr sp av ev) + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
  Proof.
    intros Hal.
    destruct at_random_off as [off [Hp [Hlen [Hmod Hrd]]]].
    pose proof lay_bsb_nw as Hnw. pose proof lay_bsb_len as Hbl.
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    assert (Hu : bv_unsigned (at_random_ptr sp av ev) = (bv_unsigned sp + Z.of_nat off)%Z).
    { rewrite Hp, word_add_nat. apply u_Z2bv; lia. }
    rewrite Hu. split; [lia|]. split; [lia|]. split; [lia|]. split.
    - rewrite Z.add_mod by lia.
      replace (bv_unsigned sp mod 8)%Z with 0%Z.
      2:{ symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
      rewrite Hmod. reflexivity.
    - intros j n Hjn. rewrite <- Hu. rewrite <- word_add_nat. apply Hrd. exact Hjn.
  Qed.

End Layout.
End RefLayout.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
Require OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.PropExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.Hoare. Import OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.PropExec OssFuzzTheorems.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec StepTac LibMaskBits.
From OssFuzzTheorems.Proofs.glaze.binary_reflection.lib Require Import PuLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= lia_nd.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition s32 (a : Z) : word := Z_to_bv 64 (bv_swrap 32 a).

(* [comment removed for export] *)
Definition sx32 (a : Z) : Z := a mod 2 ^ 32 + (if Z.testbit a 31 then 2 ^ 64 - 2 ^ 32 else 0).

Lemma pow2_32 : 2 ^ 32 = 4294967296. Proof. reflexivity. Qed.



Lemma testbit_31_mod : forall a, Z.testbit a 31 = (2 ^ 31 <=? a mod 2 ^ 32).
Proof.
  intros a. rewrite <- (Z.mod_pow2_bits_low a 32 31) by lia.
  pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)) as Hr. set (r := a mod 2 ^ 32) in *. clearbody r.
  destruct (Z.leb_spec (2^31) r) as [H|H].
  - apply Z.testbit_true; [lia|].
    replace (r / 2 ^ 31) with 1 by (apply Z.div_unique with (r := r - 2^31); lia). reflexivity.
  - apply Z.testbit_false; [lia|]. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma swrap32_eq : forall a, bv_swrap 32 a = a mod 2 ^ 32 - (if Z.testbit a 31 then 2 ^ 32 else 0).
Proof.
  intros a. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite testbit_31_mod.
  pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)) as Hr.
  replace ((a + 2 ^ 31) mod 2 ^ 32) with ((a mod 2 ^ 32 + 2 ^ 31) mod 2 ^ 32)
    by (rewrite Z.add_mod_idemp_l by lia; reflexivity).
  set (r := a mod 2 ^ 32) in *.
  destruct (Z.leb_spec (2^31) r) as [H|H].
  - rewrite <- (Z.mod_unique (r + 2^31) (2^32) 1 (r + 2^31 - 2^32)) by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

Lemma u_s32 : forall a, bv_unsigned (s32 a) = sx32 a.
Proof.
  intros a. unfold s32, sx32. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite swrap32_eq. pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)).
  destruct (Z.testbit a 31).
  - rewrite <- (Z.mod_unique (a mod 2^32 - 2^32) (2^64) (-1) (a mod 2^32 + (2^64 - 2^32))); lia.
  - rewrite Z.add_0_r, Z.sub_0_r. apply Z.mod_small. lia.
Qed.

Lemma sx32_range : forall a, 0 <= sx32 a < 2 ^ 64.
Proof. intros a. unfold sx32. pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)). destruct (Z.testbit a 31); lia. Qed.

Lemma sx32_mod : forall a, sx32 a mod 2 ^ 32 = a mod 2 ^ 32.
Proof.
  intros a. unfold sx32. pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)).
  destruct (Z.testbit a 31).
  - replace (2^64 - 2^32) with ((2^32 - 1) * 2^32) by lia. rewrite Z_mod_plus_full. apply Z.mod_mod. lia.
  - rewrite Z.add_0_r. apply Z.mod_mod. lia.
Qed.

Lemma testbit_sx32 : forall a k, 0 <= k ->
  Z.testbit (sx32 a) k = if k <? 32 then Z.testbit a k else if k <? 64 then Z.testbit a 31 else false.
Proof.
  intros a k Hk. unfold sx32. pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)) as Hr.
  destruct (Z.testbit a 31) eqn:B.
  - replace (2 ^ 64 - 2 ^ 32) with (2 ^ 32 * (2 ^ 32 - 1)) by lia.
    destruct (Z.ltb_spec k 32) as [H|H].
    + rewrite testbit_add_high by lia. apply Z.mod_pow2_bits_low. lia.
    + rewrite testbit_add_high2 by lia.
      destruct (Z.ltb_spec k 64) as [H2|H2].
      * replace (2^32 - 1) with (Z.ones 32) by reflexivity. rewrite Z.ones_spec_low by lia. reflexivity.
      * replace (2^32 - 1) with (Z.ones 32) by reflexivity. rewrite Z.ones_spec_high by lia. reflexivity.
  - rewrite Z.add_0_r. destruct (Z.ltb_spec k 32) as [H|H].
    + apply Z.mod_pow2_bits_low. lia.
    + rewrite Z.mod_pow2_bits_high by lia. destruct (Z.ltb_spec k 64); [|reflexivity]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sx32_inj : forall a b, sx32 a = sx32 b -> a mod 2 ^ 32 = b mod 2 ^ 32.
Proof. intros a b H. rewrite <- (sx32_mod a), <- (sx32_mod b), H. reflexivity. Qed.

Lemma s32_mod : forall a, s32 a = s32 (a mod 2 ^ 32).
Proof.
  intros a. apply bv_eq. rewrite !u_s32. unfold sx32. rewrite Z.mod_mod by lia.
  rewrite <- (Z.mod_pow2_bits_low a 32 31) by lia. reflexivity.
Qed.

Lemma s32_eq_iff : forall a b, s32 a = s32 b <-> a mod 2 ^ 32 = b mod 2 ^ 32.
Proof.
  intros a b. split.
  - intros H. apply sx32_inj. rewrite <- !u_s32. rewrite H. reflexivity.
  - intros H. rewrite (s32_mod a), (s32_mod b), H. reflexivity.
Qed.

Lemma s32_small : forall a, 0 <= a < 2 ^ 31 -> s32 a = Z_to_bv 64 a.
Proof.
  intros a Ha. apply bv_eq. rewrite u_s32. unfold sx32.
  rewrite (testbit_high 31 a 31) by lia. rewrite Z.mod_small by lia. rewrite u_Z2bv by lia. lia.
Qed.

Lemma s32_zero_iff : forall a, s32 a = Z_to_bv 64 0 <-> a mod 2 ^ 32 = 0.
Proof.
  intros a. rewrite <- (s32_small 0) by lia. rewrite s32_eq_iff. rewrite Z.mod_0_l by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_lw_s32 : forall a, 0 <= a < 2 ^ 64 -> v_lw (Z_to_bv 64 a) = s32 a.
Proof. intros a Ha. unfold v_lw, s32. rewrite u_Z2bv by lia. reflexivity. Qed.



Lemma v_addw_s32 : forall a b, v_addw (s32 a) (s32 b) = s32 (a + b).
Proof.
  intros a b. unfold v_addw. fold (s32 (bv_unsigned (s32 a) + bv_unsigned (s32 b))).
  apply s32_eq_iff. rewrite !u_s32. rewrite Z.add_mod, !sx32_mod, <- Z.add_mod by lia. reflexivity.
Qed.

Lemma v_addiw_s32 : forall a i, v_addiw (s32 a) i = s32 (a + i).
Proof.
  intros a i. unfold v_addiw. fold (s32 (bv_unsigned (s32 a) + i)).
  apply s32_eq_iff. rewrite u_s32. rewrite Z.add_mod, sx32_mod, <- Z.add_mod by lia. reflexivity.
Qed.


Lemma v_addiw_Z_s32 : forall a i, 0 <= a < 2 ^ 64 -> v_addiw (Z_to_bv 64 a) i = s32 (a + i).
Proof. intros a i Ha. unfold v_addiw, s32. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma v_sllw_Z_s32 : forall c k, 0 <= c < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
  v_sllw (Z_to_bv 64 c) (Z_to_bv 64 k) = s32 (c * 2 ^ (k mod 32)).
Proof.
  intros c k Hc Hk. unfold v_sllw, s32. rewrite !u_Z2bv by lia.
  rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia). reflexivity.
Qed.


(* [comment removed for export] *)
Lemma v_or_s32 : forall a b, v_or (s32 a) (s32 b) = s32 (Z.lor a b).
Proof.
  intros a b. unfold v_or. apply bv_eq. rewrite !u_s32.
  pose proof (sx32_range a). pose proof (sx32_range b). pose proof (sx32_range (Z.lor a b)).
  assert (E : Z.lor (sx32 a) (sx32 b) = sx32 (Z.lor a b)).
  { apply Z.bits_inj'. intros k Hk. rewrite Z.lor_spec, !testbit_sx32 by lia.
    destruct (k <? 32); [apply eq_sym, Z.lor_spec|]. destruct (k <? 64); [apply eq_sym, Z.lor_spec|reflexivity]. }
  rewrite E. pose proof (sx32_range (Z.lor a b)). rewrite u_Z2bv by lia. reflexivity.
Qed.

Lemma v_and_s32 : forall a b, v_and (s32 a) (s32 b) = s32 (Z.land a b).
Proof.
  intros a b. unfold v_and. apply bv_eq. rewrite !u_s32.
  assert (E : Z.land (sx32 a) (sx32 b) = sx32 (Z.land a b)).
  { apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, !testbit_sx32 by lia.
    destruct (k <? 32); [apply eq_sym, Z.land_spec|]. destruct (k <? 64); [apply eq_sym, Z.land_spec|reflexivity]. }
  rewrite E. pose proof (sx32_range (Z.land a b)). rewrite u_Z2bv by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma c_eq_s32 : forall a b, c_eq (s32 a) (s32 b) = (a mod 2 ^ 32 =? b mod 2 ^ 32).
Proof.
  intros a b. unfold c_eq.
  destruct (Z.eqb_spec (a mod 2^32) (b mod 2^32)) as [E|E].
  - apply (proj2 (s32_eq_iff a b)) in E. rewrite E. apply bv_eqb_refl.
  - apply bv_eqb_neq. intros Q. apply E. apply s32_eq_iff. exact Q.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_mod : forall n x y,
  x mod 2 ^ (8 * Z.of_nat n) = y mod 2 ^ (8 * Z.of_nat n) -> Z_to_le_bytes n x = Z_to_le_bytes n y.
Proof.
  induction n as [|n IH]; intros x y H; [reflexivity|].
  cbn [Z_to_le_bytes].
  set (N := 2 ^ (8 * Z.of_nat n)) in *.
  assert (HN : 0 < N) by (subst N; apply Z.pow_pos_nonneg; lia).
  assert (HN' : 2 ^ (8 * Z.of_nat (S n)) = 256 * N).
  { subst N. replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  rewrite HN' in H.
  assert (Hd : (256 * N | x - y)).
  { apply Z.mod_divide; [lia|]. rewrite Zminus_mod, H, Z.sub_diag. apply Z.mod_0_l. lia. }
  destruct Hd as [k Hk].
  assert (Hxy : x = y + k * (256 * N)) by lia. clear Hk.
  f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Hxy. replace (y + k * (256 * N)) with (y + (k * N) * 256) by lia. apply Z_mod_plus_full.
  - apply IH. fold N. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    rewrite Hxy. replace (y + k * (256 * N)) with (y + 256 * (k * N)) by lia.
    rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia.
    rewrite Z.add_comm, Z_mod_plus_full. reflexivity.
Qed.

Lemma w2le4_s32 : forall a, word_to_le_bytes 4 (s32 a) = word_to_le_bytes 4 (Z_to_bv 64 (a mod 2 ^ 32)).
Proof.
  intros a. unfold word_to_le_bytes. apply Z_to_le_bytes_mod. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  change (8 * 4) with 32. rewrite u_s32, sx32_mod.
  pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)). rewrite u_Z2bv by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma Z_lor_range32 : forall a b : Z, 0 <= a < 2^32 -> 0 <= b < 2^32 -> 0 <= Z.lor a b < 2^32.
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia| apply Z.lor_nonneg; lia |].
  intros k Hk. rewrite Z.lor_spec.
  rewrite (Z_testbit_high 32 a k) by lia.
  rewrite (Z_testbit_high 32 b k) by lia.
  reflexivity.
Qed.

Lemma Z_lxor_range32 : forall a b : Z, 0 <= a < 2^32 -> 0 <= b < 2^32 -> 0 <= Z.lxor a b < 2^32.
Proof.
  intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia| apply Z.lxor_nonneg; lia |].
  intros k Hk. rewrite Z.lxor_spec.
  rewrite (Z_testbit_high 32 a k) by lia.
  rewrite (Z_testbit_high 32 b k) by lia.
  reflexivity.
Qed.

Lemma add_pow2_nocarry32 : forall m i, 0 <= m < 2^32 -> 0 <= i < 32 -> Z.testbit m i = false -> m + 2^i < 2^32.
Proof.
  intros m i Hm Hi Hb.
  assert (Hl : Z.land m (2^i) = 0) by (apply (proj2 (land_pow2_testbit m i ltac:(lia) ltac:(lia))); exact Hb).
  rewrite (Z.add_nocarry_lxor m (2^i) Hl).
  assert (Hp : 0 < 2^i < 2^32) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
  pose proof (Z_lxor_range32 m (2^i)) as R. apply R; lia.
Qed.

(* [comment removed for export] *)
Lemma land_32_freeable : forall W, 0 <= W -> Z.land W 32 = 32 * ((W / 32) mod 2).
Proof.
  intros W HW.
  pose proof (Z.testbit_spec' W 5 ltac:(lia)) as Hb. change (2 ^ 5) with 32 in Hb. rewrite <- Hb.
  apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec. change 32 with (2 ^ 5) at 1. rewrite testbit_pow2 by lia.
  destruct (Z.testbit W 5) eqn:B; cbn [Z.b2z].
  - change (32 * 1) with (2 ^ 5). rewrite testbit_pow2 by lia.
    destruct (Z.eqb_spec 5 k) as [<-|Hne]; [rewrite B; reflexivity | apply Bool.andb_false_r].
  - change (32 * 0) with 0. rewrite Z.bits_0.
    destruct (Z.eqb_spec 5 k) as [<-|Hne]; [rewrite B; reflexivity | apply Bool.andb_false_r].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
