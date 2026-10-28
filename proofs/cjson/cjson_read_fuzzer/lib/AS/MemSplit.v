(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
Module Footprint.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record region : Type := Rg { rg_lo : Z; rg_hi : Z }.

Definition rg_wf (r : region) : Prop :=
  0 <= rg_lo r /\ rg_lo r <= rg_hi r /\ rg_hi r <= 2 ^ 64.

(* [comment removed for export] *)
Definition covers (r : region) (a : word) (n : nat) : Prop :=
  rg_lo r <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= rg_hi r.

Definition rg_disj (r1 r2 : region) : Prop :=
  rg_hi r1 <= rg_lo r2 \/ rg_hi r2 <= rg_lo r1.

Lemma rg_disj_sym : forall r1 r2, rg_disj r1 r2 -> rg_disj r2 r1.
Proof. intros r1 r2 [H|H]; [right|left]; exact H. Qed.

(* [comment removed for export] *)
Lemma covers_mono : forall r r' a n,
  covers r a n -> rg_lo r' <= rg_lo r -> rg_hi r <= rg_hi r' -> covers r' a n.
Proof. intros r r' a n [H1 H2] Hl Hh. split; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma covers_nowrap : forall r a n,
  rg_wf r -> covers r a n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64.
Proof. intros r a n (_ & _ & Hhi) (_ & H). lia. Qed.

(* [comment removed for export] *)
Lemma covers_disj : forall r1 r2 a1 n1 a2 n2,
  rg_disj r1 r2 -> covers r1 a1 n1 -> covers r2 a2 n2 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1.
Proof. intros r1 r2 a1 n1 a2 n2 [H|H] [H1 H2] [H3 H4]; [left|right]; lia. Qed.

(* [comment removed for export] *)
Lemma covers_same_disj : forall r a1 n1 a2 n2,
  covers r a1 n1 -> covers r a2 n2 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1.
Proof. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stack_rg (sp : word) (below above : Z) : region :=
  Rg (bv_unsigned sp - below) (bv_unsigned sp + above).

(* [comment removed for export] *)
Definition seg_rg (lo hi : Z) : region := Rg lo hi.

(* [comment removed for export] *)
Definition heap_rg (base : word) (cur : Z) : region :=
  Rg (bv_unsigned base) (bv_unsigned base + cur).

Lemma heap_rg_bump : forall base cur cur' a n,
  cur <= cur' -> covers (heap_rg base cur) a n -> covers (heap_rg base cur') a n.
Proof.
  intros base cur cur' a n Hle H.
  apply (covers_mono (heap_rg base cur)); [exact H | cbn; lia | cbn; lia].
Qed.

(* [comment removed for export] *)
Definition layout_wf (rs : list region) : Prop :=
  Forall rg_wf rs /\
  forall i j, (i < j)%nat -> (j < length rs)%nat ->
              rg_disj (nth i rs (Rg 0 0)) (nth j rs (Rg 0 0)).
End Footprint.

(* [comment removed for export] *)
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS Require CatSim.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS Require PropExec.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS Require SymStepR.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS Require MmapSim.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS Require WallSim.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StreamSim.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS Require DrainSim.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
Module StepTac.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.CatSim.ExitSim OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.PropExec OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.CatExec OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.CatSim OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.SeqExec OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.StreamExec OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.MmapSim OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.WallSim OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.StreamSim OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.DrainSim.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Unset Lia Cache.

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
        | eapply StreamSim.twr_step
        | eapply StreamSim.trd_step
        | eapply WallSim.twt_step
        | eapply WallSim.twe_step
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
  | |- StreamSim.to_wr _ _ _ ?st => norm_pc_state st
  | |- StreamSim.to_rd _ _ _ ?st => norm_pc_state st
  | |- WallSim.to_wall _ _ ?st _ _ => norm_pc_state st
  | |- WallSim.to_wall_tail _ _ ?st _ _ => norm_pc_state st
  | |- WallSim.to_wallexit _ _ _ _ ?st => norm_pc_state st
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
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma byte_nz_u : forall b : byte, b <> Z_to_bv 8 0 -> (bv_unsigned b <> 0)%Z.
Proof.
  intros b Hb Hc. apply Hb. apply bv_eq. rewrite Hc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u_zext8 : forall b : byte,
  bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof.
  intro b. apply u_Z2bv; pose proof (u8_range b); lia.
Qed.

(* [comment removed for export] *)
Lemma zext8_byte : forall b : byte,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) = b.
Proof.
  intro b. apply bv_eq.
  rewrite Z_to_bv_unsigned, u_zext8.
  apply bv_wrap_small. pose proof (u8_range b).
  change (bv_modulus 8) with 256%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma byte_neq_lit_u : forall (b : byte) (z : Z), (0 <= z < 256)%Z ->
  b <> Z_to_bv 8 z -> (bv_unsigned b <> z)%Z.
Proof.
  intros b z Hz Hb Hc. apply Hb. apply bv_eq.
  rewrite Hc, Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Z.mod_small; [reflexivity |].
  change (bv_modulus 8) with 256%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma c_eq_zext_lit_false : forall (b : byte) (z : Z), (0 <= z < 256)%Z ->
  b <> Z_to_bv 8 z ->
  c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 z) = false.
Proof.
  intros b z Hz Hb. unfold c_eq, bv_eqb. apply Z.eqb_neq.
  rewrite u_zext8, u_Z2bv by lia.
  exact (byte_neq_lit_u b z Hz Hb).
Qed.

(* [comment removed for export] *)
Lemma u_ntw : forall n : nat, (Z.of_nat n < 2^64)%Z ->
  bv_unsigned (nat_to_word n) = Z.of_nat n.
Proof. intros n Hn. unfold nat_to_word. apply u_Z2bv; lia. Qed.

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
Lemma word_add_nat_1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word m) 1 = a + nat_to_word (S m).
Proof.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma word_add_nat_m1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word (S m)) (-1) = a + nat_to_word m.
Proof.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma v_add_comm : forall x y : word, v_add x y = y + x.
Proof.
  intros x y. apply bv_eq.
  change (v_add x y) with (x + y).
  rewrite !bv_add_unsigned. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma v_add_wrap : forall x y : word,
  (2^64 <= bv_unsigned x + bv_unsigned y)%Z ->
  v_add x y = Z_to_bv 64 (bv_unsigned x + bv_unsigned y - 2^64).
Proof.
  intros x y Hw. unfold v_add. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- (Z.mod_add (bv_unsigned x + bv_unsigned y - 2^64) 1 (2^64)) by lia.
  f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma v_sub_0_neg : forall y : word,
  v_sub (Z_to_bv 64 0) y = Z_to_bv 64 (- bv_unsigned y).
Proof.
  intro y. unfold v_sub.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  f_equal.
Qed.

(* [comment removed for export] *)
Lemma u_neg_small : forall z : Z, (0 < z)%Z -> (z <= 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 (- z)) = (2^64 - z)%Z.
Proof.
  intros z Hz0 Hz. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  replace (- z)%Z with ((2^64 - z) + (-1) * 2^64)%Z by lia.
  rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma v_addi_neg_S : forall d : nat,
  v_addi (Z_to_bv 64 (- Z.of_nat (S d))) 1 = Z_to_bv 64 (- Z.of_nat d).
Proof.
  intro d. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
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
Lemma range_avoids_two : forall (s0 s1 : Segment) (a n : Z),
  Z.ltb a (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) = false ->
  Z.ltb a (Z.of_N (seg_base s1) + Z.of_N (seg_size s1)) = false ->
  range_avoids_ro_segs [s0; s1] a n = true.
Proof.
  intros s0 s1 a n H0 H1. unfold range_avoids_ro_segs. cbn [forallb].
  rewrite H0, H1. rewrite !andb_false_r. cbn [negb]. rewrite !orb_true_r.
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition ro_segs_below (segs : list Segment) (data_base : Z) : bool :=
  forallb (fun seg =>
             seg_writable seg
             || Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) data_base)
          segs.

Lemma range_avoids_ro_above : forall (segs : list Segment) (data_base addr n : Z),
  ro_segs_below segs data_base = true ->
  (data_base <= addr)%Z ->
  range_avoids_ro_segs segs addr n = true.
Proof.
  intros segs data_base addr n Hbelow Haddr.
  unfold ro_segs_below in Hbelow. unfold range_avoids_ro_segs.
  rewrite forallb_forall in *. intros seg Hin.
  specialize (Hbelow seg Hin).
  destruct (seg_writable seg) eqn:W; cbn [orb] in *; [reflexivity|].
  apply Z.leb_le in Hbelow.
  apply negb_true_iff. apply andb_false_iff. right.
  apply Z.ltb_ge. lia.
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
End StepTac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AllocSim.
Module StoreOk.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.PropExec OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.CatExec StepTac OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.StreamSim OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.AllocSim Footprint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition mem_grows (m m' : word -> option byte) : Prop :=
  forall x, m x <> None -> m' x <> None.

Lemma mem_grows_refl : forall m, mem_grows m m.
Proof. intros m x H. exact H. Qed.

Lemma mem_grows_trans : forall m1 m2 m3,
  mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 H12 H23 x Hx. apply H23, H12, Hx. Qed.

(* [comment removed for export] *)
Lemma wview_grows : forall segs m m' x,
  mem_grows m m' ->
  wview segs m x <> None -> wview segs m' x <> None.
Proof.
  intros segs m m' x Hg Hx. unfold wview in *.
  destruct (m' x) as [b'|] eqn:Hm'; [discriminate|].
  destruct (m x) as [b|] eqn:Hm.
  - exfalso. apply (Hg x); [rewrite Hm; discriminate|exact Hm'].
  - exact Hx.
Qed.

Lemma store_ok_mono : forall segs n m m' a,
  mem_grows m m' ->
  store_ok segs m a n = true -> store_ok segs m' a n = true.
Proof.
  intros segs n; induction n as [|n IH]; intros m m' a Hg H; [reflexivity|].
  cbn [store_ok] in *.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  destruct (wview segs m' a) as [b'|] eqn:Hv'.
  - apply (IH m m'); assumption.
  - exfalso. apply (wview_grows segs m m' a Hg); [rewrite Hv; discriminate|exact Hv'].
Qed.

(* [comment removed for export] *)

Lemma wbytes_grows : forall bs m a, mem_grows m (wbytes m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [wbytes]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_zeros_grows : forall zs m, mem_grows m (apply_zeros m zs).
Proof.
  intros zs m x Hx. unfold apply_zeros.
  destruct zs as [|z zs']; [exact Hx|].
  destruct (zeros_cover (z :: zs') x); [discriminate|exact Hx].
Qed.

Lemma zmem_grows : forall m b l, mem_grows m (zmem m b l).
Proof.
  intros m b l x Hx. unfold zmem.
  destruct (Z.leb _ _ && Z.ltb _ _)%bool; [discriminate|exact Hx].
Qed.

Lemma write_to_mem_grows : forall bs m a, mem_grows m (write_to_mem m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [write_to_mem]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_writes_grows : forall ws m, mem_grows m (apply_writes m ws).
Proof.
  induction ws as [|w ws' IH]; intros m x Hx.
  - exact Hx.
  - destruct w as [a bs]. cbn [apply_writes].
    apply IH. apply write_to_mem_grows. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma store_ok_of_all : forall segs n m a,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      wview segs m x <> None) ->
  store_ok segs m a n = true.
Proof.
  intros segs n; induction n as [|n IH]; intros m a Hnw Hall; [reflexivity|].
  cbn [store_ok].
  destruct (wview segs m a) as [b|] eqn:Hv.
  2: { exfalso. refine (Hall a _ Hv). rewrite Nat2Z.inj_succ. lia. }
  (* [comment removed for export] *)
  destruct n as [|n']; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hnw.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
    by (apply u_add1; rewrite Nat2Z.inj_succ in Hnw; lia).
  apply IH.
  - rewrite Hu1. lia.
  - intros x Hx. rewrite Hu1 in Hx. apply Hall.
    rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Lemma wrap_mem_window_defined : forall ph sp argv envp (x : word) uid hw rnd,
  bv_unsigned sp - stack_max_size <= bv_unsigned x ->
  bv_unsigned x < bv_unsigned sp ->
  wrap_mem ph sp argv envp uid hw rnd x <> None.
Proof.
  intros ph sp argv envp x uid hw rnd Hlo Hhi. unfold wrap_mem.
  destruct (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x) as [b|];
    [discriminate|].
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
  cbn. discriminate.
Qed.

Lemma store_ok_wrap_window : forall segs ph sp argv envp a n uid hw rnd,
  bv_unsigned sp - stack_max_size <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned sp ->
  store_ok segs (wrap_mem ph sp argv envp uid hw rnd) a n = true.
Proof.
  intros segs ph sp argv envp a n uid hw rnd Hlo Hhi.
  assert (Hsp : bv_unsigned sp < 2 ^ 64) by apply bv_unsigned_in_range.
  apply store_ok_of_all; [lia|].
  intros x Hx. unfold wview.
  destruct (wrap_mem ph sp argv envp uid hw rnd x) as [b|] eqn:Hw; [discriminate|].
  exfalso. revert Hw. apply wrap_mem_window_defined; lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_zeros_hit : forall segs m zs a n,
  zs <> [] ->
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      zeros_cover zs x = true) ->
  store_ok segs (apply_zeros m zs) a n = true.
Proof.
  intros segs m zs a n Hne Hnw Hcov.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview, apply_zeros.
  destruct zs as [|z zs']; [contradiction|].
  rewrite (Hcov x Hx). discriminate.
Qed.

(* [comment removed for export] *)
Lemma store_ok_zmem : forall segs m (b l a : word) (n : nat),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
  store_ok segs (zmem m b l) a n = true.
Proof.
  intros segs m b l a n Hnw Hlo Hhi.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview, zmem.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  cbn. discriminate.
Qed.

(* [comment removed for export] *)
Definition store_grant_ok (segs : list Segment) (m : word -> option byte)
                    (b l : word) : Prop :=
  forall (a : word) (n : nat),
    bv_unsigned b <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
    store_ok segs m a n = true.

Lemma store_grant_zmem : forall segs m b l,
  bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
  store_grant_ok segs (zmem m b l) b l.
Proof.
  intros segs m b l Hnw a n Hlo Hhi. apply store_ok_zmem; lia.
Qed.

(* [comment removed for export] *)
Lemma store_grant_zmem_prefix : forall segs m b logical physical,
  (bv_unsigned logical <= bv_unsigned physical)%Z ->
  (bv_unsigned b + bv_unsigned physical <= 2 ^ 64)%Z ->
  store_grant_ok segs (zmem m b physical) b logical.
Proof.
  intros segs m b logical physical Hle Hnw a n Hlo Hhi.
  apply store_ok_zmem; lia.
Qed.

Lemma store_grant_mono : forall segs m m' b l,
  mem_grows m m' -> store_grant_ok segs m b l -> store_grant_ok segs m' b l.
Proof.
  intros segs m m' b l Hg H a n Hlo Hhi.
  eapply store_ok_mono; [exact Hg|]. apply H; assumption.
Qed.

(* [comment removed for export] *)
Lemma store_ok_seg_writable : forall segs m a n,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      exists seg,
        find_segment segs (bv_unsigned x) 1 = Some seg /\
        seg_writable seg = true /\
        segment_byte_at (seg_bytes seg)
                    (Z.to_N (bv_unsigned x - Z.of_N (seg_base seg))) <> None) ->
  store_ok segs m a n = true.
Proof.
  intros segs m a n Hnw Hall.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview.
  destruct (m x) as [b|]; [discriminate|].
  destruct (Hall x Hx) as [seg [Hfind [Hw Hb]]].
  rewrite Hfind, Hw. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma store_ok_wseg : forall segs m a n,
  wseg_ok segs a n = true -> store_ok segs m a n = true.
Proof.
  intros segs m a n; revert a m; induction n as [|n IH]; intros a m H; [reflexivity|].
  cbn [wseg_ok] in H.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
  apply andb_true_iff in H as [H Hrec].
  apply andb_true_iff in H as [Hwr Hbyte].
  destruct (segment_byte_at (seg_bytes seg)
              (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
    [|discriminate].
  cbn [store_ok]. unfold wview at 1.
  destruct (m a) as [b0|]; [apply IH, Hrec|].
  rewrite Hseg, Hwr, Hb. apply IH, Hrec.
Qed.

(* [comment removed for export] *)
Lemma store_ok_all : forall segs m n a,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  store_ok segs m a n = true ->
  forall x : word,
    bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
    wview segs m x <> None.
Proof.
  intros segs m n; induction n as [|n IH]; intros a Hnw H x Hx;
    [cbn in Hx; lia|].
  cbn [store_ok] in H.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  rewrite Nat2Z.inj_succ in Hnw, Hx.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  { assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Hv. discriminate. }
  (* [comment removed for export] *)
  assert (Hn : (1 <= Z.of_nat n)%Z) by lia.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
  (* [comment removed for export] *)
  eapply IH; [ | exact H | ]; lia.
Qed.

Lemma store_ok_sub : forall segs m (lo a : word) (N n : nat),
  bv_unsigned lo + Z.of_nat N <= 2 ^ 64 ->
  store_ok segs m lo N = true ->
  bv_unsigned lo <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned lo + Z.of_nat N ->
  store_ok segs m a n = true.
Proof.
  intros segs m lo a N n Hnw Hok Hl Hh.
  apply store_ok_of_all; [lia|].
  intros x Hx. apply (store_ok_all segs m N lo Hnw Hok). lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_window : forall segs m (lo a : word) (N n : nat) (base hi : Z),
  bv_unsigned lo = base ->
  base + Z.of_nat N = hi ->
  hi <= 2 ^ 64 ->
  wseg_ok segs lo N = true ->
  base <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= hi ->
  store_ok segs m a n = true.
Proof.
  intros segs m lo a N n base hi Hbase Htop Hnw Hw Hl Hh.
  eapply store_ok_sub; [ | apply store_ok_wseg, Hw | | ]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma store_ok_read_aux : forall segs m n (a : word),
  store_ok segs m a n = true ->
  exists w, read_bytes_aux (wview segs m) a n = Some w.
Proof.
  intros segs m n; induction n as [|n IH]; intros a H.
  - exists []. reflexivity.
  - cbn [store_ok] in H. cbn [read_bytes_aux].
    destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
    destruct (IH (a + 1)%bv H) as [w Hw]. rewrite Hw. exists (b :: w). reflexivity.
Qed.

Lemma store_ok_wbuf : forall segs ms (buf cnt : word),
  store_ok segs (ms_mem ms) buf (word_to_nat cnt) = true ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms buf cnt H.
  rewrite read_bytes_map_eq. unfold ms_writable_byte.
  apply store_ok_read_aux. exact H.
Qed.

(* [comment removed for export] *)
Lemma of_nat_word_to_nat : forall w : word,
  Z.of_nat (word_to_nat w) = bv_unsigned w.
Proof.
  intro w. unfold word_to_nat. pose proof (u64_range w). lia.
Qed.

(* [comment removed for export] *)
Lemma store_grant_wbuf : forall segs ms (b l buf cnt : word),
  store_grant_ok segs (ms_mem ms) b l ->
  bv_unsigned b <= bv_unsigned buf ->
  bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms b l buf cnt Hg Hlo Hhi.
  apply store_ok_wbuf, Hg; rewrite ?of_nat_word_to_nat; lia.
Qed.

(* [comment removed for export] *)
Lemma heap_rg_wbuf : forall segs ms (b l buf cnt : word) (cur : Z),
  store_grant_ok segs (ms_mem ms) b l ->
  cur <= bv_unsigned b + bv_unsigned l - bv_unsigned b ->
  covers (heap_rg b cur) buf (word_to_nat cnt) ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms b l buf cnt cur Hg Hcur Hc.
  destruct Hc as [Hlo Hhi]. cbn [heap_rg rg_lo rg_hi] in Hlo, Hhi.
  rewrite of_nat_word_to_nat in Hhi.
  eapply store_grant_wbuf; [exact Hg | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma zmem_wbuf : forall segs ms m (b l buf cnt : word),
  mem_grows (zmem m b l) (ms_mem ms) ->
  bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned buf ->
  bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms m b l buf cnt Hgr Hnw Hlo Hhi.
  eapply store_grant_wbuf; [ | exact Hlo | exact Hhi ].
  eapply store_grant_mono; [exact Hgr|]. apply store_grant_zmem. exact Hnw.
Qed.

(* [comment removed for export] *)
Example drain_buffer_in_grant : forall segs ms m (b l buf cnt : word) a bs,
  ms_mem ms = wbytes (zmem m b l) a bs ->
  bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned buf ->
  bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms m b l buf cnt a bs Hm Hnw Hlo Hhi.
  eapply zmem_wbuf;
    [ rewrite Hm; apply wbytes_grows | exact Hnw | exact Hlo | exact Hhi ].
Qed.

(* [comment removed for export] *)
Ltac store_ok_peel :=
  repeat first
    [ eapply store_ok_mono; [apply wbytes_grows|]
    | eapply store_ok_mono; [apply write_to_mem_grows|]
    | eapply store_ok_mono; [apply apply_zeros_grows|]
    | eapply store_ok_mono; [apply apply_writes_grows|] ].

(* [comment removed for export] *)
Ltac store_ok_base :=
  first
    [ apply store_ok_wrap_window; unfold stack_max_size; u_norm; lia
    | eapply store_ok_zeros_hit;
      [ discriminate | u_norm; lia | intros; u_norm; lia ]
    | apply store_ok_zmem; u_norm; lia ].

(* [comment removed for export] *)
Ltac solve_store_ok :=
  store_ok_peel;
  first [ store_ok_base
        | eapply store_ok_mono; [apply zmem_grows|];
          store_ok_peel; store_ok_base ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Create HintDb store_ok_db.

Ltac store_ok_grows := solve [ eauto with store_ok_db ].

Ltac solve_store_ok_inv :=
  first [ solve_store_ok
        | store_ok_peel;
          eapply store_ok_mono; [ store_ok_grows | ]; solve_store_ok ].

(* [comment removed for export] *)
Ltac solve_mem_grows :=
  repeat first
    [ solve [ eauto with store_ok_db ]
    | apply mem_grows_refl
    | eapply mem_grows_trans; [ | apply wbytes_grows ]
    | eapply mem_grows_trans; [ | apply zmem_grows ]
    | eapply mem_grows_trans; [ | apply write_to_mem_grows ]
    | eapply mem_grows_trans; [ | apply apply_zeros_grows ]
    | eapply mem_grows_trans; [ | apply apply_writes_grows ] ].
End StoreOk.

(* [comment removed for export] *)
From Stdlib Require NArith.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS Require ShapeAlg.
Module AgentLib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.PropExec OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.CatExec OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.CatSim OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.SeqExec OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.StreamExec OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.ShapeAlg StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
  (* [comment removed for export] *)
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_emit_app : forall (a b : list event) (T : TSet),
  t_eq (t_emit (a ++ b) T) (t_emit a (t_emit b T)).
Proof.
  intros a b T tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)].
    + apply is_prefix_app_split in Hp as [Hp | (b' & -> & Hp)].
      * left. exact Hp.
      * right. exists b'. split; [reflexivity | left; exact Hp].
    + right. exists (b ++ tr'). split; [rewrite app_assoc; reflexivity|].
      right. exists tr'. auto.
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono. exact Hp.
    + right. exists tr''. rewrite app_assoc. auto.
Qed.

Lemma t_emit_congr : forall (e : list event) (T T' : TSet),
  t_eq T T' -> t_eq (t_emit e T) (t_emit e T').
Proof.
  intros e T T' H tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
  - intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
Qed.

Lemma t_alt2_congr : forall A A' B B' : TSet,
  t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof. intros A A' B B' HA HB tr. unfold t_alt2. rewrite (HA tr), (HB tr). reflexivity. Qed.

Lemma t_emit_nil_l : forall (T : TSet), T [] -> t_eq (t_emit [] T) T.
Proof. exact t_emit_nil_eq. Qed.

(* [comment removed for export] *)
Lemma rz_eq : forall segs c (T T' : TSet),
  t_eq T' T -> realizes segs c T' -> realizes segs c T.
Proof. intros segs c T T' Heq H. eapply rz_conseq; [exact H | exact Heq]. Qed.

(* [comment removed for export] *)
Lemma t_emit_app3 : forall (a b c : list event) (T : TSet),
  t_eq (t_emit a (t_emit b (t_emit c T))) (t_emit (a ++ b ++ c) T).
Proof.
  intros a b c T. apply t_eq_sym.
  eapply t_eq_trans; [apply t_emit_app|].
  apply t_emit_congr. apply t_emit_app.
Qed.

(* [comment removed for export] *)
Lemma map_app3 {A B} (f : A -> B) (a b c : list A) :
  map f (a ++ b ++ c) = map f a ++ map f b ++ map f c.
Proof. rewrite !map_app. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma len_word_of_nat : forall (bs : list byte),
  len_word bs = Z_to_bv 64 (Z.of_nat (length bs)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma read_bytes_map_of_store_ok : forall segs mem (a : word) (n : nat),
  store_ok segs mem a n = true -> (Z.of_nat n < 2 ^ 64)%Z ->
  exists w, read_bytes_map (wview segs mem) a (Z_to_bv 64 (Z.of_nat n)) = Some w.
Proof.
  intros segs mem a n H Hn. rewrite read_bytes_map_eq. unfold word_to_nat.
  rewrite Z_to_bv_small by (unfold bv_modulus; lia). rewrite Nat2Z.id.
  apply store_ok_read_aux. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fd_insert_head_same : forall fds (fd : word) e e',
  fd_insert ((fd, e) :: fds) fd e' = fd_insert fds fd e'.
Proof.
  intros fds fd e e'. unfold fd_insert. cbn [List.filter fst].
  rewrite bv_eqb_refl. cbn [negb]. reflexivity.
Qed.

Lemma filter_fd_id : forall (fds : list (word * FdEntry)) (fd : word),
  fd_lookup fds fd = None ->
  List.filter (fun p => negb (bv_eqb (fst p) fd)) fds = fds.
Proof.
  induction fds as [|[k e] r IH]; intros fd H; [reflexivity|].
  cbn [List.filter fst fd_lookup] in *.
  destruct (bv_eqb k fd) eqn:E; [discriminate|]. cbn [negb].
  rewrite (IH fd H). reflexivity.
Qed.

Lemma fd_insert_fresh_eq : forall fds (fd : word) e,
  fd_lookup fds fd = None -> fd_insert fds fd e = (fd, e) :: fds.
Proof. intros fds fd e H. unfold fd_insert. rewrite (filter_fd_id fds fd H). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_lit : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

(* [comment removed for export] *)
Lemma v_add_lit : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (a + b < 2 ^ 64)%Z ->
  v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b Ha Hb Hab. unfold v_add. rewrite !u64_lit by lia. reflexivity.
Qed.

Lemma v_sub_lit : forall a b, (0 <= b <= a)%Z -> (a < 2 ^ 64)%Z ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b Hab Ha. unfold v_sub. rewrite !u64_lit by lia. reflexivity.
Qed.

Lemma v_addi_lit : forall a i, (0 <= a < 2 ^ 64)%Z ->
  v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros a i Ha. unfold v_addi. rewrite u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma Z_to_bv_64_mod : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64).
Proof.
  intro z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma c_ltu_lit : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma c_eq_lit : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b)%Z.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bv_signed_small : forall z, (0 <= z < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap.
  unfold bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z by reflexivity.
  replace (2 ^ 64 `div` 2)%Z with (2 ^ 63)%Z by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma bv_signed_neg : forall e, (0 < e <= 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 (- e)) = (- e)%Z.
Proof.
  intros e He. rewrite Z_to_bv_signed. unfold bv_swrap.
  unfold bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z by reflexivity.
  replace (2 ^ 64 `div` 2)%Z with (2 ^ 63)%Z by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma c_lts_zero_nonneg : forall z, (0 <= z < 2 ^ 63)%Z ->
  c_lts (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof.
  intros z Hz. unfold c_lts, bv_lts. rewrite !bv_signed_small by lia. apply Z.ltb_ge. lia.
Qed.

Lemma c_lts_zero_errno : forall e, (0 < e <= 2 ^ 63)%Z ->
  c_lts (Z_to_bv 64 (- e)) (Z_to_bv 64 0) = true.
Proof.
  intros e He. unfold c_lts, bv_lts. rewrite bv_signed_neg by lia.
  rewrite bv_signed_small by lia. apply Z.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma errno_ret_lit : forall e, errno_ret e = Z_to_bv 64 (- e).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac show_goal_marker := match goal with |- ?g => idtac "=====GOAL=====" g end.

(* [comment removed for export] *)
Lemma rdn_addr_eq : forall segs m (a b : word) n r,
  a = b -> rdn segs m b n = r -> rdn segs m a n = r.
Proof. intros segs m a b n r -> H. exact H. Qed.

Ltac rdn_at b :=
  apply (rdn_addr_eq _ _ _ b);
  [ first [ f_equal; lia
          | lazymatch goal with |- ?g => StepTac.check_closed_term g end;
            apply bv_eq; vm_compute; reflexivity ]
  | ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zall (n : nat) (f : Z -> bool) (z : Z) : bool :=
  match n with
  | O => true
  | S n' => if f z then zall n' f (z + 1)%Z else false
  end.

Lemma zall_spec : forall n f z,
  zall n f z = true -> forall x, (z <= x < z + Z.of_nat n)%Z -> f x = true.
Proof.
  induction n as [|n IH]; intros f z H x Hx; [lia|].
  cbn [zall] in H. destruct (f z) eqn:E; [|discriminate].
  destruct (Z.eq_dec x z) as [->|Hne]; [exact E|].
  apply (IH f (z + 1)%Z H). lia.
Qed.

(* [comment removed for export] *)
Lemma zallN_spec : forall (n : N) f,
  zall (N.to_nat n) f 0%Z = true -> forall x, (0 <= x < Z.of_N n)%Z -> f x = true.
Proof. intros n f H x Hx. apply (zall_spec (N.to_nat n) f 0%Z H). rewrite N_nat_Z. lia. Qed.

(* [comment removed for export] *)
Ltac rdn_at_hyp Hb :=
  lazymatch type of Hb with
  | rdn _ _ ?b _ = _ => rdn_at b; exact Hb
  end.
End AgentLib.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import PropExec.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS Require SymStepR.
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.CatExec.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS Require SymStepR.
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.SeqExec.
Import StepTac.
Import StoreOk.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import StreamSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_inside : forall bs m (a x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
  wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
  cbn [wbytes length] in *.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Z.sub_diag. cbn [Z.to_nat nth].
    destruct rest as [|b' rest'].
    + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
    + cbn [length] in Hnw. rewrite wbytes_below.
      * rewrite bv_eqb_refl. reflexivity.
      * rewrite u_add1 by lia. cbn [length]. lia.
      * rewrite u_add1 by lia. lia.
  - assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
      by (apply u_add1; lia).
    rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
    rewrite Hu1.
    replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
      with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
    reflexivity.
Qed.

Lemma wbytes_outside : forall bs m (a x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x) ->
  wbytes m a bs x = m x.
Proof.
  intros bs m a x Hnw [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above; assumption.
Qed.

(* [comment removed for export] *)
Lemma wbytes_select : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
                    P x = true) ->
  wbytes (fun x => if P x then f x else g x) a bs
  = (fun x => if P x then wbytes f a bs x else g x).
Proof.
  intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

Lemma wbytes_select_r : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
                    P x = false) ->
  wbytes (fun x => if P x then f x else g x) a bs
  = (fun x => if P x then f x else wbytes g a bs x).
Proof.
  intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wbytes_shadow : forall m (a : word) bs1 bs2,
  length bs1 = length bs2 ->
  bv_unsigned a + Z.of_nat (length bs2) <= 2^64 ->
  wbytes (wbytes m a bs1) a bs2 = wbytes m a bs2.
Proof.
  intros m a bs1 bs2 Hlen Hnw. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs2))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_const : forall segs m (a : word) n b,
  bv_unsigned a + Z.of_nat n <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> m x = Some b) ->
  rdn segs m a n = Some (repeat b n).
Proof.
  intros segs m a n; revert a; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
  cbn [rdn repeat]. rewrite (Hall a) by lia.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv b) by (rewrite Hu1; first [lia | intros x Hx; apply Hall; lia]).
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition win_lo (sp0 : word) : Z := bv_unsigned sp0 - stack_max_size.

Definition in_win (sp0 : word) (x : word) : Prop :=
  win_lo sp0 <= bv_unsigned x < bv_unsigned sp0.

Definition cmem (sp0 : word) (mem0 J D : word -> option byte) : word -> option byte :=
  fun a => if (bv_unsigned sp0 <=? bv_unsigned a) then mem0 a
           else if (win_lo sp0 <=? bv_unsigned a) then J a else D a.

(* [comment removed for export] *)
Definition wfJ (sp0 : word) (J : word -> option byte) : Prop :=
  forall x : word, in_win sp0 x -> J x <> None.

Lemma wfJ_const : forall sp0 b, wfJ sp0 (fun _ => Some b).
Proof. intros sp0 b x _. discriminate. Qed.

Lemma wfJ_wbytes : forall sp0 J a bs, wfJ sp0 J -> wfJ sp0 (wbytes J a bs).
Proof. intros sp0 J a bs H x Hx. apply wbytes_grows. apply H. exact Hx. Qed.

(* [comment removed for export] *)
Definition agree_above (lo : Z) (J J' : word -> option byte) : Prop :=
  forall x : word, lo <= bv_unsigned x -> J' x = J x.

Lemma agree_above_refl : forall lo J, agree_above lo J J.
Proof. intros lo J x _. reflexivity. Qed.

Lemma agree_above_trans : forall lo J1 J2 J3,
  agree_above lo J1 J2 -> agree_above lo J2 J3 -> agree_above lo J1 J3.
Proof. intros lo J1 J2 J3 H12 H23 x Hx. rewrite (H23 x Hx). apply H12. exact Hx. Qed.

Lemma agree_above_mono : forall lo lo' J J',
  lo <= lo' -> agree_above lo J J' -> agree_above lo' J J'.
Proof. intros lo lo' J J' Hle H x Hx. apply H. lia. Qed.

Lemma agree_above_wbytes : forall lo J a bs,
  bv_unsigned a + Z.of_nat (length bs) <= lo ->
  agree_above lo J (wbytes J a bs).
Proof.
  intros lo J a bs Hle x Hx. apply wbytes_above. lia.
Qed.

Lemma rdn_agree_above : forall segs lo J J' (a : word) n,
  agree_above lo J J' -> lo <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= 2^64 ->
  rdn segs J' a n = rdn segs J a n.
Proof.
  intros segs lo J J' a n H Hlo Hnw. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply H. lia.
Qed.

Section CMem.
  Variable sp0 : word.
  Variable mem0 : word -> option byte.

  Let csel := cmem sp0 mem0.

  Lemma stack_max_size_pos : 0 < stack_max_size.
  Proof. rewrite stack_max_size_val. lia. Qed.

  (* [comment removed for export] *)

  Lemma wbytes_cmem_win : forall J D (a : word) bs,
    win_lo sp0 <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned sp0 ->
    wbytes (cmem sp0 mem0 J D) a bs = cmem sp0 mem0 (wbytes J a bs) D.
  Proof.
    intros J D a bs Hlo Hhi. unfold cmem.
    pose proof (u64_range sp0) as Hsp.
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
               (fun x => if win_lo sp0 <=? bv_unsigned x then J x else D x) a bs)
      by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
    apply functional_extensionality. intro x.
    destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
    rewrite (wbytes_select (fun x => win_lo sp0 <=? bv_unsigned x) J D a bs)
      by (first [lia | intros y Hy; apply Z.leb_le; lia]).
    reflexivity.
  Qed.

  Lemma wbytes_cmem_data : forall J D (a : word) bs,
    bv_unsigned a + Z.of_nat (length bs) <= win_lo sp0 ->
    wbytes (cmem sp0 mem0 J D) a bs = cmem sp0 mem0 J (wbytes D a bs).
  Proof.
    intros J D a bs Hhi. unfold cmem.
    pose proof (u64_range sp0) as Hsp. pose proof stack_max_size_pos.
    unfold win_lo in *.
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
               (fun x => if bv_unsigned sp0 - stack_max_size <=? bv_unsigned x then J x else D x) a bs)
      by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
    apply functional_extensionality. intro x.
    destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 - stack_max_size <=? bv_unsigned x) J D a bs)
      by (first [lia | intros y Hy; apply Z.leb_gt; lia]).
    reflexivity.
  Qed.

  (* [comment removed for export] *)

  Lemma rdn_cmem_above : forall segs J D (a : word) n,
    bv_unsigned sp0 <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat n <= 2^64 ->
    rdn segs (cmem sp0 mem0 J D) a n = rdn segs mem0 a n.
  Proof.
    intros segs J D a n Hlo Hnw. apply rdn_ext; [exact Hnw|].
    intros x Hx. unfold cmem. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  Lemma rdn_cmem_win : forall segs J D (a : word) n,
    win_lo sp0 <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 ->
    rdn segs (cmem sp0 mem0 J D) a n = rdn segs J a n.
  Proof.
    intros segs J D a n Hlo Hhi. pose proof (u64_range sp0).
    apply rdn_ext; [lia|].
    intros x Hx. unfold cmem.
    rewrite (proj2 (Z.leb_gt _ _)) by lia.
    rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  Lemma rdn_cmem_data : forall segs J D (a : word) n,
    bv_unsigned a + Z.of_nat n <= win_lo sp0 ->
    rdn segs (cmem sp0 mem0 J D) a n = rdn segs D a n.
  Proof.
    intros segs J D a n Hhi. pose proof (u64_range sp0). pose proof stack_max_size_pos.
    unfold win_lo in *.
    apply rdn_ext; [lia|].
    intros x Hx. unfold cmem, win_lo.
    rewrite (proj2 (Z.leb_gt _ _)) by lia.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cmem_at_above : forall J D (x : word),
    bv_unsigned sp0 <= bv_unsigned x -> cmem sp0 mem0 J D x = mem0 x.
  Proof. intros. unfold cmem. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. Qed.

  Lemma cmem_at_win : forall J D (x : word),
    in_win sp0 x -> cmem sp0 mem0 J D x = J x.
  Proof.
    intros J D x [Hlo Hhi]. unfold cmem.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  Lemma cmem_at_data : forall J D (x : word),
    bv_unsigned x < win_lo sp0 -> cmem sp0 mem0 J D x = D x.
  Proof.
    intros J D x Hx. pose proof stack_max_size_pos. unfold cmem, win_lo in *.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)

  Lemma store_ok_cmem_win : forall segs J D (a : word) n,
    wfJ sp0 J ->
    win_lo sp0 <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 ->
    store_ok segs (cmem sp0 mem0 J D) a n = true.
  Proof.
    intros segs J D a n HJ Hlo Hhi. pose proof (u64_range sp0).
    apply store_ok_of_all; [lia|].
    intros x Hx. unfold wview.
    rewrite cmem_at_win by (unfold in_win; lia).
    destruct (J x) as [b|] eqn:E; [discriminate|].
    exfalso. apply (HJ x); [unfold in_win; lia | exact E].
  Qed.

  Lemma store_ok_cmem_data : forall segs J D (a : word) n,
    wseg_ok segs a n = true ->
    store_ok segs (cmem sp0 mem0 J D) a n = true.
  Proof. intros. apply store_ok_wseg. assumption. Qed.

End CMem.

(* [comment removed for export] *)
Lemma cmem_init : forall ph (sp0 : word) av ev uid hw (rdraw : EntryDraw),
  wrap_mem ph sp0 av ev uid hw rdraw
  = cmem sp0 (wrap_mem ph sp0 av ev uid hw rdraw) (fun _ => Some (Z_to_bv 8 0)) (fun _ => None).
Proof.
  intros ph sp0 av ev uid hw rdraw. apply functional_extensionality. intro x.
  unfold cmem.
  destruct (bv_unsigned sp0 <=? bv_unsigned x) eqn:E1; [reflexivity|].
  apply Z.leb_gt in E1.
  unfold wrap_mem, win_lo.
  assert (Hst : stack_to_mem sp0 (entry_stack_image ph sp0 av ev uid hw rdraw) x = None).
  { unfold stack_to_mem. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
  rewrite Hst. rewrite (proj2 (Z.ltb_lt _ _) E1), andb_true_r. reflexivity.
Qed.
