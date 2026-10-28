(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.EH Require Import XExitSim XPropExec XCatExec XCatSim XSeqExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require Import OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick12eq37Corelib4Init9Datatypesla6option01Z3h5LinuxProcessSemantics5Riscv5Instrne5instr7fOssFuzzTheorems6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExecqa4getrqa6v_addila4Somela4boolla4prod3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshgedmachine_stateqa4mksthf9bv_signedla4consla5falsela4listla3nilla4pairla4true3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehp37Segmenthge9MachineOkhgeafetch_wordhge8is_ecallhgeemachine_resulthge4stephge8store_ok3h5LinuxProcessSemantics5Riscv7DecodeCii0adecode_anyne3SZ1ne5Store3h5LinuxProcessSemantics5Riscv7Preludeim25bvmap7fOssFuzzTheorems6Proofsaboost_jsonafuzz_parse3lib2EH8XCatExecip16wbyteshf7Z_to_bvhfbbv_unsigned46Stdlib6ZArith6BinInt1Ziv12leiv12ltiv13powiv13subiv13add" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Section WithFP0.
Context {fx : FPState}.
Lemma step_sb_any : ltac2:(zQ "i21!h9!jc!l5!n2!nb!q2!u9!v0!v9!hg0!hg7!hk5!hl6!hld!hm9!hn0!hn8!hnf!ho5!hoc!hs8!ht3!hu0!hue!hva!igc!ih4!ik6!il4!ila!io8!isf!it9!iu3&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$h0$h4>4regs@2$he@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>0@3$2@1$3@1$1@1$0#i0@2$h6^9^7@2$8@1$1@1$0#i0^4>0@3$2$9@1$h7^5$f>0@3$2@1$3@2$a$5$4@1$hb^6@2$8@2$a$5$4@4$h2$5$4@4$hd$hc^5^4^3+4>0@3$2$9@4$ha^c^9@2$7@2$6^b^6@2$d@1$0#c^4N1$h3@3$2@1$h8$b@2$h9^d@5$c?2fx^c^b^a^9@2$h5$b@5$c?2fx^c@2$7^b+4@3$hf^a@2$7@2$6^c^7@2$d@1$0#c^5@3$e@1$1@1$0#8@2$i0@1$0#8@2$i1@1$0#k0@2$6^c^6@1$h1@1$1@1$0#8^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  rewrite <- N_to_le_bytes_1_small.
  apply (step_sb segs regs pc mem rom w rs1 rs2 imm); assumption.
Qed.
Lemma step_sb_at : ltac2:(zQ "i21!h9!jc!l5!n2!nb!q2!v9!hg0!hg7!hk5!u9!hl6!v0!hm9!hn0!hn8!hnf!ho5!hoc!hs8!ht3!hu0!hue!hva!igc!ih4!ik6!il4!ila!io8!isf!it9!hld!iu3&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$f$h3>4regs@2$hd@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>1a@1$1@1$0#k0>1v@1$1@1$0#k0>1b@1$1@1$0#8>0@3$2@1$3@1$1@1$0#i0@2$h5^c^a@2$6@1$1@1$0#i0^7>0@3$2$7@1$h6^8$e>0@3$2@1$3@2$8$5$4@1$ha^9@2$6@2$8$5$4@4$h1$5$4@4$hc$hb^8^7^6+4>0@3$2@1$1@1$0#k0@2$c@2$a^e^9@2$i0@1$0#c^7^6>0@3$2@1$1@1$0#k0@2$a^f^9^6>0@3$2@1$1@1$0#8@2$hf@1$0#8@2$i1@1$0#k0^7^6>0@3$2$7@4$h9^h2^f^9N1$h2@3$2@1$h7$9@2$h8^h3@5$b?2fx^h2^h1^h0^f@2$h4$9@5$b?2fx^h2@2$c^h1+4@3$he^h0^a@3$d@1$1@1$0#8^8@1$h0@1$1@1$0#8^f").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v b Hf He Hd Ha Hv Hb Hok.
  rewrite (step_sb_any segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv, Hb. reflexivity.
  - rewrite Ha. exact Hok.
Qed.
End WithFP0.


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
        | eapply te_step ].

Section WithFP2.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP2.

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
  | |- to_exit _ _ ?st => norm_pc_state st
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
    | exact (XPropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
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
        exact (XPropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
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
Lemma u_Z2bv : ltac2:(zQ "80!h9!nb!l5!jg9!jgf!jh5!it9!iu3>1z$1>0@2$3Z^1>0@2$4^2@2$5+2+k0@3$2$1@2$7@1$0#k0@2$6@1$0#k0^3^3").
Proof.
  intros z Hlo Hhi. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. apply Z.mod_small. split; [exact Hlo|].
  exact Hhi.
Qed.

(* [comment removed for export] *)
Lemma v_addi_m1 : ltac2:(zQ "80!h9!jc!iu3!l5!v0!jg9!jhc!it9>1x@1$1@1$0#k0>0@2$5+1@2$2@1$0#k0^1@3$3@1$1@1$0#k0@2$4^2-1@2$7@1$0#k0@2$6@2$2@1$0#k0^2+1").
Proof. intros x H1. apply (v_addi_m x 1); lia. Qed.

Lemma v_addi_m16 : ltac2:(zQ "80!h9!jc!iu3!l5!v0!jg9!jhc!it9>1x@1$1@1$0#k0>0@2$5+h0@2$2@1$0#k0^1@3$3@1$1@1$0#k0@2$4^2-h0@2$7@1$0#k0@2$6@2$2@1$0#k0^2+h0").
Proof. intros x H16. apply (v_addi_m x 16); lia. Qed.

Lemma v_addi_m32 : ltac2:(zQ "80!h9!jc!iu3!l5!v0!jg9!jhc!it9>1x@1$1@1$0#k0>0@2$5+i0@2$2@1$0#k0^1@3$3@1$1@1$0#k0@2$4^2-i0@2$7@1$0#k0@2$6@2$2@1$0#k0^2+i0").
Proof. intros x H32. apply (v_addi_m x 32); lia. Qed.

Lemma v_addi_m48 : ltac2:(zQ "80!h9!jc!iu3!l5!v0!jg9!jhc!it9>1x@1$1@1$0#k0>0@2$5+j0@2$2@1$0#k0^1@3$3@1$1@1$0#k0@2$4^2-j0@2$7@1$0#k0@2$6@2$2@1$0#k0^2+j0").
Proof. intros x H48. apply (v_addi_m x 48); lia. Qed.

Lemma v_addi_m64 : ltac2:(zQ "80!h9!jc!iu3!l5!v0!jg9!jhc!it9>1x@1$1@1$0#k0>0@2$5+k0@2$2@1$0#k0^1@3$3@1$1@1$0#k0@2$4^2-k0@2$7@1$0#k0@2$6@2$2@1$0#k0^2+k0").
Proof. intros x H64. apply (v_addi_m x 64); lia. Qed.

Lemma v_addi_m80 : ltac2:(zQ "80!h9!jc!iu3!l5!v0!jg9!jhc!it9>1x@1$1@1$0#k0>0@2$5+l0@2$2@1$0#k0^1@3$3@1$1@1$0#k0@2$4^2-l0@2$7@1$0#k0@2$6@2$2@1$0#k0^2+l0").
Proof. intros x H80. apply (v_addi_m x 80); lia. Qed.

(* [comment removed for export] *)
Lemma v_addi_nneg_t : ltac2:(zQ "b0!h9!ji3!jc!iu3!l5!nb!v0!jg9!jgf!jh5!it9>1x@1$2@1$0#k0>3imm$5>0@2$7Z^1>0@2$8@2$1@2$3@1$0#k0^3^2@2$9+2+k0@3$4@1$2@1$0#k0@2$6^4^3@2$a@1$0#k0@2$1@2$3@1$0#k0^4^3").
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
        eapply step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val
        | reflexivity | oktac ]
    end
  | step_simpl ].

(* [comment removed for export] *)

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

Section WithFP32.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP32.

Section WithFP33.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

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
