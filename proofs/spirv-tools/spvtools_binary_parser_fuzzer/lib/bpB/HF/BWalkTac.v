(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStepTac BHoare.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BWalkTac () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI47Corelib4Init5Logic2eq00C6ARocqVerifyHarness?AgentSubmission3bpB2HF9BPropExec;bv_eqb_reflC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7add_0_rC6ARocqVerifyHarness?AgentSubmission3bpB2HF9BPropExec5v_addI47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith6BinInt1Z7add_0_l".
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma reg_neq_of_eqb : forall a b : reg, bv_eqb a b = false -> a <> b.
Proof.
ltac2:(KReplay.run1 (kr_t_BWalkTac ()) [] "p'0h01Hh11bi001bh21Eh32H0h41ah51ep;1p;3p;2p;6p;7g0000j1;Tg000Uj1:Tg001:j16Tg001Xj14Tg002;j31Tg002hj32Tg003Bj25Tg004Cj63j78Tg004_j27Tg005>j19Tg005WR0f0R1g0067R232p=0g006W#;#:#6R3#4R4f1R5=131#0f2R6=245R7P4f3R8f4R9=131#0g007<R:]0X14A1388#0P0A1399%01X10P1g007YR81539E3A2082P0P8P0p-0P1g0089P:n0110000020000X50g008UP2P1E3P:17:1b3b0W0P6P1P5F8W2%97eW0X14W4o"). Qed.

Ltac getr_proof X r :=
  lazymatch X with
  | regupd ?Y ?rd ?v =>
      match tt with
      | _ => let chk := match tt with _ => constr_eq rd r end in
             uconstr:(getr_same Y r v (reg_neq_of_eqb r (0%bv) (@eq_refl bool false)))
      | _ => let p := getr_proof Y r in
             uconstr:(eq_trans (getr_other Y rd v r (reg_neq_of_eqb r rd (@eq_refl bool false))) p)
      end
  | _ => uconstr:(@eq_refl word (getr X r))
  end.

Ltac gres :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             let p := getr_proof X r in
             let p' := constr:(p) in rewrite p'
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.

Lemma v_add_0_r : forall x : word, v_add x (Z_to_bv 64 0) = x.
Proof.
ltac2:(KReplay.run1 (kr_t_BWalkTac ()) [] "h02b1h12b2h21nh31zh41Hh51xp;1p;2p;3p;6g0000j13Tg001:j1>Tg001Xj12Tg0091j20Tg009[j24Tg002hj31Tg00:Aj3;Tg00:ej29Tg00;Kj28Tg00<>j37Tg00<jj26Tg00=Yj65Tg00>7j2:Tg00>Tj1=Tg00?5j2<Tg006W#3#3#3#3#3#3#>R0#2R1g00@0R2f0R3,00R41403f1R5511X32g00@NR6%23R7%25R8g00@lf2R9#2?153f3R:/0910:5512R;[10951093512%2:?195[R<f4#2?1:9\;A;953P3n2001000000120000000W1W0W2P<^18^07^26P3P01005R6,40R7P5P2190610099123X321805970610071606E5O4b4g00AGR6,:4%=4E51406,<3=113eW5o"). Qed.

Lemma v_add_0_l : forall x : word, v_add (Z_to_bv 64 0) x = x.
Proof.
ltac2:(KReplay.run1 (kr_t_BWalkTac ()) [] "h02b1h12b2h21nh31zh41Hh51xp;1p;2p;3p;6g0000j13Tg001:j1>Tg001Xj12Tg0091j20Tg009[j24Tg002hj31Tg00:Aj3;Tg00:ej29Tg00;Kj28Tg00<>j37Tg00<jj26Tg00=Yj65Tg00>7j2:Tg00Aej1=Tg00?5j2<Tg006W#3#3#3#3#3#3#>R0#2R1g00@0R2f0R3,00R41403f1R5511X32g00@NR6%23R7%25R8g00@lf2R9#2?153f3R:/0910:5512R;[10951093512%2:?195[R<f4#2?1:9\;A;953P3n2001000000120000000W1W0W2P<^18^07^26P3P01005R6,40R7P5P2190610099123X321805970610071606E5O4b4g00AGR6/:4%=4E51406/<3=113eW5o"). Qed.

Ltac is_pos_lit p :=
  lazymatch p with
  | xH => idtac
  | xO ?q => is_pos_lit q
  | xI ?q => is_pos_lit q
  end.
Ltac is_Z_lit z :=
  lazymatch z with
  | Z0 => idtac
  | Zpos ?p => is_pos_lit p
  | Zneg ?p => is_pos_lit p
  end.

Ltac val_lit v :=
  lazymatch v with
  | Z_to_bv 64 ?z => tryif is_Z_lit z then fail else wlit_closed v
  | @BV _ _ _ => fail
  | _ => wlit_closed v
  end.

Ltac vals_lit :=
  repeat match goal with
         | |- context [regupd _ _ ?v] => val_lit v
         end.

Ltac vnorm :=
  gres; imm_norm;
  match goal with |- context [v_addi _ Z0] => rewrite ?v_addi_0 | _ => idtac end;
  match goal with |- context [v_add _ (Z_to_bv 64 0)] => rewrite ?v_add_0_r | _ => idtac end;
  match goal with |- context [v_add (Z_to_bv 64 0) _] => rewrite ?v_add_0_l | _ => idtac end;
  vals_lit.

Ltac stepn F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
  | _ => stepi F D; vnorm
  end.

Ltac vres := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].
Ltac stepv F D v := stepiv F D v vres.

Ltac stepb_tk F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].

Ltac stepb_ft F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].

Ltac cond_compute :=
  idtac;
  lazymatch goal with
  | |- ?g => check_closed_term g; vm_compute; reflexivity
  end.

Ltac stepb F D :=
  first [ stepb_tk F D ltac:(cond_compute) | stepb_ft F D ltac:(cond_compute) ].

Ltac stepret F D k tac :=
  stepjr F D k ltac:(gres; tac);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      | Hk : v_jalr k 0 = k |- _ => rewrite Hk
      end;
  try (wlit (v_jalr k 0)).

Ltac stepsd F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sd_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
    | gres; first [ reflexivity | assumption | symmetry; assumption ]
    | oktac ]
  | step_simpl ].

Ltac stepld F D vv rtac :=
  chain_step;
  [ reflexivity
  | eapply step_ld with (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; rtac
    | first [ apply bytes_le_to_Z_8 | reflexivity ] ]
  | step_simpl; vnorm ].
