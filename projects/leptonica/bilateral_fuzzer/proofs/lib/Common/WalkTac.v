(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_WalkTac () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith6BinInt1Z7add_0_l".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac gres_core :=
  gres_loop;          (* [comment removed for export] *)
  rewrite ?getr_zero.
(* [comment removed for export] *)
Ltac mem_is_clean M :=
  tryif has_evar M then fail else
  lazymatch M with
  | context [getr _ _] => fail
  | context [v_addi _ _] => fail
  | context [v_add _ _] => fail
  | _ => idtac
  end.
Ltac gres_hiding M :=
  tryif mem_is_clean M then (let GM := fresh "GRES_M" in set (GM := M); gres_core; subst GM) else gres_core.
Ltac gres :=
  first [ lazymatch goal with
          | |- context [mkst ?R ?pc ?M ?rom] => gres_hiding M
          | |- rdn _ ?M _ _ = _ => gres_hiding M
          | |- store_ok _ ?M _ _ = _ => gres_hiding M
          | |- context [wbytes ?M _ _] => gres_hiding M
          end
        | gres_core ].

(* [comment removed for export] *)
Lemma v_add_0_r : forall x : word, v_add x (Z_to_bv 64 0) = x.
Proof.
ltac2:(KReplay.run1 (kr_t_WalkTac ()) [] "h02b1h12b2h21nh31zh41Hh51xp;1p;2p;3p;6g0000j13Tg000Uj1>Tg0013j12Tg001Vj20Tg002@j24Tg002fj31Tg003@j3;Tg003dj29Tg004Jj28Tg005=j37Tg005ij26Tg006Xj65Tg0076j2:Tg007Sj1=Tg0084j2<Tg008n#3#3#3#3#3#3#>R0#2R1g009SR2f0R3,00R41403f1R5511X32g00:1R6%23R7%25R8g00:Of2R9#2?153f3R:/0910:5512R;[10951093512%2:?195[R<f4#2?1:9\;A;953P3n2001000000120000000W1W0W2P<^18^07^26P3P01005R6,40R7P5P2190610099123X321805970610071606E5O4b4g00:jR6,:4%=4E51406,<3=113eW5o"). Qed.

Lemma v_add_0_l : forall x : word, v_add (Z_to_bv 64 0) x = x.
Proof.
ltac2:(KReplay.run1 (kr_t_WalkTac ()) [] "h02b1h12b2h21nh31zh41Hh51xp;1p;2p;3p;6g0000j13Tg000Uj1>Tg0013j12Tg001Vj20Tg002@j24Tg002fj31Tg003@j3;Tg003dj29Tg004Jj28Tg005=j37Tg005ij26Tg006Xj65Tg0076j2:Tg00;Hj1=Tg0084j2<Tg008n#3#3#3#3#3#3#>R0#2R1g009SR2f0R3,00R41403f1R5511X32g00:1R6%23R7%25R8g00:Of2R9#2?153f3R:/0910:5512R;[10951093512%2:?195[R<f4#2?1:9\;A;953P3n2001000000120000000W1W0W2P<^18^07^26P3P01005R6,40R7P5P2190610099123X321805970610071606E5O4b4g00:jR6/:4%=4E51406/<3=113eW5o"). Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac val_lit v :=
  lazymatch v with
  | Z_to_bv 64 ?z => tryif is_Z_lit z then fail else wlit_closed v
  | @BV _ _ _ => fail
  | _ => wlit_closed v
  end.

(* [comment removed for export] *)
Ltac vals_lit :=
  repeat match goal with
         | |- context [regupd _ _ ?v] => val_lit v
         end.

(* [comment removed for export] *)
Ltac vnorm_core := gres_core; imm_norm; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; vals_lit.
Ltac vnorm :=
  first [ lazymatch goal with
          | |- context [mkst ?R ?pc ?M ?rom] =>
              tryif mem_is_clean M then (let GM := fresh "VN_M" in set (GM := M); vnorm_core; subst GM) else vnorm_core
          end
        | vnorm_core ].

(* [comment removed for export] *)
Ltac stepn F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
  | _ => stepi F D; vnorm
  end.

(* [comment removed for export] *)
Ltac vres := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].
Ltac stepv F D v := stepiv F D v vres.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac cond_compute :=
  idtac;
  lazymatch goal with
  | |- ?g => check_closed_term g; vm_compute; reflexivity
  end.

(* [comment removed for export] *)
Ltac stepb F D :=
  first [ stepb_tk F D ltac:(cond_compute) | stepb_ft F D ltac:(cond_compute) ].

(* [comment removed for export] *)
Ltac stepret F D k tac :=
  stepjr F D k ltac:(gres; tac);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      | Hk : v_jalr k 0 = k |- _ => rewrite Hk
      end;
  try (wlit (v_jalr k 0)).

(* [comment removed for export] *)
Ltac stepsd F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sd_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
    | gres; first [ reflexivity | assumption | symmetry; assumption ]
    | oktac ]
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepld F D vv rtac :=
  chain_step;
  [ reflexivity
  | eapply step_ld with (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; rtac
    | first [ apply bytes_le_to_Z_8 | reflexivity ] ]
  | step_simpl; vnorm ].
