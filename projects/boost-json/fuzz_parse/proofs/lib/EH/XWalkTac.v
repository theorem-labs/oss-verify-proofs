(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStepTac XHoare.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option37Corelib4Init5Logicm22eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~nb4getrk14boolk15falsek14listk14prodm21I3h5LinuxProcessSemantics5Riscv7Preludeu26bv_eqbu25bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XWalkTac~~~~~~hh98wf_chainhh97wf_lookhf2BVhf4BvWfnb5v_addhf7Z_to_bv" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint wf_chain (l : list (reg * word)) (R : bvmap 5 word) : bvmap 5 word :=
  match l with nil => R | cons (r, v) l' => regupd (wf_chain l' R) r v end.
Fixpoint wf_look (l : list (reg * word)) (r : reg) : option word :=
  match l with nil => None | cons (r', v) l' => if bv_eqb r r' then Some v else wf_look l' r end.
Lemma wf_getr_chain : ltac2:(zQ "h00!h9!jc!l9!n6!ra!s1!s8!t0!t7!te!hg8!hh1!hl7!hm3!hme!hn3>1l@1$7@2$8@1$1@1$0#5@1$1@1$0#k0>1R@2$b@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>0@3$3$5@3$a@1$0#5^1@3$e@1$0#5ZKv$9@2$f@1$0#5Z$6@3$3@1$1@1$0#k0@2$4@2$c^4^3^2M2\1x@1$2@1$1@1$0#k0@1$1@1$0#k0@2$d^4^2\1v@1$1@1$0#k0^1@2$4^3^2").
Proof.
  induction l as [|[r' v] l IH]; intros R r Hr; cbn [wf_chain wf_look]; [reflexivity|].
  assert (Hr0 : r <> 0). { intros E. rewrite E in Hr. rewrite XPropExec.bv_eqb_refl in Hr. discriminate Hr. }
  destruct (bv_eqb r r') eqn:E.
  - assert (r = r') as ->. { apply bv_eq. unfold bv_eqb in E. apply Z.eqb_eq in E. exact E. }
    apply XPropExec.getr_same. exact Hr0.
  - rewrite XPropExec.getr_other. { apply IH. exact Hr. }
    intros E2. rewrite E2 in E. rewrite XPropExec.bv_eqb_refl in E. discriminate E.
Qed.
Ltac wf_chain_list RS := lazymatch RS with regupd ?R' ?r' ?v => let l := wf_chain_list R' in constr:(cons (r', v) l) | _ => constr:(@nil (reg * word)) end.
Ltac wf_chain_base RS := lazymatch RS with regupd ?R' _ _ => wf_chain_base R' | _ => RS end.
Ltac wf_find RS r := lazymatch RS with
  | regupd ?R' ?r' ?v => let b := eval vm_compute in (bv_eqb r r') in
      lazymatch b with true => v | false => wf_find R' r end
  | _ => constr:(getr RS r) end.
Ltac wf_gres_one :=
  match goal with
  | |- context [getr (regupd ?R0 ?r' ?v0) ?r] =>
      let RS := constr:(regupd R0 r' v0) in
      let z := eval vm_compute in (bv_eqb r 0) in
      lazymatch z with
      | true => change (getr RS r) with (Z_to_bv 64 0)
      | false =>
          let l := wf_chain_list RS in let B := wf_chain_base RS in
          let val := wf_find RS r in
          let H := fresh "gH" in
          pose proof (wf_getr_chain l B r (@eq_refl bool false) : getr RS r = val) as H;
          rewrite H; clear H
      end
  end.
Ltac gres_old :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ].
Ltac gres :=
  repeat wf_gres_one;
  lazymatch goal with |- context [getr (regupd _ _ _) _] => gres_old | _ => idtac end;
  lazymatch goal with |- context [getr _ 0%bv] => rewrite ?getr_zero | _ => idtac end.
Section FPX_1. Context {fx : XPropExec.FPState}.


(* [comment removed for export] *)
Lemma v_add_0_r : ltac2:(zQ "50!h9!jc!n6!hna!ho2>1x@1$1@1$0#k0@3$2@1$1@1$0#k0@2$3^1@2$4@1$0#k0Z^1").
Proof.
  intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_r. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

Lemma v_add_0_l : ltac2:(zQ "50!h9!jc!n6!hna!ho2>1x@1$1@1$0#k0@3$2@1$1@1$0#k0@2$3@2$4@1$0#k0Z^1^1").
Proof.
  intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_l. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.
End FPX_1.


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
Ltac vnorm := gres; imm_norm;
  lazymatch goal with |- context [v_addi _ 0%Z] => rewrite ?v_addi_0 | _ => idtac end;
  lazymatch goal with |- context [v_add _ (Z_to_bv 64 0)] => rewrite ?v_add_0_r | _ => idtac end;
  lazymatch goal with |- context [v_add (Z_to_bv 64 0) _] => rewrite ?v_add_0_l | _ => idtac end;
  vals_lit.

(* [comment removed for export] *)
Ltac stepn F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
  | _ => stepi F D; vnorm
  end.

(* [comment removed for export] *)

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

(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
