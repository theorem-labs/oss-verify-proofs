(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep AKitIn AKitRV.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~hf7v_sltiu46Stdlib6ZArith6BinInt1Zm82le35stdpp9bitvectorbdefinitionso5bbv_unsigned37Corelib4Init5Logicr03and01Zo52bvhf6v_sltu37Corelib4Init9Datatypestb4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~va3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hje4cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~ho25asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hs68ro_cellsm83addm86of_nattb6length79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB7AKitSeg~~~~~~ii57cond_ror02or3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsin3cwrite_to_memhjeacells_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~is82wam83powr02eqm84landm82ltm83oppo57Z_to_bvo59bv_signed" s.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
(* [comment removed for export] *)
Local Ltac addr_diff E A ::=
  lazymatch A with
  | E => constr:(0%Z)
  | _ =>
    match E with
    | Z.add ?X ?c1 =>
        let c1 := zlit c1 in
        lazymatch A with
        | Z.add X ?c2 => let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
        | X => c1
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    | _ =>
        lazymatch A with
        | Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    end
  end.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Lemma sltiu_range : ltac2:(zQ "70!h9!le!o0!q2!s4!sa!sd>1x@1$6@1$0#k0>3imm$5@2$4@2$2Z@2$3@1$0#k0@2$1^2^1@2$2@2$3@1$0#k0@2$1^2^1+1").
  Proof. intros x imm. unfold v_sltiu. destruct (bv_unsigned x <? bv_wrap 64 imm); rewrite unsigned_lit by lia; lia. Qed.
  Lemma sltu_range : ltac2:(zQ "60!h9!t2!o0!sd!q2!s4>1x@1$3@1$0#k0>1y@1$3@1$0#k0@2$5@2$2Z@2$4@1$0#k0@2$1^2^1@2$2@2$4@1$0#k0@2$1^2^1+1").
  Proof. intros x y. rewrite v_sltu_b2z. destruct (bv_unsigned x <? bv_unsigned y); cbn [Z.b2z]; rewrite unsigned_lit by lia; lia. Qed.
  (* [comment removed for export] *)
  Ltac sltiu_bounds :=
    repeat match goal with
    | |- context [bv_unsigned (v_sltiu ?a ?b)] =>
        pose proof (sltiu_range a b); let u := fresh "u" in set (u := bv_unsigned (v_sltiu a b)) in *; clearbody u
    | |- context [bv_unsigned (v_sltu ?a ?b)] =>
        pose proof (sltu_range a b); let u := fresh "u" in set (u := bv_unsigned (v_sltu a b)) in *; clearbody u
    end.
  Ltac fin_arith ::= first [ lia | rewrite ?unsigned_lit by lia; lia | sltiu_bounds; rewrite ?unsigned_lit by lia; lia ].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cond_ro : ltac2:(zQ "40!v3!sa!hj8!hna>1cP>1m$2>1A$1>2cs@1$0$3P") := ltac2:(zQ "60!v3!sa!hrd!hj8!hna!ig1\1cP\1m$3\1A$1\2cs@1$0$4>0^4@4$5$2^4^3^2").
  Lemma cond_ro_frame : ltac2:(zQ "h00!o0!h9!igd!ih3!sd!ihc!v3!sa!im3!ime!iqa!hj8!hna!ira!jg2!jg8>1cP>1m$b>1A$7>2cs@1$6$c>1a$7>2bs@1$6@1$4@1$1#8>0@4$8^6^5^4^3>0@2$0Z^3>0@2$0@2$2^4@1$3@2$5@1$4@1$1#8^3@2$f+2+k0>0@2$9@2$0@2$2^7@1$3@1$d^6^5@2$0@2$2^5@1$3@2$5@1$4@1$1#8^4^7@4$8^a@3$a^9@1$e^6^5^8^7").
  Proof. intros c m A cs a bs H Ha Hb Hd Hc. apply ro_cells_frame; auto. Qed.
  Ltac transport_cond_ro segs m a bs :=
    repeat match goal with
    | H : cond_ro ?c m ?A2 ?cs2 |- _ =>
        first [ apply (cond_ro_frame c m A2 cs2 a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
              | idtac "note: dropping conditional input fact" H; clear H ]
    end.
  Ltac arm_inputs :=
    repeat match goal with
    | H : cond_ro ?c ?m ?A ?cs |- _ =>
        let Hc := fresh "Hc" in assert (Hc : c) by lia; unfold cond_ro in H; specialize (H Hc); clear Hc
    end.
  (* [comment removed for export] *)
  Ltac run_to stops ::=
    repeat (lazymatch goal with
            | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                lazymatch stops with
                | context [pc] => fail
                | _ => first [ st1b | arm_inputs; st1b ]; gen_data
                end
            end).

  Ltac lit_eq EQ := match type of EQ with _ = ?rhs => let v := eval vm_compute in rhs in replace rhs with v in EQ by (vm_compute; reflexivity) end.

  Lemma land255_small : ltac2:(zQ "60!sa!s4!jge!jh3!o0!jha>1x$0>0@2$1@2$4Z^1@2$5^1+hg0@3$2$0@2$3^2+vf^2").
  Proof. intros x Hx. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
  Ltac norm_lits :=
    repeat match goal with
    | |- context [Z_to_bv 64 (Z.land ?a ?b)] =>
        let a' := zlit a in let b' := zlit b in let v := eval vm_compute in (Z.land a' b') in
        change (Z_to_bv 64 (Z.land a b)) with (Z_to_bv 64 v)
    | |- context [Z_to_bv 64 (Z.lor ?a ?b)] =>
        let a' := zlit a in let b' := zlit b in let v := eval vm_compute in (Z.lor a' b') in
        change (Z_to_bv 64 (Z.lor a b)) with (Z_to_bv 64 v)
    | |- context [Z_to_bv 64 (Z.shiftl ?a ?b)] =>
        let a' := zlit a in let b' := zlit b in let v := eval vm_compute in (Z.shiftl a' b') in
        change (Z_to_bv 64 (Z.shiftl a b)) with (Z_to_bv 64 v)
    | |- context [Z_to_bv 64 (Z.shiftr ?a ?b)] =>
        let a' := zlit a in let b' := zlit b in let v := eval vm_compute in (Z.shiftr a' b') in
        change (Z_to_bv 64 (Z.shiftr a b)) with (Z_to_bv 64 v)
    | |- context [Z_to_bv 64 (Z.land ?a 255)] => rewrite (land255_small a) by lia
    end.
  Ltac run_to stops ::=
    repeat (lazymatch goal with
            | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                lazymatch stops with
                | context [pc] => fail
                | _ => first [ st1b | arm_inputs; st1b ]; norm_lits; gen_data
                end
            end).
  Lemma signed_lit : ltac2:(zQ "a0!h9!sa!jg8!s4!jge!o0!jha!jhf!ji5!jif>1z$1>0@2$3@2$5@1$7@2$2+2+jf^1@2$6^1@2$2+2+jf@3$4$1@2$9@1$0#k0@2$8@1$0#k0^2^2").
  Proof.
    intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
  Qed.
  (* [comment removed for export] *)
  Ltac box_ugly K ::=
    try (rewrite !signed_lit in K by lia);
    lazymatch type of K with
    | context [Z.lor _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.land _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.shiftl _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.shiftr _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.modulo _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | _ => idtac
    end.
  (* [comment removed for export] *)
  Ltac fin_atom ::=
    first [ eassumption
          | reflexivity
          | lazymatch goal with
            | |- @eq Z _ _ => rv_cbv; fin_arith
            | |- (_ <= _)%Z => rv_cbv; fin_arith
            | |- (_ < _)%Z => rv_cbv; fin_arith
            | |- not _ => rv_cbv; fin_arith
            | |- @eq _ _ _ => rv_cbv; first [ reflexivity | eassumption | f_equal; lia | apply bv_eq; rewrite ?unsigned_lit by lia; lia
                                             | apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity ]
            | |- _ => rv_cbv; first [ reflexivity | eassumption ]
            end ].
(* [comment removed for export] *)
