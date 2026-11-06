(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJRep BJKitW BJKitVS BJKitIn BJKitRV.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~i23mem35stdpp9bitvectorbdefinitionsn32bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~p54cell46Stdlib6ZArith6BinInt1Zt82lt37Corelib4Init9Datatypesv54consv53nilp52C179OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hhf8ro_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~hm65rsegst83addt82le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~hr77v_sltiun3bbv_unsigned37Corelib4Init5Logicigf3andhr76v_sltuv54listt86of_natv56length79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU8BJKitSeg~~~~~~ikd7cond_roigf2or3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsipdcwrite_to_memp5acells_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~iv12wat83powigf2eqt84landt83oppn37Z_to_bvn39bv_signed" s.
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
  Definition pinput : ltac2:(zQ "40!h9!hc!md!p0>1m$2>1q$0>1e$0>3inb>0$0@1$3@1$1#8P") := ltac2:(zQ "d0!h9!t1!v0!hgd!hh4!hc!hha!hla!md!hq3!hqc!hr2!p0\1m$8\1q$0\1e$0\3inb>0$0@1$c@1$5#8>1x$0>0@2$b^4^1>0@2$2^2^4>0@2$2^3@2$a^6+c@4$7$9^8^4@3$3$1@1$6@1^5^4@1$4$1").

  (* [comment removed for export] *)

  Lemma sltiu_range : ltac2:(zQ "70!hc!hv6!hr2!ig1!ii3!h9!p0>1x@1$6@1$0#k0>3imm$5@2$4@2$2Z@2$3@1$0#k0@2$1^2^1@2$2@2$3@1$0#k0@2$1^2^1+1").
  Proof. intros x imm. unfold v_sltiu. destruct (bv_unsigned x <? bv_wrap 64 imm); rewrite unsigned_lit by lia; lia. Qed.
  Lemma sltu_range : ltac2:(zQ "60!hc!iia!hr2!p0!ig1!ii3>1x@1$3@1$0#k0>1y@1$3@1$0#k0@2$5@2$2Z@2$4@1$0#k0@2$1^2^1@2$2@2$4@1$0#k0@2$1^2^1+1").
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
  Definition cond_ro : ltac2:(zQ "40!ij4!h9!t1!md>1cP>1m$3>1A$1>2cs@1$0$2P") := ltac2:(zQ "60!ij4!h9!t1!hla!md!hq3\1cP\1m$4\1A$1\2cs@1$0$2>0^4@4$3$5^4^3^2").
  Lemma cond_ro_frame : ltac2:(zQ "h00!hr2!hc!hqc!ijb!p0!ik4!ij4!h9!ioc!ip7!it4!t1!iu4!jib!md!jj1>1cP>1m$e>1A$7>2cs@1$6$b>1a$7>2bs@1$6@1$4@1$1#8>0@4$8^6^5^4^3>0@2$0Z^3>0@2$0@2$2^4@1$3@2$5@1$4@1$1#8^3@2$f+2+k0>0@2$9@2$0@2$2^7@1$3@1$c^6^5@2$0@2$2^5@1$3@2$5@1$4@1$1#8^4^7@4$8^a@3$a^9@1$d^6^5^8^7").
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
  Ltac pose_cond_inputs INB q e :=
    try pose proof ((fun H : q < e => INB q ltac:(lia) H ltac:(lia)) : cond_ro (q < e) _ q _) as IR0;
    try pose proof ((fun H : q + 1 < e => INB (q + 1) ltac:(lia) H ltac:(lia)) : cond_ro (q + 1 < e) _ (q + 1) _) as IR1;
    try pose proof ((fun H : q + 2 < e => INB (q + 2) ltac:(lia) H ltac:(lia)) : cond_ro (q + 2 < e) _ (q + 2) _) as IR2;
    try pose proof ((fun H : q + 3 < e => INB (q + 3) ltac:(lia) H ltac:(lia)) : cond_ro (q + 3 < e) _ (q + 3) _) as IR3;
    try pose proof ((fun H : q + 4 < e => INB (q + 4) ltac:(lia) H ltac:(lia)) : cond_ro (q + 4 < e) _ (q + 4) _) as IR4;
    try pose proof ((fun H : q + 5 < e => INB (q + 5) ltac:(lia) H ltac:(lia)) : cond_ro (q + 5 < e) _ (q + 5) _) as IR5;
    try pose proof ((fun H : q + 6 < e => INB (q + 6) ltac:(lia) H ltac:(lia)) : cond_ro (q + 6 < e) _ (q + 6) _) as IR6;
    try pose proof ((fun H : q + 7 < e => INB (q + 7) ltac:(lia) H ltac:(lia)) : cond_ro (q + 7 < e) _ (q + 7) _) as IR7;
    try pose proof ((fun H : q + 8 < e => INB (q + 8) ltac:(lia) H ltac:(lia)) : cond_ro (q + 8 < e) _ (q + 8) _) as IR8;
    try pose proof ((fun H : q + 9 < e => INB (q + 9) ltac:(lia) H ltac:(lia)) : cond_ro (q + 9 < e) _ (q + 9) _) as IR9;
    try pose proof ((fun H : q + 10 < e => INB (q + 10) ltac:(lia) H ltac:(lia)) : cond_ro (q + 10 < e) _ (q + 10) _) as IR10;
    try pose proof ((fun H : q + 11 < e => INB (q + 11) ltac:(lia) H ltac:(lia)) : cond_ro (q + 11 < e) _ (q + 11) _) as IR11;
    arm_inputs.
  (* [comment removed for export] *)
  Ltac inputs INB q e tac := pose_cond_inputs INB q e; tac.
  Ltac run_to stops ::=
    repeat (lazymatch goal with
            | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                lazymatch stops with
                | context [pc] => fail
                | _ => first [ st1b | arm_inputs; st1b ]; gen_data
                end
            end).


  Lemma land255_small : ltac2:(zQ "60!h9!ii3!jj7!jjd!hr2!v0>1x$0>0@2$1@2$4Z^1@2$5^1+hg0@3$2$0@2$3^2+vf^2").
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
  Lemma signed_lit : ltac2:(zQ "a0!hc!h9!jj1!ii3!jj7!hr2!v0!jk4!jka!jl4>1z$1>0@2$3@2$5@1$7@2$2+2+jf^1@2$6^1@2$2+2+jf@3$4$1@2$9@1$0#k0@2$8@1$0#k0^2^2").
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
