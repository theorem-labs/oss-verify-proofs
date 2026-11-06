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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import BJFrame HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJRep BJHeap BJIface BJIfaceEsc BJEhTabs BJKitW BJKitVS BJKitIn BJKitRV BJKitSeg BJArithU.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU7BJKitRV~~~~~~i22rv35stdpp9bitvectorbdefinitionsm52bv37Corelib4Init5Logico72eqo73andm57Z_to_bvi23rs0i23rs1i24rs10i24rs11i23rs2i23rs3i23rs4i23rs5i23rs6i23rs8i23rs9i23rsp37Corelib4Init9Datatypesva4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~hh93mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hmb4cellva4conshmb2C8m5bbv_unsigned46Stdlib6ZArith6BinInt1Zhsa3addhsa4lxorva3nilhmb2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hvd8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~ik45rsegshmb2C4hmb2C179OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ip62b8hsa4landhsa2lehsa2lthsa3powo72orhsa6modulohsa3opphsa3subhsa3lorhsa6shiftrm57bv_wrap" s.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs; transport_cond_ro segs m a bs.
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
  Definition ucore : ltac2:(zQ "40!h9!hf!m0!o2>1r$2>3sp'@1$3@1$0#k0>1c$1P") := ltac2:(zQ "h30!h9!o2!pb!q0!q6!hf!r0!r6!rc!s3!sa!t0!t6!tc!u2!u8!ue!v4!m0\1r$h2\3sp'@1$1@1$0#k0\1c$5@2$3@3$2@1$1@1$0#k0@1$h1^3^2@2$3@3$2@1$1@1$0#k0@1$e^3@2$4@1$0#k0^1@2$3@3$2@1$1@1$0#k0@1$6^3@2$4@1$0#k0-og1@2$3@3$2@1$1@1$0#k0@1$7^3@2$4@1$0#k0-5@2$3@3$2@1$1@1$0#k0@1$a^3@2$4@1$0#k0-ugg0@2$3@3$2@1$1@1$0#k0@1$b^3@2$4@1$0#k0+n5@2$3@3$2@1$1@1$0#k0@1$c^3@2$4@1$0#k0+b@2$3@3$2@1$1@1$0#k0@1$d^3@2$4@1$0#k0+a@2$3@3$2@1$1@1$0#k0@1$f^3@2$4@1$0#k0+1@2$3@3$2@1$1@1$0#k0@1$h0^3@2$4@1$0#k0+5@2$3@3$2@1$1@1$0#k0@1$8^3@2$4@1$0#k0+9@3$2@1$1@1$0#k0@1$9^3@2$4@1$0#k0+lc").
  Ltac open_ucore PC := box_post; destruct PC as (?C1 & ?C2 & ?C3 & ?C4 & ?C5 & ?C6 & ?C7 & ?C8 & ?C9 & ?C10 & ?C11 & ?C12).

  (* [comment removed for export] *)
  Definition uframe : ltac2:(zQ "50!h9!o2!hf!hh2!hm4>1m$4>3sp'@1$1@1$0#k0>2j8@1$3@1$1@1$0#8>3k16@1$1@1$0#k0>3tmp@1$1@1$0#k0>2pa@1$1@1$0#k0>2ta@1$1@1$0#k0>1e$2>3isk$2P") := ltac2:(zQ "h00!h9!hq7!hqf!hr6!q6!o2!hrc!hf!hu2!hu9!hh2!hv1!hv7!ij8!hm4!io1\1m$e\3sp'@1$5@1$0#k0\2j8@1$a@1$5@1$0#8\3k16@1$5@1$0#k0\3tmp@1$5@1$0#k0\2pa@1$5@1$0#k0\2ta@1$5@1$0#k0\1e$7\3isk$7@4$d$f^9@2$6@1$0#k0^8@3$2$1@2$cN8^7@3$2$1@1$3^6@3$2$1@1$3^5@3$2$1@1$3@2$4@1$0#k0+vvvd@3$2$1@1$3@2$4@1$0#k0Z@3$2$1@1$3@2$4@1$0#k0@2$9^1+d@3$2$1@1$3@2$4@1$0#k0+vvvvvvvvvsqgikg0@3$2$1@1$3@2$4@1$0#k0@2$8@2$6@1$0#k0^4+l8@3$2$1@1$3@2$4@1$0#k0+nvvvvvve@3$2$1@1$3@2$4@1$0#k0^2@3$2$1@1$3@2$4@1$0#k0^1@3$2$1@1$3^3@3$2$1@1$3^4@3$2$1@1$3@2$4@1$0#k0@2$9@2$8@2$6@1$0#k0^8+n0+vvvvvvvvvvvvvvvf@1$b$1").
  (* [comment removed for export] *)
  Definition usize : ltac2:(zQ "40!h9!hf!hm4!o2>1m$2>3sp'@1$3@1$0#k0>2sz$1P") := ltac2:(zQ "d0!h9!hq7!hqf!hv1!hf!hr6!ij8!hm4!io1!hu2!q6!o2!hrc\1m$7\3sp'@1$b@1$0#k0\2sz$4@4$6$8^3@2$9@2$c@1$0#k0^2+hn0@3$2$1@1$5@2$a@1$0#k0^1@1$3$1").
  (* [comment removed for export] *)
  Definition ucells : ltac2:(zQ "50!h9!o2!hh2!hf!hm4>1m$4>2pa@1$1@1$0#k0>1e$3>2sc@1$2@1$1@1$0#8>3u1w@1$1@1$0#k0>3u2w@1$1@1$0#k0>4pad7@1$2@1$1@1$0#8>2v1@1$1@1$0#k0>2v2@1$1@1$0#k0>2v3@1$1@1$0#k0P") := ltac2:(zQ "h30!h9!hq7!hqf!o2!hv1!hr6!ij8!io1!hu2!hrc!q0!hh2!ioa!hv7!hf!ip0!it1!hm4!q6\1m$h1\2pa@1$3@1$0#k0\1e$e\2sc@1$b@1$3@1$0#8\3u1w@1$3@1$0#k0\3u2w@1$3@1$0#k0\4pad7@1$b@1$3@1$0#8\2v1@1$3@1$0#k0\2v2@1$3@1$0#k0\2v3@1$3@1$0#k0@2$a@4$6$7^a@2$8@2$9@1$0#k0^9+q0@3$2$1@2$dN8^7@3$2$1@1$c^6@3$2$1@1$c^5@1$4$1@2$a@4$6$7^a@2$8@2$9@1$0#k0^9+r0@3$2$1@1$f@1$h0Z@3$2$1@2$dN7^4@1$4$1@2$a@4$6$7^a@2$8@2$9@1$0#k0^9+r8@3$2$1@1$5@2$h2@1$0#k0^8@1$4$1@4$6$7^a@2$8@2$9@1$0#k0^9+l8@3$2$1@1$5^3@3$2$1@1$5^2@3$2$1@1$5^1@1$4$1").
  Ltac open_ucells PM := box_post; destruct PM as (SCR & MORE & END & EC).
  (* [comment removed for export] *)
  Definition uctx {HCEIL : HeapCeil} (sp' pa ta : word) (lo e : Z) : Prop :=
    hceil <= lo /\ lo <= bv_unsigned sp' /\ bv_unsigned sp' + 480 <= bv_unsigned ta /\ bv_unsigned ta + 8 <= bv_unsigned pa /\
    bv_unsigned pa + 280 <= 2^64 /\ e <= hceil.
  Ltac open_uctx PX := box_post; destruct PX as (CEIL & ROOM & TA1 & TA2 & A0HI & EH).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma land223_range : ltac2:(zQ "50!it7!itf!q0!hf!iu5>1x$3>0@2$1Z^1@2$2@2$1Z@2$0^2+tf@2$4@2$0^2+tf+hg0").
  Proof. intros x Hx. rewrite Z.land_comm. apply (land_lt_pow2 223 x 8); lia. Qed.
  Lemma land255_range : ltac2:(zQ "50!it7!itf!q0!hf!iu5>1x$3>0@2$1Z^1@2$2@2$1Z@2$0^2+vf@2$4@2$0^2+vf+hg0").
  Proof. intros x Hx. rewrite Z.land_comm. apply (land_lt_pow2 255 x 8); lia. Qed.
  Ltac wrange w := try (let H := fresh "WR" in pose proof (bv_unsigned_in_range _ w) as H; unfold bv_modulus in H;
                        change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in H).
  Ltac zpos x := lazymatch x with bv_unsigned ?w => wrange w | _ => idtac end.
  Ltac pose_byte_ranges inb q :=
    let go k := let H := fresh "BR" in pose proof (bv_unsigned_in_range _ (inb (q + k)%Z)) as H; unfold bv_modulus in H;
                change (2 ^ Z.of_N 8)%Z with 256%Z in H in
    go 0%Z; go 1%Z; go 2%Z; go 3%Z; go 4%Z; go 5%Z; go 6%Z; go 7%Z; go 8%Z; go 9%Z; go 10%Z; go 11%Z.
  Lemma unwrap_s : ltac2:(zQ "90!q0!hf!itf!iu5!iub!iv2!hu2!iv7!jg1>1P>0$1P>1x$1>0@2$0@2$2@1$8@2$4+2+jf^1@2$3^1@2$4+2+jf>0@1^3@2$7^2+hggggggggggggggg0@2$5@2$0@2$2Z^3@1^4^3@2$0@2$3^3Z@1^4@2$6^3+hggggggggggggggg0").
  Proof.
    intros P x R HP. destruct (Z_lt_le_dec x 0) as [L|L].
    - right. split; [lia|]. replace (x + 18446744073709551616) with (x mod 18446744073709551616); [exact HP|].
      rewrite <- (Z.mod_add x 1 18446744073709551616) by lia. rewrite Z.mod_small by lia. lia.
    - left. split; [lia|]. rewrite Z.mod_small in HP by lia. exact HP.
  Qed.
  Lemma unwrap_u : ltac2:(zQ "70!q0!hf!itf!iu5!iv2!iv7!jg8>1P>0$1P>1x$1>0@2$0@2$2Z^1@2$3^1+iggggggggggggggg0>0@1^3@2$5^2+hggggggggggggggg0@2$4@2$0@2$3^3+hggggggggggggggg0@1^4^3@2$0@2$2+hggggggggggggggg0^3@1^4@2$6^3+hggggggggggggggg0").
  Proof.
    intros P x R HP. destruct (Z_lt_le_dec x 18446744073709551616) as [L|L].
    - left. split; [lia|]. rewrite Z.mod_small in HP by lia. exact HP.
    - right. split; [lia|]. replace (x - 18446744073709551616) with (x mod 18446744073709551616); [exact HP|].
      rewrite <- (Z.mod_add x (-1) 18446744073709551616) by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  Ltac unwrap_cmp K :=
    repeat match type of K with
    | context [(?x mod 18446744073709551616)%Z] =>
        pattern (x mod 18446744073709551616)%Z in K;
        first [ apply (unwrap_s _ x ltac:(lia)) in K | apply (unwrap_u _ x ltac:(lia)) in K ];
        cbv beta in K
    end.
  Lemma land223_255 : ltac2:(zQ "30!it7!hf!pb>1x$1@3$2$1@2$0^1+tf@2$0@2$0^1+vf+tf").
  Proof. intros x. rewrite <- Z.land_assoc. reflexivity. Qed.
  Lemma lor_m1_l : ltac2:(zQ "60!hf!q0!pb!itf!jgf!iu5>1y$0>0@2$1@2$3Z^1@2$5^1+hggggggggggggggg0@3$2$0@2$4+vvvvvvvvvvvvvvvf^2+vvvvvvvvvvvvvvvf").
  Proof.
    intros y Hy. apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
    destruct (Z_lt_le_dec n 64) as [L|L].
    - replace 18446744073709551615 with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_low by lia. reflexivity.
    - replace 18446744073709551615 with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_high by lia.
      assert (LG : Z.log2 y < 64).
      { destruct (Z.eq_dec y 0) as [->|NZ]. cbn; lia. apply (proj1 (Z.log2_lt_pow2 y 64 ltac:(lia))). lia. }
      rewrite (Z.bits_above_log2 y n); [reflexivity| lia| lia].
  Qed.
  Lemma lor_m1_r : ltac2:(zQ "60!hf!q0!pb!itf!jgf!iu5>1x$0>0@2$1@2$3Z^1@2$5^1+hggggggggggggggg0@3$2$0@2$4^2+vvvvvvvvvvvvvvvf+vvvvvvvvvvvvvvvf").
  Proof. intros x Hx. rewrite Z.lor_comm. apply lor_m1_l. exact Hx. Qed.
  Lemma lor_bound32 : ltac2:(zQ "51!q0!itf!iu5!hf!jgf&@2$0@2$1Z^2@2$2^2+hggggggg0>1x$3>1y$3>0~0>0~0@2$0@2$1Z@2$4^4^3@2$2@2$4^4^3+hggggggg0").
  Proof. intros x y Hx Hy. apply (lor_lt_pow2 x y 32); assumption. Qed.
  Lemma shiftr_small0 : ltac2:(zQ "70!hf!itf!q0!pb!iu5!iub!jh6>1x$0>1n$0>0@2$1Z^1>0@2$2@2$1Z^3@2$4^3@2$5+2^2@3$3$0@2$6^4^3Z").
  Proof. intros x n Hn Hx. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
  Lemma wrap32_small : ltac2:(zQ "70!hf!q0!pb!h9!itf!iu5!ji0>1x$0>0@2$1@2$4Z^1@2$5^1+hggggggg0@3$2$0@2$6@1$3#i0^2^2").
  Proof. intros x Hx. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
  Definition hxeq : ltac2:(zQ "10!hf>1a$0>1b$0P") := ltac2:(zQ "20!hf!pb\1a$0\1b$0@3$1$0^2^1").
  Ltac hx_name_b t :=
    let b := fresh "bx" in let E := fresh "EQ" in
    pose proof (eq_refl t : hxeq t t) as E; set (b := t) in |- *; change (hxeq t b) in E; clearbody b.
  Ltac hx_name_h t :=
    let b := fresh "hx" in let E := fresh "EQ" in
    pose proof (eq_refl t : hxeq t t) as E; set (b := t) in |- *; change (hxeq t b) in E; clearbody b.
  Ltac hx_reuse R :=
    match goal with
    | E : hxeq ?t ?v |- _ => lazymatch R with context [t] => unfold hxeq in E; rewrite !E; change (hxeq t v) in E end
    end.
  Ltac hex_norm1 R :=
    first
    [ hx_reuse R
    | match R with
      | context [bv_unsigned (v_sltiu ?a ?b)] =>
          let u := fresh "u" in let H := fresh "U" in
          pose proof (sltiu_range a b) as H; set (u := bv_unsigned (v_sltiu a b)) in *; clearbody u
      | context [bv_unsigned (v_sltu ?a ?b)] =>
          let u := fresh "u" in let H := fresh "U" in
          pose proof (sltu_range a b) as H; set (u := bv_unsigned (v_sltu a b)) in *; clearbody u
      | context [Z.land ?x 255] =>
          first [ rewrite (land255_small x) by lia
                | zpos x; let H := fresh "BX" in pose proof (land255_range x ltac:(lia)) as H;
                  hx_name_b (Z.land x 255);
                  lazymatch goal with E : hxeq (Z.land x 255) ?b |- _ => unfold hxeq in E; rewrite E in H; change (hxeq (Z.land x 255) b) in E end ]
      | context [Z.land ?x 223] =>
          first [ let H := fresh "HX" in pose proof (land223_range x ltac:(lia)) as H;
                  first [ assert (x < 256)%Z by lia | fail 1 ];
                  match goal with T : (x < 256)%Z |- _ => clear T end;
                  hx_name_h (Z.land x 223);
                  lazymatch goal with E : hxeq (Z.land x 223) ?b |- _ => unfold hxeq in E; rewrite E in H; change (hxeq (Z.land x 223) b) in E end
                | rewrite (land223_255 x) ]
      | context [Z.lor 18446744073709551615 ?y] => rewrite (lor_m1_l y) by lia
      | context [Z.lor ?x 18446744073709551615] => rewrite (lor_m1_r x) by lia
      | context [Z.lor ?x ?y] =>
          let H := fresh "OR" in pose proof (lor_bound32 x y ltac:(lia) ltac:(lia)) as H;
          let o := fresh "ox" in set (o := Z.lor x y) in *; clearbody o
      | context [bv_wrap 32 ?y] => rewrite (wrap32_small y) by lia
      | context [bv_swrap 32 ?y] => rewrite (BJArithU.swrap32_small y) by lia
      | context [Z.shiftr ?x ?n] =>
          first [ rewrite (shiftr_small0 x n) by lia
                | first [ assert (0 <= x < 1099511627776)%Z by lia | fail 1 ];
                  match goal with T : (0 <= x < 1099511627776)%Z |- _ => clear T end;
                  rewrite (Z.shiftr_div_pow2 x n) by lia;
                  let v := eval vm_compute in (2^n)%Z in change (2^n)%Z with v ]
      | context [Z.shiftl ?x ?n] =>
          first [ assert (-1099511627776 <= x < 1099511627776)%Z by lia | fail 1 ];
          match goal with T : (-1099511627776 <= x < 1099511627776)%Z |- _ => clear T end;
          rewrite (Z.shiftl_mul_pow2 x n) by lia;
          let v := eval vm_compute in (2^n)%Z in change (2^n)%Z with v
      end ].
  Ltac hex_norm :=
    repeat lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => hex_norm1 R end.
  Ltac box_ugly K ::=
    try (rewrite !signed_lit in K by lia);
    try unwrap_cmp K;
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
                                             | lazymatch goal with |- Z_to_bv _ ?x = Z_to_bv _ ?y => is_Zlit x; is_Zlit y end;
                                               apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity ]
            | |- _ => rv_cbv; first [ reflexivity | eassumption ]
            end ].

  Ltac run_to stops ::=
    repeat (lazymatch goal with
            | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                lazymatch stops with
                | context [pc] => fail
                | _ => first [ st1b | arm_inputs; st1b ]; norm_lits; hex_norm; gen_data
                end
            end).
  Ltac prune_or K tac ::=
    lazymatch type of K with
    | boxP _ => tac
    | _ => first [ exfalso; try rewrite BJArithU.not64 in K by lia; lia | tac ]
    end.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac print_hyps ::=
    try (match goal with H : ?T |- _ =>
           lazymatch T with
           | rw_cells _ _ _ _ => idtac "  " H ":" T
           | ro_cells _ _ _ _ => idtac "  " H ":" T
           | @eq Z _ _ => idtac "  " H ":" T
           | Z.lt _ _ => idtac "  " H ":" T
           | Z.le _ _ => idtac "  " H ":" T
           | not _ => idtac "  " H ":" T
           | _ /\ _ => idtac "  " H ":" T
           | _ \/ _ => idtac "  " H ":" T
           | munch _ _ _ => idtac "  " H ":" T
           | stk _ _ _ _ => idtac "  " H ":" T
           | _ => fail
           end; fail end).

  Ltac seg_begin r :=
    intro_rv r; subst; unfold uframe, usize in *; unfold seg_post, ucore, uframe, usize, ucells; hide_post;
    lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP end;
    hcb.

  Ltac seg_unfold ::=
    lazymatch goal with
    | |- ucore _ _ _ => unfold ucore
    | |- uframe _ _ _ _ _ _ _ _ _ => unfold uframe
    | |- usize _ _ _ => unfold usize
    | |- ucells _ _ _ _ _ _ _ _ _ _ => unfold ucells
    end.
(* [comment removed for export] *)
