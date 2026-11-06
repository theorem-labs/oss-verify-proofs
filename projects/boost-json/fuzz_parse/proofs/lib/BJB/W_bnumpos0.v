(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsObj AsStack0 AsWalk N8Kit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep AXpres AKitChk AKitCells AKitIn AKitRV AKitSeg W_bnum0 W_bnumneg0.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import N8Store.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos46Stdlib6ZArith6BinInt1Zhf2lt35stdpp9bitvectorbdefinitionsjc7Z_to_bv37Corelib4Init5Logicm33and01Zhf2lehf3powm32eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~p06v_sltujc2bvp07v_sltiu" s.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs; try transport_cond_ro segs m a bs.
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
Lemma v_sltu_lit_true : ltac2:(zQ "a1!h9!j7!l9!n7!nd!o0!o5!ob!sf!t8&@2$3@2$5Z^2@2$1^2@2$6+2+k0>1a$4>1b$4>0~0>0~0>0@2$1^4^3@3$7@1$9@1$0#k0@2$8@2$2@1$0#k0^5@2$2@1$0#k0^4@2$2@1$0#k0+1").
Proof. intros a b Ha Hb H. rewrite v_sltu_b2z, !unsigned_lit by lia. destruct (Z.ltb_spec0 a b); [reflexivity| lia]. Qed.
Lemma v_sltu_lit_false : ltac2:(zQ "a1!h9!o0!l9!n7!nd!j7!o5!ob!sf!t8&@2$3@2$1Z^2@2$5^2@2$6+2+k0>1a$4>1b$4>0~0>0~0>0@2$1^3^4@3$7@1$9@1$0#k0@2$8@2$2@1$0#k0^5@2$2@1$0#k0^4@2$2@1$0#k0Z").
Proof. intros a b Ha Hb H. rewrite v_sltu_b2z, !unsigned_lit by lia. destruct (Z.ltb_spec0 a b); [lia| reflexivity]. Qed.
Lemma v_sltiu_lit_true : ltac2:(zQ "a1!h9!j7!n7!nd!o0!o5!l9!ob!td!t8&@2$2@2$4Z^2@2$1^2@2$5+2+k0>1a$3>1i$3>0~0>0~0>0@2$1^4^3@3$7@1$9@1$0#k0@2$8@2$6@1$0#k0^5^4@2$6@1$0#k0+1").
Proof.
  intros a i Ha Hi H. rewrite v_sltiu_b2z, unsigned_lit by lia. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite Z.mod_small by lia. destruct (Z.ltb_spec0 a i); [reflexivity| lia].
Qed.
Lemma v_sltiu_lit_false : ltac2:(zQ "a1!h9!o0!n7!nd!j7!o5!l9!ob!td!t8&@2$2@2$1Z^2@2$4^2@2$5+2+k0>1a$3>1i$3>0~0>0~0>0@2$1^3^4@3$7@1$9@1$0#k0@2$8@2$6@1$0#k0^5^4@2$6@1$0#k0Z").
Proof.
  intros a i Ha Hi H. rewrite v_sltiu_b2z, unsigned_lit by lia. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite Z.mod_small by lia. destruct (Z.ltb_spec0 a i); [lia| reflexivity].
Qed.
Ltac norm_s32 ::=
    repeat match goal with
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?a) + bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_2 a b) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?a) - bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_sub a b) by lia
    | |- context [bv_swrap 32 (?k - bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_rsub k b) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) + ?k)] => rewrite (swrap32_of_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) * ?k)] => rewrite (swrap32_mul_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_0 b) by lia
    | |- context [sx32 (Z_to_bv 64 ?b)] => rewrite (sx32_ssmall b) by lia
    | |- context [bv_swrap 32 ?x] => first [rewrite (swrap32_id x) by lia | rewrite (swrap32_id_m64 x) by lia]
    | |- context [Z.lxor ?w 18446744073709551615] => rewrite (lxor_m1_64 w) by lia
    | |- context [bv_unsigned (b8 ?x)] => rewrite (b8_unsigned x) by lia
    | |- context [Z_to_bv 64 (Z.land ?a 1)] => rewrite (land1_small a) by lia
    | |- context [Z_to_bv 64 (Z.land ?a 7)] => rewrite (land7_mod8 a) by lia
    | |- context [sxb (b8 ?v)] => rewrite (sxb_b8_small v) by lia
    | |- context [sx32 (Z_to_bv 64 ?b)] =>
        lazymatch isZcst b with
        | true => let v := eval vm_compute in (bv_swrap 32 b) in
                  replace (sx32 (Z_to_bv 64 b)) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity)
        end
    (* [comment removed for export] *)
    | |- context [v_sltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => first [rewrite (v_sltu_lit_true a b) by lia | rewrite (v_sltu_lit_false a b) by lia]
    | |- context [v_sltiu (Z_to_bv 64 ?a) ?i] => first [rewrite (v_sltiu_lit_true a i) by lia | rewrite (v_sltiu_lit_false a i) by lia]
    | |- context [Z.lxor ?a ?b] =>
        lazymatch isZcst a with true => lazymatch isZcst b with true =>
          let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v end end
    end.

(* [comment removed for export] *)
Ltac achk ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 1063528 => chkjoin 11 1063532   (* [comment removed for export] *)
    | 1063632 => chkjoin 6 1063636   (* [comment removed for export] *)
    | 1063772 => chkjoin 7 1063776   (* [comment removed for export] *)
    | 1063892 => chkjoin 12 1063896   (* [comment removed for export] *)
    | 1063952 => chkjoin 14 1063956   (* [comment removed for export] *)
    | 1064044 => chkjoin 11 1064048   (* [comment removed for export] *)
    | 1064128 => chkjoin 11 1064132   (* [comment removed for export] *)
    | 1064192 => chkjoin 5 1064196   (* [comment removed for export] *)
    | 1064496 => chkjoin 13 1064500   (* [comment removed for export] *)
    | 1064660 => chkjoin 11 1064664   (* [comment removed for export] *)
    | 1064712 => chkjoin 12 1064716   (* [comment removed for export] *)
    | 1064792 => chkjoin 12 1064796   (* [comment removed for export] *)
    | 1064888 => chkjoin 6 1064892   (* [comment removed for export] *)
    | 1065056 => chkjoin 12 1065060   (* [comment removed for export] *)
    | 1065172 => chkjoin 12 1065176   (* [comment removed for export] *)
    | 1065236 => chkjoin 13 1065240   (* [comment removed for export] *)
    | 1065296 => chkjoin 12 1065300   (* [comment removed for export] *)
    | 1065420 => chkjoin 12 1065424   (* [comment removed for export] *)
    | 1066072 => chkjoin 13 1066076   (* [comment removed for export] *)
    | 1066212 => chkjoin 12 1066216   (* [comment removed for export] *)
    | 1066332 => chkjoin 13 1066336   (* [comment removed for export] *)
    | 1066484 => chkjoin 12 1066488   (* [comment removed for export] *)
    | 1066556 => chkjoin 12 1066560   (* [comment removed for export] *)
    | 1038824 => chkjoin 13 1038828   (* [comment removed for export] *)
    end
  end.
(* [comment removed for export] *)
