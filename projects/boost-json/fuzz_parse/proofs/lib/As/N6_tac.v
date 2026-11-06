(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes ZBridge.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc2eq46Stdlib6ZArith6BinInt1Zj54landj56moduloj53powhc3andj52lej52ltj54lxorj53sub" s.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac nonneg_lit d := lazymatch (eval vm_compute in (andb (Z.leb 0 d) (Z.leb d 4096))) with true => d end.

Ltac addr_diff E A ::=
  lazymatch E with
  | Z.add ?X ?c1 =>
      lazymatch A with
      | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in let d := eval vm_compute in (c1 - c2)%Z in nonneg_lit d
      | X => let c1 := zlit c1 in nonneg_lit c1
      | _ => let e := zlit E in let a := zlit A in let d := eval vm_compute in (e - a)%Z in nonneg_lit d
      end
  | _ =>
      lazymatch A with
      | Z.add E ?c2 => let c2 := zlit c2 in let d := eval vm_compute in (- c2)%Z in nonneg_lit d
      | E => constr:(0%Z)
      | _ => let e := zlit E in let a := zlit A in let d := eval vm_compute in (e - a)%Z in nonneg_lit d
      end
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land_7 : ltac2:(zQ "40!h9!j0!kd!l4>1y$0@3$1$0@2$2^1+7@2$3^1+8").
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_ones64 : ltac2:(zQ "50!h9!j0!kd!l4!ld>1x$0@3$1$0@2$2^1+vvvvvvvvvvvvvvvf@2$3^1@2$4+2+k0").
Proof. intros x. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma lxor_ones64 : ltac2:(zQ "80!h9!m3!j0!m9!me!n3!ld!na>1x$0>0@2$1@2$3Z^1@2$4^1@2$6+2+k0@3$2$0@2$5^2+vvvvvvvvvvvvvvvf@2$7+vvvvvvvvvvvvvvvf^2").
Proof.
  intros x Hx. destruct (Z.eq_dec x 0) as [->|NZ]; [reflexivity|].
  change 18446744073709551615 with (Z.ones 64).
  rewrite <- Z.ldiff_ones_l_low; [| lia | apply Z.log2_lt_pow2; lia].
  rewrite <- Z.sub_nocarry_ldiff.
  - unfold Z.ones. rewrite Z.shiftl_1_l. reflexivity.
  - rewrite Z.ldiff_ones_r_low; [reflexivity | lia | apply Z.log2_lt_pow2; lia].
Qed.
(* [comment removed for export] *)
