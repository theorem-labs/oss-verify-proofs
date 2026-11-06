(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp F_malloc_enf AllocSlot_iface Malloc_iface F_malloc_join.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_malloc_small () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_small.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1length"; "1nat"; "1option"; "1true"; "2and"; "2eq"; "2iff"; "2or"; "3Z"; "4coarse_sc"; "4lor1_check"; "4lor1_range_check"; "5usages"; "5wz"]; ["6mstate"; "6size_class"; "6usage"; "7nth_error"; "8add"; "8even"; "8land"; "8le"; "8lor"; "8lt"; "8lxor"; "8modulo"; "8pow"; "8to_nat"; "0sc"; "0st"]; ["9bv"; "0x"; "0y"]]).
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition coarse_sc (st : mstate) (sc : Z) : Z :=
match active st sc with
| Some _ => sc
| None =>
if (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) then
let usage1 := usage st (Z.lor sc 1) in
let usage1 := match active st (Z.lor sc 1) with
| None => usage1 + 3
| Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
end in
if usage1 <=? 12 then Z.lor sc 1 else sc
else sc
end.
Lemma malloc_small_ctrl_eq {R} lay st n (k : mstate -> option (aptr * Z) -> Malloc.M R) bail :
malloc_small_ctrl lay st n k bail =
let sc := coarse_sc st (size_to_class n) in
let g := active st sc in
let mask := match g with Some gp => m_avail (get_meta_rec st gp) | None => 0 end in
let first := lowbit mask in
match g, negb (first =? 0) with
| Some gp, true => k (upd_meta gp (m_set_avail (mask - first)) st) (Some (gp, ctz32 first))
| _, _ =>
alloc_slot lay FUEL st sc n (fun st1 idx =>
if idx <? 0 then k st1 None
else match active st1 sc with
| Some gp => k st1 (Some (gp, idx))
| None => SVis (EUndef UBadPtr) (fun _ => bail)
end) bail
end.
Proof. reflexivity. Qed.
Lemma usages_length : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_small ">'@'7'3&2'Q0yR0%211&>r1%211%7241uQ@%;3:21pR0=1").
Proof. intros. unfold usages. rewrite length_map, length_seq. reflexivity. Qed.
Lemma usages_nth : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_small "Q3'@':'6&Gzr1%3221&I+Q@%2241%8241'7'4'Q0yR0%211%411&C&>r3%211&Mr2%211%73941(0&?&B%1296%311%52?1%D3?71p0F1pQNQ01pR0Q21").
Proof.
intros st sc Hsc. unfold usages. rewrite nth_error_map, nth_error_seq.
replace (Z.to_nat sc <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma lxor_sign_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_small "G':'6&Gzr1%3221&I&L+2+QO%3221%5271%;271'7&Jr2+XPPPPPPPPPPP0%3221&D%1243%73D31p091pR4F1").
Proof. intros x.
intros Hx. change 9223372036854775808 with (2^63).
rewrite <- Z.add_nocarry_lxor. 2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec i 63) as [->|NE].
- replace (Z.testbit x 63) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
- rewrite Z.pow2_bits_false by lia. apply andb_false_r. }
reflexivity.
Qed.
Lemma land_ones64 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_small ">':'7&Fr1+_oooooooooooO%3221&K&L+2+R0%3221%5281%;3<71pR6=1").
Proof. intros y. change 18446744073709551615 with (Z.ones 64). apply Z.land_ones. lia. Qed.
Lemma land_1_even : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_small "@':&8'7&Fr1+1%3221z%63821'1&E%117(5%;3421%=261pR4?1").
Proof. intros x.
change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2^1) with 2.
rewrite Z.even_spec. split.
- intros H. exists (x / 2). lia.
- intros [k ->]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.
Definition lor1_check : bool :=
forallb (fun sc => negb ((4 <=? sc) && (sc <? 32) && Z.even sc) || (size_class sc <=? size_class (Z.lor sc 1))) (zseq 0 48).
Lemma lor1_check_true : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_small "5'7'1&<(5%43321").
Proof. vm_compute. reflexivity. Qed.
Lemma size_class_lor1 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_small "L':'6&G+4r1%3221&I+Q0%2241%8241'7'1&Er2%211(5%63521&Ar3%211&H+1%2241%611%F251p091p0A1pQNK1").
Proof. intros sc.
intros H E. pose proof (forallb_zseq _ 0 48 sc lor1_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
replace (4 <=? sc) with true in X by (symmetry; apply Z.leb_le; lia).
replace (sc <? 32) with true in X by (symmetry; apply Z.ltb_lt; lia). rewrite E in X. cbn [andb negb orb] in X.
apply Z.leb_le. exact X.
Qed.
Definition lor1_range_check : bool := forallb (fun sc => (0 <=? Z.lor sc 1) && (Z.lor sc 1 <? 48)) (zseq 0 48).
Lemma lor1_range_check_true : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_small "5'7'1&=(5%43321").
Proof. vm_compute. reflexivity. Qed.
Lemma lor1_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_small "C':'6&Gzr1%3221&I+Q@%2241%8241&Hr2+1%3221%<2;1%9228%?221p081pQNB1").
Proof. intros sc.
intros H. pose proof (forallb_zseq _ 0 48 sc lor1_range_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
apply andb_prop in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
Qed.
Lemma coarse_sc_cases : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_small "Q6'@':'6&Gzr1%3221&I+Q@%2241%8241'9'7&;r3r2%3221%53@12&H+1%2251%93D51+4%D218+Q0%B2:1%H231'1&E%11>(5%C3421%N261%O2<1%G2A1p0I1pQNQ31pR0Q51").
Proof. intros st sc.
intros H. unfold coarse_sc. destruct (active st sc); [left; reflexivity|].
destruct ((4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0)) eqn:E; [|left; reflexivity].
apply andb_prop in E. destruct E as [E E5]. apply andb_prop in E. destruct E as [E E4].
apply andb_prop in E. destruct E as [E E3]. apply andb_prop in E. destruct E as [E1 E2].
apply Z.leb_le in E1. apply Z.ltb_lt in E2.
cbv zeta. destruct (_ <=? 12); [right|left]; auto.
Qed.
End CEIL_WRAP_1.
