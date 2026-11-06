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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_malloc_entry () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_enframe."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_entry.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1true"; "2and"; "2eq"; "3Z"; "4zseq"; "5clz_fn"; "5clz_notv"; "5clz_pow"; "5stc_fn"; "5stc_q"; "6MMAP_THRESHOLD"; "6size_class"; "6size_to_class"; "7forallb"; "8add"]; ["8div"; "8le"; "8log2"; "8lor"; "8lt"; "8mul"; "8pow"; "8shiftr"; "0a"; "0b"; "0k"; "0n"; "9bv_swrap"; "9bv_wrap"; "0x"]]).
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma srliw_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_entry "M'4'2&Azr2%3221&D&F+2+O%3221%5271%;271'3&LyQ0&G&Mr4%2241r3%5221%8271%7253%;3H21p0D1p0>1pQFK1pQBL1").
Proof. intros a k.
intros Ha Hk. change (bv_wrap 32 a) with (a mod 2^32). rewrite Z.mod_small by lia.
apply swrap32_small. rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia]|].
apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Lemma lor_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_entry "N'4&Azr3%3221'2&D&F+2r4%3221%5281%7281r5%7261%92<1%;2<1&C%1259%B2A1r6%>2=1%@241%B241p081p0=1p0F1pQDK1pQBL1pQHM1").
Proof. intros n a b.
intros Hn Ha Hb. pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)) as NN. split; [exact NN|].
destruct (Z.eq_dec a 0) as [->|A0]; [rewrite Z.lor_0_l; lia|].
destruct (Z.eq_dec b 0) as [->|B0]; [rewrite Z.lor_0_r; lia|].
assert (P : 0 < Z.lor a b).
{ destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [apply zb_lor_eq0 in E; lia|]. lia. }
apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n P)).
rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
- apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia.
- apply (proj1 (Z.log2_lt_pow2 b n ltac:(lia))). lia.
Qed.
Lemma shiftr_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_entry "J'4'2&Azr2%3221&D&F+2r3%3221%5271%;271&Gr4%2216%>2=1r5%;2:1%=241%C241p0@1p0:1pQFG1pQBH1pQHI1").
Proof. intros n a k.
intros Ha Hk. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Definition clz_pow (x : Z) : Z :=
let v1 := Z.lor (Z.shiftr x 2) (Z.shiftr x 1) in
let v2 := Z.lor v1 (Z.shiftr v1 2) in
let v3 := Z.lor v2 (Z.shiftr v2 4) in
let v4 := Z.lor v3 (Z.shiftr v3 8) in
Z.land (v4 + 1) (Z.lxor v4 18446744073709551615).
Definition clz_notv (x : Z) : Z :=
let v1 := Z.lor (Z.shiftr x 2) (Z.shiftr x 1) in
let v2 := Z.lor v1 (Z.shiftr v1 2) in
let v3 := Z.lor v2 (Z.shiftr v2 4) in
let v4 := Z.lor v3 (Z.shiftr v3 8) in
Z.lxor v4 18446744073709551615.
Definition clz_fn (x : Z) : bool := (clz_pow x =? 2 ^ Z.log2 x) && (0 <=? clz_notv x) && (clz_notv x <? 2^64).
Lemma clz_check_true : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_entry "<'3'0&>'4&6&5+;+WoE%3221%73651(1%;3:21").
Proof. vm_compute. reflexivity. Qed.
Lemma clz_pow_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_entry "O'4'2&A+;r1%3221&D+XP0%2241%8241'3&8r2%211&F+2&B%115%4231%93C61z&7%11:%E231+R0%;2:1%D241%J241%K291p0D1pQNN1").
Proof. intros x.
intros Hx. pose proof (forallb_zseq clz_fn 11 8181 x clz_check_true ltac:(lia) ltac:(lia)) as X. unfold clz_fn in X.
apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
apply Z.eqb_eq in X1. apply Z.leb_le in X2. apply Z.ltb_lt in X3. split; [exact X1| split; [exact X2| exact X3]].
Qed.
Definition stc_q (q : Z) : Z :=
if q <? 10 then q else
let x := q + 1 in
let i := 4 * Z.log2 x - 4 in
let i := if size_class (i + 1) <? x then i + 2 else i in
if size_class i <? x then i + 1 else i.
Definition stc_fn (q : Z) : bool :=
let sc := stc_q q in (0 <=? sc) && (sc <? 48) && (q + 1 <=? size_class sc)
&& ((q <? 10) || ((3 <=? Z.log2 (q + 1)) && (Z.log2 (q + 1) <=? 12))).
Lemma stc_check_true : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_entry "<'3'0&>'4&9&5z+WoO%3221%73651(1%;3:21").
Proof. vm_compute. reflexivity. Qed.
Lemma size_to_class_q : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_entry "D'4&Azr1%3221'3&=r2%211&:&@&?+3%2261+@%5221%711%<3A91p0>1pQHC1").
Proof. intros n.
intros Hn. unfold size_to_class, stc_q, IB, clz32.
replace (Z.shiftr (n + 4 - 1) 4) with ((n + 3) / 16) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 4) with 16; f_equal; lia).
set (q := (n + 3) / 16). cbv zeta.
replace ((28 - (31 - Z.log2 (q + 1))) * 4 + 8) with (4 * Z.log2 (q + 1) - 4) by lia.
reflexivity.
Qed.
Lemma size_to_class_props : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_entry "Q@'4'2&Azr1%3221&D&;%2241%8241&=r2%211%;2:1+Q@%9231%?231&?+4%2281&E+@&<%11;%4231%G261+:&@+3%<2B1%3219%M251&Br3%A216%821>+1%D221%611%Q52;1+<%Q7231%Q9231p0<1%Q;2C1%Q<2M1p0Q51pQHQ?1").
Proof. intros n.
intros Hn. unfold MMAP_THRESHOLD in Hn. rewrite size_to_class_q by lia.
assert (Q : 0 <= (n + 3) / 16 < 8191) by (Z.div_mod_to_equations; lia).
pose proof (forallb_zseq stc_fn 0 8191 ((n + 3) / 16) stc_check_true ltac:(lia) ltac:(lia)) as X. unfold stc_fn in X. cbv zeta in X.
apply andb_prop in X. destruct X as [X X4]. apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
apply Z.leb_le in X1. apply Z.ltb_lt in X2. apply Z.leb_le in X3.
split; [lia|]. split; [Z.div_mod_to_equations; lia|].
intros HQ. apply orb_prop in X4. destruct X4 as [X4|X4]; [apply Z.ltb_lt in X4; lia|].
apply andb_prop in X4. destruct X4 as [X5 X6]. apply Z.leb_le in X5. apply Z.leb_le in X6. lia.
Qed.
Definition entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a2 a3 a4 junk m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz n) s1 (Z_to_bv 64 n) a1 a2 a3 a4 (Z_to_bv 64 (size_to_class n)) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x16e88) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 48 junk; C8 s0; C8 ra]
/\ length junk = 48%nat
/\ stk asegs m' lo (bv_unsigned sp + -64)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'.
Definition entry_big_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists junk m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz n) s1 (Z_to_bv 64 n) a1 a2 a3 a4 (Z_to_bv 64 131051) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x16d60) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 48 junk; C8 s0; C8 ra]
/\ length junk = 48%nat
/\ stk asegs m' lo (bv_unsigned sp + -64)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'.
End CEIL_WRAP_1.
