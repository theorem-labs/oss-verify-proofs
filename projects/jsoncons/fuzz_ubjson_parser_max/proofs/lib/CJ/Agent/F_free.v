(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_enframe F_mm_syscalls MallocTree MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres F_ntf F_free_A F_free_B F_free_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_free_K.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_free () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_free_K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_ntf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Decode."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2eq"; "3Z"; "4hdr_st"; "5oracle_ok"; "6ticks_ok"; "7mmap_len"; "8aptr"; "8mstate"; "8round_up_pg"; "9modulo"; "0m"; "0o"; "0pf"; "0st"; ":bv"]; ["0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition DROPPED (st st' : mstate) (a : Z) : Prop :=
exists rid r, (s_regions st) !! rid = Some r /\ (s_regions st') !! rid = None /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r).
Definition lbrm (LB : list block) (blk : block) : list block :=
filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot blk))) LB.
Lemma oracle_ok_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free "?'?yR0%211'0y8%511%311p051'8&4r2r1%33221pN51pH71").
Proof. intros m st. intros rid r q h _ _ _ _ _. reflexivity. Qed.
Lemma oracle_ok_hdr_st : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free "L'?yR0%211'0y8%511%311p051'8&7&5r2%211&4r5r4r3%43321r6&3%1254%83371p051p0;1pL?1pNA1pHC1pJD1").
Proof. intros o m st pf.
intros TK OK rid r q h Hr Hk Hq M8 Hc. change (s_regions (hdr_st st pf)) with (s_regions st) in Hr.
rewrite hdr_st_cell_read in Hc by exact TK.
destruct (N.eqb rid (fst pf) && ((q =? snd pf - 1) || (q =? snd pf - 2) || (q =? snd pf - 3)))%bool; [discriminate|].
exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.
Lemma munmap_ok_range_val a : match a with RgErr e => 1 <= e <= 4095 | _ => True end -> munmap_answer_ok (range_val a) = true.
Proof.
destruct a as [e|c]; cbn [range_val]; intros He; unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
- apply orb_true_intro. right. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
- reflexivity.
Qed.
Lemma round_up_pg_mod : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free ";'2'1&:&9r1%211+TP0%5221z%83921pQ2:1").
Proof. intros x. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. Z.div_mod_to_equations. lia. Qed.
Lemma mmap_len_round : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_free "9'2'1&6&9r1%211%411%63712pQ281").
Proof. intros x.
pose proof (round_up_pg_mod x) as M. unfold mmap_len, page_round_up_Z, page_size.
set (y := round_up_pg x) in *. Z.div_mod_to_equations. nia.
Qed.
End CEIL_WRAP_1.
Ltac cover_intervals tac :=
let lo0 := fresh "ilo" in let hi0 := fresh "ihi" in let HW := fresh "HinW" in let y := fresh "y" in let Hy := fresh "Hy" in
intros lo0 hi0 HW y Hy; cbn [In] in HW;
repeat (destruct HW as [HW|HW]); try contradiction;
injection HW; intros; subst lo0 hi0; tac y Hy.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Lemma NoDup_map_inj_in {A B} (f : A -> B) (l : list A) :
List.NoDup (map f l) -> forall x y, In x l -> In y l -> f x = f y -> x = y.
Proof.
induction l as [|a l IH]; intros ND x y Hx Hy E; [destruct Hx|].
cbn [map] in ND. inversion ND; subst.
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; assumption].
- exfalso. apply H1. rewrite E. apply in_map. exact Hy.
- exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.
Lemma filter_ext_in {A} (P1 P2 : A -> Prop) `{forall x, Decision (P1 x)} `{forall x, Decision (P2 x)} (l : list A) :
(forall x, In x l -> (P1 x <-> P2 x)) -> filter P1 l = filter P2 l.
Proof.
induction l as [|a l IH]; intros HE; [reflexivity|]. rewrite !filter_cons.
rewrite IH by (intros x Hx; apply HE; right; exact Hx).
destruct (decide (P1 a)) as [Y|N]; destruct (decide (P2 a)) as [Y'|N']; try reflexivity; exfalso;
pose proof (HE a (or_introl eq_refl)); tauto.
Qed.
End CEIL_WRAP_2.
