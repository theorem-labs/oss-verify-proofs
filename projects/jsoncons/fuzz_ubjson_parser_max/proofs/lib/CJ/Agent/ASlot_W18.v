(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2 F_malloc_big.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_A3.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_W18 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1cons"; "1list"; "1nil"; "1pair"; "1prod"; "2and"; "2not"; "3Z"; "4ivl"; "4outside"; "4sub_fp"; "5In"; "6le"; "6lt"; "0W"; "0hi"]; ["0lo"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition as_fm_link (st0 : mstate) (g head : aptr) : mstate :=
let hprev := m_prev (get_meta_rec st0 head) in
let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
upd_meta head (m_set_prev (Some g)) st2.
Definition as_fm_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).
Definition as_queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
match get_head st0 h with
| Some head => as_fm_link st0 g head
| None => as_fm_single st0 h g
end.
Lemma as_queue_eq : forall R h g st0 (k : mstate -> Malloc.M R) (bail : Malloc.M R),
m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
queue h g st0 k bail = k (as_queue_st h g st0).
Proof.
intros R h g st0 k bail Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
unfold as_queue_st, as_fm_link, as_fm_single. destruct (get_head st0 h); reflexivity.
Qed.
Definition as_fm_st (st : mstate) (g : aptr) : mstate := as_queue_st LFree g (put_meta g meta0 st).
Lemma as_free_meta_eq : forall R st g (k : mstate -> Malloc.M R) (bail : Malloc.M R), free_meta g st k bail = k (as_fm_st st g).
Proof.
intros. unfold free_meta, as_fm_st. apply as_queue_eq; rewrite get_meta_rec_put_same; reflexivity.
Qed.
Lemma outside_In : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W18 "N'1&8%211'7&9r4r3%3221&;'4%1277(3r2%24::71r5%73521&6'5&<%12>5&=%127?%5231%711p091p0B1pQ0G1pQ2H1pQ4I1pNK1").
Proof. intros W x lo hi.
induction W as [|[a b] W IH]; cbn; intros HO HI; [destruct HI|].
destruct HI as [E|HI]; [inversion E; subst; tauto|]. apply IH; tauto.
Qed.
Lemma sub_fp_single : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W18 "H'1'4'7%2211%411&;(3r2r1%347721r3%63821&:(0%84<<47(2%11=%43>31r4%7221p091pQ0C1pQ2D1pNC1").
Proof. intros W lo hi. intros HI x HO. cbn. split; [exact (outside_In W x lo hi HO HI)| exact I]. Qed.
End CEIL_WRAP_1.
