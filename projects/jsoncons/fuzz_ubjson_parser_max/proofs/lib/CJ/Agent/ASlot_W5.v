(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_A3 ASlot_W1.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_W5 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W5.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."], [["1None"; "1Some"; "2eq"; "2not"; "3Z"; "4clr"; "5LActive"; "5active"; "5aptr"; "5dequeue"; "5get_meta_rec"; "5m_next"; "5m_prev"; "5m_set_next"; "5m_set_prev"; "5mstate"]; ["5optr"; "5put_meta"; "5set_active"; "0g"; "0nx"; "0pv"; "0sc"; "0st"; "0st1"; "0st2"; "0st3"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition clr (r : meta) : meta := m_set_prev None (m_set_next None r).
Lemma dequeue_self_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W5 "Q2'4&8'?'2&@&;&:r1r2%3221%511(1%12;4%:3931&9(6r4%211r3%5321;&A&5%@2>4%211&B(0%11I%33;1C%83:51%J3K:1p0A1pQ@M1pQ8O1pQ>Q11").
Proof. intros sc g st.
intros GN. unfold dequeue. rewrite GN. cbn [optr_eqb negb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbn [negb set_head].
rewrite upd_meta_put. reflexivity.
Qed.
Lemma dequeue_other_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W5 "R6'4&8'?'2&@&;&:r1r4%3221%511(1r3%22<1%;3:41&<r2r5%<221%411%A3@17&3r6%D3F61%311r7%G3I91%611&7r9%22=1r8%E2O1%N3M31&9(6r:%211%4319@&A&=%Q32C@%22:1%43B1E&>%Q72Q6@%22>1%83B1Q8&Br<%Q72QA>%3321Q<&5%Q?2H4%211%@361Q@tQFQF51tQDQG:1tQBQH?1%QH3QIE1p0K1p0Q21p0Q61p0Q;1p0QB1pQ@QO1pQ<R11pQ:R21pQ8R31pQ>R51").
Proof. intros sc g nx pv st.
intros GN GP NEn NEp HA. unfold dequeue. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head set_head].
rewrite !upd_meta_put.
match goal with |- context [optr_eqb (active ?s sc) (Some g)] => change (active s sc) with (active st sc) end.
rewrite HA. cbn [optr_eqb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbv zeta.
f_equal. f_equal. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E).
rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity.
Qed.
End CEIL_WRAP_1.
