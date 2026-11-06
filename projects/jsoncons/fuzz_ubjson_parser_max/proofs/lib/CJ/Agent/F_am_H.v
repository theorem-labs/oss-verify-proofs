(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls F_mm_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require KStep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_am_A F_am_K F_am_C F_am_F F_am_G.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_am_H () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_H.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_mm_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Decode."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.ITree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Prog."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1Some"; "1bool"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "3Z"; "0L"; "4fx_rel"; "5fixed_shape"; "6brk_new_pages"; "7resp"; "8dec_mmap_fixed"]; ["8fixed_ans"; "9add"; "9land"; "9le"; "9lt"; "9modulo"; "9opp"; "9pow"; "0a"; "0cur"; "0n"; "0r"; "0rsp"; ":Z_to_bv"; ":bv"; ":bv_unsigned"]; ["0u"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte).
Definition brk_regs (a0 : word) : _ :=
mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
Definition brk_res (cur req : Z) (a : brk_ans) : Z := match a with BrkGrown => req | BrkSame => cur end.
Definition brk_mem (cur req : Z) (a : brk_ans) : word -> option byte :=
match a with
| BrkGrown => match brk_new_pages cur req with Some (lo, n) => apply_zeros m [(wa lo, Z_to_bv 64 n)] | None => m end
| BrkSame => m
end.
End BRKNODES.
Lemma land_neg_aligned : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_H "Q3'9'6&Dzr1%3221&G+2+R0%3221%8261%:261'7&Er2+TP0%3221%53A1>&B&OyR0&M&A&Fr3%211%42G1%6271%9281+SoO%<221%C3O1Lp0?1p0F1pQDQ21").
Proof. intros cur.
intros H AL. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
replace ((0 + - cur) mod 2^64) with ((2^52 - cur / 4096) * 4096) by (Z.div_mod_to_equations; lia).
change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. apply Z.mod_mul. lia.
Qed.
Lemma brk_new_pages_aligned : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_H "Q2'9&Czr2%3221&D%1243'7&Er4+TP0%3221%53<1:'3'5%12??%311&=r6&Ar5%2231%5241(1(4%14II75%32;1%D3;51p0@1p0A1p0H1p0K1pQFQ01pQDQ11").
Proof. intros cur n.
intros C0 N0 CA NA. unfold brk_new_pages. rewrite <- !KStep.round_up_pg_eq.
rewrite !KStep.round_up_pg_aligned by (auto; rewrite Z.add_mod, CA, NA by lia; reflexivity).
replace (cur <? cur + n) with true by (symmetry; apply Z.ltb_lt; lia). f_equal. f_equal. lia.
Qed.
Definition fx_rel (A : Z) (a : fixed_ans) (r : word) (u : bool) : Prop :=
match a with
| FxKept e => errno_of r = Some e /\ u = false
| FxDone => r = Z_to_bv 64 A /\ u = true
| FxLost e => errno_of r = Some e /\ u = true
end.
Lemma dec_mmap_fixed_shape : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_H "Q7'9&>'@'7'3%113&?r4r3r2%43321(1r1%22;1%;3941'8'NyR0%211'2'6&;r7%241@>;r5&<r6%2451B?%I3K41%9261qR2;1%@2<1qQH>1%B2?1p0D1pQBQ11pQJQ31pFQ51p2Q61").
Proof. intros A L rsp a.
unfold dec_mmap_fixed, fixed_shape. destruct rsp as [r ws zs us cs ci].
intros HH. destruct cs; [|kill_eff_tail HH]. destruct ci; [|kill_eff_tail HH]. cbv beta iota in HH. revert HH.
destruct ws; [| discriminate]. destruct zs; [| discriminate]. destruct us as [|[ua un] us].
- destruct (errno_of r) eqn:E; [| discriminate]. intros H; inversion H; subst. exists r, false. cbn. rewrite E. auto.
- destruct us; [| discriminate]. destruct (bv_eqb ua (Z_to_bv 64 A) && bv_eqb un (Z_to_bv 64 (mmap_len L))) eqn:E; [| discriminate].
apply andb_prop in E. destruct E as [E1 E2]. apply Fs.bv_eqb_eq in E1. apply Fs.bv_eqb_eq in E2. subst ua un.
destruct (errno_of r) eqn:E.
+ intros H; inversion H; subst. exists r, true. cbn. rewrite E. auto.
+ destruct (bv_eqb r (Z_to_bv 64 A)) eqn:E3; [| discriminate]. apply Fs.bv_eqb_eq in E3. intros H; inversion H; subst. exists (Z_to_bv 64 A), true. cbn. auto.
Qed.
End CEIL_WRAP_1.
