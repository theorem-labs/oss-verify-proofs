(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2 F_malloc_bigw.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_A3 ASlot_W10.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_W17 () := ([""; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W17.CEIL_WRAP_1.MMOK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1and"; "1eq"; "2Z"; "3M_DIVU"; "4mul_div"; "5mm_ai"; "6wz"; "7round_up_pg"; "8div"; "8le"; "8lt"; "8opp"; "8pow"; "8sub"; "0a"; "0b"]; ["0cnt"; "9Z_to_bv"; "9bv"; "9bv_signed"; "0x"; "0z"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition mm_frame (nd gm cnt size sc : Z) (j8 : list byte) (s4v s3v s2v s1v s0v rav : word) : list cell :=
[C8 (wz nd); C8 (Z_to_bv 64 gm); C8 (wz cnt); C8 (wz size); C8 (Z_to_bv 64 (sc + 58)); CB 8 j8; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
Lemma round_up_pg_idem : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W17 "8'2'1&7r1%211%311%53612pQ:71").
Proof. intros x.
pose proof (MallocKit_A2.round_up_pg_mod x) as M.
unfold round_up_pg at 1. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
change (2 ^ 12) with 4096. Z.div_mod_to_equations. lia.
Qed.
Lemma signed_lit_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W17 "H'2'0&9&;&<+2+QO%3221%511r1%8221&:%1235%<231'1&CyR0&Ar2%2231%5241%73E13p091pQ<G1").
Proof. intros z.
intros Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
destruct (Z.ltb_spec (z mod 2^64) (2^63)); Z.div_mod_to_equations; lia.
Qed.
Lemma divu_word : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W17 "Q4'2'0&9zr2%3221&:&<+2+R0%3221%5271%;271%72:9%=213'1'ByR0%211&4(3&Ar4%2261&6r3%211%84:741&8%1274%92=1%@3=41p0B1p0E1pQ0Q21pNQ31").
Proof. intros a b.
intros Ha Hb. unfold mul_div. rewrite (wz_unsigned b) by lia. replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
apply bv_eq. rewrite bv_divu_unsigned, (wz_unsigned b), unsigned_lit, Z_to_bv_unsigned by lia.
unfold bv_wrap. change (bv_modulus 64) with (2^64). symmetry. apply Z.mod_small.
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Section MMOK.
Variables (st2 : mstate) (sc cnt size nd xa c : Z) (mt : aptr) (rid : N) (r0 : region).
Let G := conc st2 mt.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis ND : 16 <= nd < 2^40.
Hypothesis NDA : nd mod 4096 = 0.
Hypothesis XA : 0 < xa.
Hypothesis XA2 : xa + nd <= alloc_ceiling.
Hypothesis MST : meta_slot st2 mt.
Hypothesis REC : get_meta_rec st2 mt = meta0.
Hypothesis HC : c_mmap_counter (ctx st2) = c.
Hypothesis CR : 0 <= c < 2^32.
Definition mm_ai : Z :=
let ai := (4096 - UNIT) / size - 1 in
let ai := if cnt - 1 <? ai then cnt - 1 else ai in
if ai <? 0 then 0 else ai.
Definition mm_st4 : mstate :=
upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2).
Lemma mm_ai_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W17 ";'0&9z&5%3221&=v@+1%3221%8261%:261").
Proof.
unfold mm_ai, UNIT. change (4096 - 16) with 4080.
pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)).
destruct (Z.ltb_spec (cnt - 1) (4080 / size - 1)); [destruct (Z.ltb_spec (cnt - 1) 0)| destruct (Z.ltb_spec (4080 / size - 1) 0)]; lia.
Qed.
End MMOK.
End CEIL_WRAP_1.
