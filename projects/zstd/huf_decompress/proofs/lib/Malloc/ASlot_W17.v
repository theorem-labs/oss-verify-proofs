(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (4 recorded proofs replaced by written proofs (round_up_pg_idem, signed_lit_small, divu_word and 1 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2 F_malloc_bigw.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3 ASlot_W10.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W17 () := "C59OSSVerify5KrLib6Malloc<MallocKit_A2?round_up_pg_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3oppK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr06C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr04C45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib7ZBridge9zb_signedC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_divuC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;wz_unsignedC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@bv_divu_unsignedC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv3Sem7mul_divK47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1N00K4ELinuxProcessSemantics5Riscv5Instr5mulop06C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc59OSSVerify5KrLib6Malloc9ASlot_W175mm_aiC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition mm_frame (nd gm cnt size sc : Z) (j8 : list byte) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 (wz nd); C8 (Z_to_bv 64 gm); C8 (wz cnt); C8 (wz size); C8 (Z_to_bv 64 (sc + 58)); CB 8 j8; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

(* [comment removed for export] *)
Lemma round_up_pg_idem x : round_up_pg (round_up_pg x) = round_up_pg x.
Proof.
  pose proof (MallocKit_A2.round_up_pg_mod x) as M.
  unfold round_up_pg at 1. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
  change (2 ^ 12) with 4096. Z.div_mod_to_equations. lia.
Qed.

Lemma signed_lit_small z : -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  destruct (Z.ltb_spec (z mod 2^64) (2^63)); Z.div_mod_to_equations; lia.
Qed.

Lemma divu_word a b : 0 <= a < 2^64 -> 0 < b < 2^64 -> mul_div M_DIVU (Z_to_bv 64 a) (wz b) = Z_to_bv 64 (a / b).
Proof.
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
Hypothesis XA2 : xa + nd <= ATOP.
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

Lemma mm_ai_range : 0 <= mm_ai <= cnt - 1.
Proof.
  unfold mm_ai, UNIT. change (4096 - 16) with 4080.
  pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)).
  destruct (Z.ltb_spec (cnt - 1) (4080 / size - 1)); [destruct (Z.ltb_spec (cnt - 1) 0)| destruct (Z.ltb_spec (4080 / size - 1) 0)]; lia.
Qed.
End MMOK.


End CANSEC1.
