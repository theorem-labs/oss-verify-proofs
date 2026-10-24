(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Functional multiplication loop adapted from the pinned Varnish proof to
    the actual zlib checksum_fuzzer instruction layout and register allocation. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Tac Bytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import Img0 CrcLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require TacDiet2.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.transport_chunks segs m a bs ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.footprint_after_store segs m a bs ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.mem_after_store ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.transport_after_call segs m m' MU WM ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.addr_eq_tac ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.word_eq_tac ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.mlia ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require StepFast.
#[local] Ltac2 Set OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.step_core segs R F pc fc rv m ro ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.zstep ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Destzna.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.destruct_exs PO ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Destzna.dk_exs PO.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.destruct_ands PO ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require WeqGuard TacDiet2.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.WeqGuard.weq_guard; OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Stor0fe.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.mem_after_store ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Dieta54.
Local Ltac lia ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Dieta54.dlia.
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcModel CrcByteStep CrcTables CrcLoads CrcLinearBasis.

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcUnrolledBytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import AdlerModel AdlerWord AdlerShortReduce.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import AdlerOneByte AdlerSeed.
Lemma adler_combine_div32 : forall x, (0 <= x < 2^32)%Z ->
  (x*2147975281/2^47 = x/65521)%Z.
Proof.
  intros x HX.
  set (q := (x/65521)%Z). set (r := (x mod 65521)%Z).
  pose proof (Z.div_mod x 65521 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound x 65521 ltac:(lia)) as R. fold q r in D,R.
  assert (HQ : (0 <= q <= 65551)%Z) by lia.
  assert (B : (q*2^47 <= x*2147975281 < (q+1)*2^47)%Z) by nia.
  replace (x*2147975281)%Z with ((x*2147975281-q*2^47)+q*2^47)%Z by ring.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. unfold q. lia.
Qed.
Lemma adler_conditional_subtract2_word : forall x, (0 <= x < 2*131042)%Z ->
  Z_to_bv 64 (x+Z.land ((-Z.b2z (131041 <? x)) mod 2^64) 18446744073709420574) =
  Z_to_bv 64 (x mod 131042).
Proof.
  intros x HX. destruct (Z.ltb_spec 131041 x).
  - change (Z_to_bv 64 (x+18446744073709420574) = Z_to_bv 64 (x mod 131042)).
    assert (E : (x mod 131042 = x-131042)%Z).
    { replace x with ((x-131042)+1*131042)%Z at 1 by ring. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    rewrite E. apply Z_to_bv_eqm.
    replace (x+18446744073709420574)%Z with ((x-131042)+1*2^64)%Z by ring.
    rewrite Z.mod_add by lia. reflexivity.
  - change (Z_to_bv 64 (x+0) = Z_to_bv 64 (x mod 131042)).
    rewrite Z.add_0_r,Z.mod_small by lia. reflexivity.
Qed.
Lemma adler_combine_suffix : forall
  (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (low high : Z),
  (0 <= low < 2*65521)%Z -> (0 <= high < 4*65521)%Z ->
  (forall h11 h12 h13 h14, evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
      (Z_to_bv 64 (adler_pack (low mod 65521) ((high mod 131042) mod 65521))) h11 h12 h13 h14
      a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (ret_pc ra) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 65520) (Z_to_bv 64 high) (Z_to_bv 64 (-65521)) (Z_to_bv 64 low) a4
      a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x1524c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q low high HL HH CONT.
  pose proof (Z.mod_pos_bound low 65521 ltac:(lia)) as HLF.
  pose proof (Z.mod_pos_bound high 131042 ltac:(lia)) as HHF.
  pose proof (Z.mod_pos_bound (high mod 131042) 65521 ltac:(lia)) as HHFF.
  assert (SB : (0 <= Z.shiftl (high mod 131042) 16 < 2^64)%Z) by (rewrite Z.shiftl_mul_pow2 by lia;nia).
  assert (SBF : (0 <= Z.shiftl ((high mod 131042) mod 65521) 16 < 2^64)%Z) by (rewrite Z.shiftl_mul_pow2 by lia;nia).
  idtac "ADLER COMBINE suffix 0". zstep.
  idtac "ADLER COMBINE suffix 1". zstep.
  idtac "ADLER COMBINE suffix 2". zstep.
  idtac "ADLER COMBINE suffix 3". zstep.
  idtac "ADLER COMBINE suffix 4". zstep.
  rewrite adler_conditional_subtract_word by exact HL.
  idtac "ADLER COMBINE suffix 5". zstep.
  idtac "ADLER COMBINE suffix 6". zstep.
  idtac "ADLER COMBINE suffix 7". zstep.
  idtac "ADLER COMBINE suffix 8". zstep.
  idtac "ADLER COMBINE suffix 9". zstep.
  idtac "ADLER COMBINE suffix 10". zstep.
  idtac "ADLER COMBINE suffix 11". zstep.
  idtac "ADLER COMBINE suffix 12". zstep.
  rewrite adler_conditional_subtract2_word by exact HH.
  idtac "ADLER COMBINE suffix 13". zstep.
  idtac "ADLER COMBINE suffix 14". zstep.
  idtac "ADLER COMBINE suffix 15". zstep.
  idtac "ADLER COMBINE suffix 16". zstep.
  idtac "ADLER COMBINE suffix 17". zstep.
  idtac "ADLER COMBINE suffix 18". zstep.
  rewrite adler_conditional_shift_word by exact HHF.
  idtac "ADLER COMBINE suffix 19". zstep.
  first [rewrite adler_pack_or by lia|rewrite Z.lor_comm;rewrite adler_pack_or by lia].
  idtac "ADLER COMBINE suffix 20". zstep.
  apply CONT.
Qed.
Lemma adler_pack_land16 : forall a b, (0 <= a < ADLER_BASE)%Z ->
  Z.land (adler_pack a b) 65535 = a.
Proof. intros a b HA. change (Z.land (adler_pack a b) (Z.ones 16) = a). rewrite Z.land_ones by lia. change (adler_pack a b mod 65536 = a). apply adler_pack_low. exact HA. Qed.
Lemma adler_combine_setup : forall
  (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (a b c d n : Z),
  (0 <= a < ADLER_BASE)%Z -> (0 <= b < ADLER_BASE)%Z ->
  (0 <= c < ADLER_BASE)%Z -> (0 <= d < ADLER_BASE)%Z -> (0 <= n <= 1048576)%Z ->
  ov_read_bytes rsegs m (wa 0x119e0) 8 = Some (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  (forall h5 h6 h7 h14 h15 h16 h17, evt rsegs Q
    (MS (mkR ra sp gp tp h5 h6 h7 s0 s1 (Z_to_bv 64 65520)
      (Z_to_bv 64 (b+d+65521-n mod 65521+(n mod 65521*a) mod 65521))
      (Z_to_bv 64 (-65521)) (Z_to_bv 64 (a+c+65520)) h14 h15 h16 h17
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x15230) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (adler_pack a b))
      (Z_to_bv 64 (adler_pack c d)) (Z_to_bv 64 n) a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x15198) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q a b c d n HA HB HC HD HN MAGIC CONT.
  pose proof (adler_pack_range a b HA HB) as HAB.
  pose proof (adler_pack_range c d HC HD) as HCD.
  remember (Z.shiftr (n*ADLER_MAGIC) 64) as h eqn:DH.
  assert (HH : (0 <= h <= n)%Z).
  { rewrite DH,Z.shiftr_div_pow2 by lia. apply adler_mulhu_bounds. lia. }
  assert (NH : (0 <= Z.shiftr (n-h) 1+h <= n)%Z).
  { rewrite Z.shiftr_div_pow2 by lia.
    assert (E : (0 <= (n-h)/2 <= n-h)%Z) by (split;[apply Z.div_pos;lia|apply Z.div_le_upper_bound;lia]). lia. }
  assert (QN : Z.shiftr (Z.shiftr (n-h) 1+h) 15 = (n/ADLER_BASE)%Z).
  { rewrite DH. apply adler_div_form. lia. }
  pose proof (Z.div_mod n ADLER_BASE ltac:(unfold ADLER_BASE;lia)) as DN.
  pose proof (Z.mod_pos_bound n ADLER_BASE ltac:(unfold ADLER_BASE;lia)) as RN.
  assert (PN : (0 <= n/ADLER_BASE*ADLER_BASE <= n)%Z).
  { pose proof (Z.div_pos n ADLER_BASE ltac:(lia) ltac:(unfold ADLER_BASE;lia)). unfold ADLER_BASE in *. lia. }
  set (r := (n mod 65521)%Z).
  set (x := (r*a)%Z).
  assert (XR : (0 <= x < 2^32)%Z) by (unfold x,r,ADLER_BASE in *;nia).
  pose proof (adler_combine_div32 x XR) as QX.
  pose proof (Z.div_mod x 65521 ltac:(lia)) as DX.
  pose proof (Z.mod_pos_bound x 65521 ltac:(lia)) as RX.
  assert (PX : (0 <= x/65521*65521 <= x)%Z).
  { pose proof (Z.div_pos x 65521 ltac:(lia) ltac:(lia));lia. }
  assert (MX : (0 <= x*2147975281 < 2^64)%Z) by nia.
  unfold ADLER_BASE,ADLER_MAGIC in *.
  idtac "ADLER COMBINE setup 0". zstep.
  if_cases NEG;zify_cond NEG;[exfalso;lia|].
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 1". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 2". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 3". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 4". zstep.
  rewrite adler_srliw16_pack by assumption.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 5". zstep.
  rewrite adler_srliw16_pack by assumption.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 6". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 7". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 8". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 9". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 10". zstep.
  rewrite adler_pack_land16 by assumption.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 11". zstep.
  rewrite adler_pack_land16 by assumption.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 12". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 13". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 14". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 15". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 16". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 17". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 18". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 19". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 20". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 21". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 22". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 23". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 24". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  rewrite QN.
  idtac "ADLER COMBINE setup 25". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 26". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  replace (n-n/65521*65521)%Z with r by (unfold r;rewrite Z.mod_eq by lia;ring).
  idtac "ADLER COMBINE setup 27". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  change (r*a)%Z with x.
  idtac "ADLER COMBINE setup 28". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 29". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 30". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  rewrite Z.shiftr_div_pow2 by lia. rewrite QX.
  idtac "ADLER COMBINE setup 31". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 32". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  unfold_swrap32. rewrite Z.mod_small by lia.
  idtac "ADLER COMBINE setup 33". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 34". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  replace (x-x/65521*65521)%Z with (x mod 65521)%Z by (rewrite Z.mod_eq by lia;ring).
  idtac "ADLER COMBINE setup 35". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 36". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER COMBINE setup 37". zstep.
  try rewrite <- DH.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  replace (x mod 65521+2147483648-2147483648)%Z with (x mod 65521)%Z by ring.
  rewrite (Z.mod_small (x mod 65521) 4294967296) by lia.
  replace (b+d+65535-r+x mod 65521+ -14)%Z with (b+d+65521-r+x mod 65521)%Z by ring.
  unfold x,r in *. apply CONT.
Qed.
Definition adler_combine_model (a b c d n : Z) : Z :=
  adler_pack ((a+c-1) mod 65521)
    ((b+d+65521-n mod 65521+(n mod 65521*a) mod 65521) mod 65521).
Lemma adler_combine_body : forall
  (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (a b c d n : Z),
  (0 <= a < ADLER_BASE)%Z -> (0 <= b < ADLER_BASE)%Z ->
  (0 <= c < ADLER_BASE)%Z -> (0 <= d < ADLER_BASE)%Z -> (0 <= n <= 1048576)%Z ->
  ov_read_bytes rsegs m (wa 0x119e0) 8 = Some (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  (forall h5 h6 h7 h11 h12 h13 h14 h15 h16 h17, evt rsegs Q
    (MS (mkR ra sp gp tp h5 h6 h7 s0 s1 (Z_to_bv 64 (adler_combine_model a b c d n))
      h11 h12 h13 h14 h15 h16 h17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (ret_pc ra) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (adler_pack a b))
      (Z_to_bv 64 (adler_pack c d)) (Z_to_bv 64 n) a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x15198) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q a b c d n HA HB HC HD HN MAGIC CONT.
  pose proof (Z.mod_pos_bound n 65521 ltac:(lia)) as RN.
  pose proof (Z.mod_pos_bound (n mod 65521*a) 65521 ltac:(lia)) as RX.
  assert (HR : (0 <= b+d+65521-n mod 65521+(n mod 65521*a) mod 65521 < 4*65521)%Z) by (unfold ADLER_BASE in *;lia).
  eapply adler_combine_setup; [exact HA|exact HB|exact HC|exact HD|exact HN|exact MAGIC|].
  intros h5 h6 h7 h14 h15 h16 h17. zstep. if_cases K;zify_cond K.
  - assert (POS : (0 < a+c)%Z) by (unfold ADLER_BASE in *;lia).
    zstep. replace (a+c+65520+ -65521)%Z with (a+c-1)%Z by ring.
    eapply adler_combine_suffix; [unfold ADLER_BASE in *;lia|exact HR|].
    intros h11 h12 h13 h14'.
    rewrite Z.mod_mod_divide by (exists (2%Z);reflexivity).
    unfold adler_combine_model in CONT. apply CONT.
  - assert (ZERO : (a+c=0)%Z) by (unfold ADLER_BASE in *;lia).
    do 2 zstep.
    eapply adler_combine_suffix; [lia|exact HR|].
    intros h11 h12 h13 h14'.
    rewrite Z.mod_mod_divide by (exists (2%Z);reflexivity).
    unfold adler_combine_model in CONT. rewrite ZERO in CONT.
    change ((0-1) mod 65521)%Z with 65520%Z in CONT.
    change (65520 mod 65521)%Z with 65520%Z.
    apply CONT.
Qed.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcGen CrcApiRegisters RegisterBridge.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Regs6ss.
Theorem adler32_combine_spec : forall
  (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b c d n : Z),
  (0 <= a < ADLER_BASE)%Z -> (0 <= b < ADLER_BASE)%Z ->
  (0 <= c < ADLER_BASE)%Z -> (0 <= d < ADLER_BASE)%Z -> (0 <= n <= 1048576)%Z ->
  ov_read_bytes rsegs m (wa 0x119e0) 8 = Some (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  evt rsegs (crc_return_post (adler_combine_model a b c d n)
    ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (adler_pack a b))
      (Z_to_bv 64 (adler_pack c d)) (Z_to_bv 64 n) a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x15198) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m a b c d n HA HB HC HD HN MAGIC.
  eapply adler_combine_body; [exact HA|exact HB|exact HC|exact HD|exact HN|exact MAGIC|].
  intros h5 h6 h7 h11 h12 h13 h14 h15 h16 h17.
  apply evt_done. unfold crc_return_post. do 14 eexists.
  split; [reflexivity|]. split; [apply munch_refl|apply wmono_refl].
Qed.
Lemma adler_combine_model_range : forall a b c d n,
  (0 <= adler_combine_model a b c d n < 2^32)%Z.
Proof.
  intros. unfold adler_combine_model. apply adler_pack_range;apply Z.mod_pos_bound;unfold ADLER_BASE;lia.
Qed.
Theorem adler32_combine_registers : forall R F fc m a b c d n,
  reg_get R 10 = Z_to_bv 64 (adler_pack a b) ->
  reg_get R 11 = Z_to_bv 64 (adler_pack c d) ->
  reg_get R 12 = Z_to_bv 64 n ->
  (0 <= a < ADLER_BASE)%Z -> (0 <= b < ADLER_BASE)%Z ->
  (0 <= c < ADLER_BASE)%Z -> (0 <= d < ADLER_BASE)%Z -> (0 <= n <= 1048576)%Z ->
  ov_read_bytes rsegs m (wa 0x119e0) 8 = Some (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  evt rsegs (crc_api_post (adler_combine_model a b c d n) R F fc m)
    (MS R F (Z_to_bv 64 0x15198) fc None m (seg_rom rsegs)).
Proof.
  intros R F fc m a b c d n H0 H1 H2 HA HB HC HD HN MAGIC.
  unfold crc_api_post. eapply canonical_contract_transport.
  unfold canonical_register_state,MS. cbn. unfold mkR_of. cbn.
  rewrite H0,H1,H2. apply adler32_combine_spec;assumption.
Qed.
