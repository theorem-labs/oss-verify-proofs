(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Module RF_enframe.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
Definition renframe_tail_mem (m : word -> option byte) (P E n k q : Z) : word -> option byte :=
  let m1 := write_to_mem m (wa (P - 3)) [b8 k] in
  let m2 := write_to_mem m1 (wa (P - 2)) (le2 (wz q)) in
  let r := E - P - n in
  let m3 := if r =? 0 then m2 else write_to_mem m2 (wa (E - r)) [b8 0] in
  let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m3, r) in
  write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].

Definition ren3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw : word) (F : bvmap 5 word) (fc : bv 32)
   (m : word -> option byte) (P E n k q : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 pw a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ m' = renframe_tail_mem m P E n k q
    /\ mem_inv psegs m'.

Lemma lor_shl5 r k : 0 <= k < 32 -> 0 <= r -> Z.lor (r * 2 ^ 5) k = Z.land k 31 + Z.shiftl r 5.
Proof using .
  intros Hk Hr. replace (Z.land k 31) with k by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (D : Z.land (r * 2 ^ 5) k = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 5).
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - replace (Z.testbit k i) with false; [apply andb_false_r|]. symmetry.
      destruct (Z.eq_dec k 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply (Z.lt_le_trans _ 5); [|lia]. apply Z.log2_lt_pow2; lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- (Z.add_nocarry_lxor _ _ D). lia.
Qed.

Ltac read_k := lazymatch goal with BKc : bytes_at psegs ?mc (?P - 3) [b8 ?k] |- _ =>
      pose proof (bytes_at_read psegs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
      cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
      change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.
(* [comment removed for export] *)
Ltac sok off len addr := lazymatch goal with W : wr_at psegs ?mc (?P - 3) _ |- _ =>
    let H := fresh "SO" in
    pose proof (wr_at_store_ok psegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
    replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.

(* [comment removed for export] *)
Lemma renframe_tail_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 gw a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0w nw : word) F fc m
    (P0 P E B n k stride : Z),
  bv_unsigned p0w = P0 -> bv_unsigned nw = n -> E = P0 + stride - 4 ->
  mem_inv psegs m ->
  wr_at psegs m (P - 3) (E - P + 3) ->
  E + 1 <= 2^64 -> B + 16 <= P -> P0 <= P -> P + n <= E -> E - P - n < 2^31 -> P - B < 2^31 -> 16 <= P0 -> 0 <= B -> 0 <= n -> 0 <= k < 32 ->
  0 <= stride ->
  evt psegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 P) F fc m P E n k ((P - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw (Z_to_bv 64 P) (Z_to_bv 64 stride) p0w (wz B) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x169a0) fc None m (seg_rom psegs)).
Proof.
  intros until stride. intros HP0 HN HE MI WR ETOP BP P0P PNE EP PB P16 B0 N0 HK S0.
  pose proof (bv_unsigned_in_range _ p0w) as PWR. change (bv_modulus 64) with (2^64) in PWR.
  set (r := E - P - n).
  assert (K31 : Z.land k 31 = k) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  (* [comment removed for export] *)
  step.
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit P), (wz_unsigned B), (swrap32_small (P - B)) by lia.
  (* [comment removed for export] *)
  step. rewrite HN.
  (* [comment removed for export] *)
  step. rewrite HP0. replace (P0 + stride + -4) with E by lia.
  (* [comment removed for export] *)
  step. step. rewrite (unsigned_lit (P - B + -16)), Z.shiftr_div_pow2 by lia.
  change (2 ^ 4) with 16. replace (P - B + -16) with (P - B - 16) by lia.
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
  replace (E - (n + P)) with r by lia.
  (* [comment removed for export] *)
  sok 0 1%nat (P + -3).
  step. rewrite (le1_wz k) by lia. sdk.
  lazymatch goal with E2 : ?mc = write_to_mem ?mp (wa ?a) [b8 k] |- _ =>
    pose proof (bytes_at_write_same psegs mp a [b8 k] ltac:(lia) ltac:(cbn; lia)) as BK; rewrite <- E2 in BK;
    replace a with (P - 3) in BK by lia end.
  (* [comment removed for export] *)
  sok 1 2%nat (P + -2).
  step. change (le2 (Z_to_bv 64 ((P - B - 16) / 16))) with (le2 (wz ((P - B - 16) / 16))). sdk.
  (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  - (* [comment removed for export] *)
    step. step.
    (* [comment removed for export] *)
    read_k. step. clear RK. rewrite ?zxb_b8 by lia.
    step. rewrite ?(wz_unsigned k), ?K31 by lia. step. step. rewrite ?(unsigned_lit 0), ?(unsigned_lit k) by lia.
    rewrite Z.lor_0_l.
    sok 0 1%nat (P + -3).
    step. change (le1 (Z_to_bv 64 k)) with (le1 (wz k)). rewrite (le1_wz k) by lia. sdk.
    step. step.
    apply evt_done. unfold ren3_post. nexists 15%nat. split; [reflexivity|].
    split; [|assumption].
    unfold renframe_tail_mem. fold r. rewrite KR. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta.
    rewrite K31. change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r.
    repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
    repeat (f_equal; try (unfold wa; f_equal; lia)).
  - (* [comment removed for export] *)
    step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (n + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    + (* [comment removed for export] *)
      step.
      read_k. step. clear RK. rewrite ?zxb_b8 by lia.
      step. rewrite ?(wz_unsigned k), ?K31 by lia.
      step. rewrite (unsigned_lit r), Z.shiftl_mul_pow2 by lia.
      step. rewrite (unsigned_lit (r * 2 ^ 5)), (unsigned_lit k) by lia. rewrite (lor_shl5 r k) by lia.
      sok 0 1%nat (P + -3).
      step. rewrite (le1_wz (Z.land k 31 + Z.shiftl r 5)) by (rewrite K31, Z.shiftl_mul_pow2 by lia; lia). sdk.
      step. step.
      apply evt_done. unfold ren3_post. nexists 15%nat. split; [reflexivity|].
      split; [|assumption].
      unfold renframe_tail_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
    + (* [comment removed for export] *)
      sok (E - P - 2) 1%nat (P0 + stride + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - P - 1) 4%nat (P0 + stride + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      read_k. step. clear RK. rewrite ?zxb_b8 by lia.
      step. rewrite ?(wz_unsigned k), ?K31 by lia.
      step. step. rewrite ?(unsigned_lit 5), (unsigned_lit k) by lia. change (5 ≪ 5) with (5 * 2 ^ 5). rewrite (lor_shl5 5 k) by lia.
      sok 0 1%nat (P + -3).
      step. rewrite (le1_wz (Z.land k 31 + Z.shiftl 5 5)) by (rewrite K31; change (Z.shiftl 5 5) with 160; lia). sdk.
      step. step.
      apply evt_done. unfold ren3_post. nexists 15%nat. split; [reflexivity|].
      split; [|assumption].
      unfold renframe_tail_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.

(* [comment removed for export] *)
Definition renframe_off_mem (m : word -> option byte) (P0 off : Z) : word -> option byte :=
  if off =? 0 then m
  else write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 3)) [b8 224]) (wa (P0 - 2)) (le2 (wz off)))
                    (wa (P0 + 16 * off - 4)) [b8 0].

(* [comment removed for export] *)
Lemma renframe_off_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 gw a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0w nw prev next : word) F fc m
    (P0 B stride n k off avail freed mword : Z),
  bv_unsigned p0w = P0 -> bv_unsigned nw = n ->
  mem_inv psegs m ->
  rw_cells psegs m (bv_unsigned gw) [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  wr_at psegs m (P0 - 4) stride ->
  P0 + stride <= 2^64 -> (P0 + stride <= bv_unsigned gw \/ bv_unsigned gw + 40 <= P0 - 4) ->
  B + 16 <= P0 -> 0 <= B -> 0 <= n -> n + 4 <= stride -> stride - 4 - n < 2^31 -> P0 + 16 * off - B < 2^31 -> 16 <= P0 -> 0 <= k < 32 ->
  0 <= off -> 16 * off <= stride - 4 - n ->
  evt psegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw a3 (Z_to_bv 64 stride) p0w (wz B) (Z_to_bv 64 off) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1697c) fc None m (seg_rom psegs)).
Proof.
  intros until mword. intros HP HN MI MM WR PTOP SEPG BP B0 N0 NS SS PBS P16 HK OFF0 OFFS.
  pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.
  (* [comment removed for export] *)
  step. step. if_cases KO; zify_cond KO; rewrite ?(unsigned_lit off) in KO by lia.
  - (* [comment removed for export] *)
    subst off. unfold renframe_off_mem. rewrite Z.eqb_refl.
    replace (P0 + 16 * 0) with P0 by lia.
    replace p0w with (Z_to_bv 64 P0) by (rewrite <- HP; apply Z_to_bv_bv_unsigned).
    eapply renframe_tail_walk with (P0 := P0) (E := P0 + stride - 4); try eassumption; try lia.
    + apply unsigned_lit. lia.
    + eapply wr_at_sub; [exact WR | lia | lia].
  - (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit off), Z.shiftl_mul_pow2, (swrap32_small (off * 2 ^ 4)) by lia.
    step. rewrite HP.
    pose proof (wr_at_store_ok psegs m _ _ 1 1 WR ltac:(lia) ltac:(lia)) as SO1.
    replace (P0 - 4 + 1) with (bv_unsigned p0w + -3) in SO1 by lia.
    change (wa (bv_unsigned p0w + -3)) with (Z_to_bv 64 (bv_unsigned p0w + -3)) in SO1.
    step. rewrite le1_neg32. sdk.
    lazymatch goal with W : wr_at psegs ?mc (P0 - 4) _ |- _ =>
      pose proof (wr_at_store_ok psegs mc _ _ 2 2 W ltac:(lia) ltac:(lia)) as SO2;
      replace (P0 - 4 + 2) with (bv_unsigned p0w + -2) in SO2 by lia;
      change (wa (bv_unsigned p0w + -2)) with (Z_to_bv 64 (bv_unsigned p0w + -2)) in SO2 end.
    step. change (le2 (Z_to_bv 64 off)) with (le2 (wz off)). sdk.
    lazymatch goal with W : wr_at psegs ?mc (P0 - 4) _ |- _ =>
      pose proof (wr_at_store_ok psegs mc _ _ (16 * off) 1 W ltac:(lia) ltac:(lia)) as SO3;
      replace (P0 - 4 + 16 * off) with (P0 + off * 2 ^ 4 + -4) in SO3 by lia;
      change (wa (P0 + off * 2 ^ 4 + -4)) with (Z_to_bv 64 (P0 + off * 2 ^ 4 + -4)) in SO3 end.
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    step.
    replace (P0 + off * 2 ^ 4) with (P0 + 16 * off) by lia.
    unfold renframe_off_mem. replace (off =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      replace (write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 3)) [b8 224]) (wa (P0 - 2)) (le2 (wz off))) (wa (P0 + 16 * off - 4)) [b8 0])
        with mc end.
    2:{ repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
        repeat (f_equal; try (unfold wa; f_equal; lia)). }
    eapply renframe_tail_walk with (P0 := P0) (E := P0 + stride - 4); try eassumption; try lia.
    eapply wr_at_sub; [exact WR | lia | lia].
Qed.

Lemma swrap32_add_2p64 d : -2^31 <= d < 2^31 -> bv_swrap 32 (18446744073709551616 + d) = d.
Proof.
  intros Hd. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  replace (18446744073709551616 + d + 2147483648) with ((d + 2147483648) + 4294967296 * 4294967296) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma renframe_fold_walk : forall (ra sp gp tp t2 s0 s1 gw a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0w nw prev next : word) F fc m
    (P0 B stride n k off0 avail freed mword T0 : Z),
  let slack := (stride - 4 - n) / 16 in
  let off := fold_off off0 slack in
  bv_unsigned p0w = P0 -> bv_unsigned nw = n -> T0 = stride - 4 - n ->
  mem_inv psegs m ->
  rw_cells psegs m (bv_unsigned gw) [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  wr_at psegs m (P0 - 4) stride ->
  P0 + stride <= 2^64 -> (P0 + stride <= bv_unsigned gw \/ bv_unsigned gw + 40 <= P0 - 4) ->
  B + 16 <= P0 -> 0 <= B -> 0 <= n -> n + 4 <= stride -> stride - 4 - n < 2^31 ->
  (forall off', 0 <= off' -> 16 * off' + n + 4 <= stride -> P0 + 16 * off' - B < 2^31) -> 16 <= P0 -> 0 <= k < 32 ->
  0 <= off0 < 256 ->
  evt psegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp (Z_to_bv 64 T0) (Z_to_bv 64 slack) t2 s0 s1
               gw (wz k) nw a3 (Z_to_bv 64 stride) p0w (wz B) (Z_to_bv 64 off0) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16940) fc None m (seg_rom psegs)).
Proof.
  intros until T0. intros slack off HP HN HT0 MI MM WR PTOP SEPG BP B0 N0 NS SS PBS P16 HK OF.
  assert (SL : 0 <= slack <= stride) by (subst slack; Z.div_mod_to_equations; lia).
  pose proof (fold_off_le_slack off0 slack OF ltac:(lia)) as FO. fold off in FO.
  assert (S16 : 16 * slack <= stride - 4 - n) by (subst slack; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?(unsigned_lit slack), ?(unsigned_lit off0) in K1 by lia.
  - (* [comment removed for export] *)
    assert (EO : off = off0) by (subst off; rewrite fold_off_eq; replace (slack <? off0) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    rewrite EO. eapply renframe_off_walk; try eassumption; try lia; try (apply PBS; lia).
  - (* [comment removed for export] *)
    step. rewrite (unsigned_lit T0), HT0 by lia.
    replace ((stride - 4 - n) ≫ 5) with (slack ≫ 1) by (subst slack; rewrite <- (Z.shiftr_div_pow2 _ 4), Z.shiftr_shiftr by lia; reflexivity).
    pose proof (Z_shiftr_range slack 1 ltac:(lia) ltac:(lia)) as R1.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (slack ≫ 1)), (unsigned_lit slack) by lia.
    set (m1 := Z.lor slack (slack ≫ 1)).
    pose proof (Z_lor_range slack (slack ≫ 1) ltac:(lia) R1) as RM1. fold m1 in RM1.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit m1) by lia. pose proof (Z_shiftr_range m1 2 RM1 ltac:(lia)) as R2.
    step. rewrite (unsigned_lit m1), (unsigned_lit (m1 ≫ 2)) by lia. rewrite (Z.lor_comm (m1 ≫ 2) m1).
    set (m2 := Z.lor m1 (m1 ≫ 2)). pose proof (Z_lor_range m1 (m1 ≫ 2) RM1 R2) as RM2. fold m2 in RM2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit m2) by lia. pose proof (Z_shiftr_range m2 4 RM2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit m2), (unsigned_lit (m2 ≫ 4)) by lia. rewrite (Z.lor_comm (m2 ≫ 4) m2).
    set (m3 := Z.lor m2 (m2 ≫ 4)). pose proof (Z_lor_range m2 (m2 ≫ 4) RM2 R3) as RM3. fold m3 in RM3.
    assert (SM : m3 = smear slack) by reflexivity.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit off0), (unsigned_lit m3) by lia.
    set (x := Z.land off0 m3).
    assert (RX : 0 <= x <= off0) by (subst x; split; [apply Z.land_nonneg; lia | apply land_le_l; lia]).
    (* [comment removed for export] *)
    step. rewrite v_sltu_b2z, (unsigned_lit slack), (unsigned_lit x) by lia.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit slack) by lia.
    destruct (Z.ltb_spec slack x) as [LT|GE]; cbn [Z.b2z].
    + pose proof (fold_assert_ok off0 slack OF ltac:(lia) ltac:(rewrite <- SM; exact LT)) as FA. rewrite <- SM in FA. fold x in FA.
      step. step. rewrite (zb_lxor_ones slack) by lia. rewrite (unsigned_lit (18446744073709551615 - slack)) by lia.
      change 18446744073709551615 with (Z.ones 64) at 1. rewrite (Z.land_comm (Z.ones 64)), Z.land_ones by lia.
      rewrite (Z.mod_small (18446744073709551615 - slack)) by lia.
      step. rewrite (unsigned_lit (18446744073709551615 - slack)), (unsigned_lit x) by lia.
      replace (18446744073709551615 - slack + x) with (18446744073709551616 + (x - (slack + 1))) by lia.
      rewrite swrap32_add_2p64 by lia.
      (* [comment removed for export] *)
      step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit slack), ?(unsigned_lit (x - (slack + 1))) in K2 by lia; [|exfalso; lia].
      assert (EO : off = x - (slack + 1)).
      { subst off. rewrite fold_off_eq. replace (slack <? off0) with true by (symmetry; apply Z.ltb_lt; lia). cbv zeta.
        rewrite <- SM. fold x. replace (slack <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
      rewrite EO. eapply renframe_off_walk; try eassumption; try lia; try (apply PBS; lia).
    + step. step. change (Z.land 0 _) with 0.
      step. rewrite (unsigned_lit x), Z.add_0_l, (swrap32_small x) by lia.
      step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit slack), ?(unsigned_lit x) in K2 by lia; [|exfalso; lia].
      assert (EO : off = x).
      { subst off. rewrite fold_off_eq. replace (slack <? off0) with true by (symmetry; apply Z.ltb_lt; lia). cbv zeta.
        rewrite <- SM. fold x. replace (slack <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite EO. eapply renframe_off_walk; try eassumption; try lia; try (apply PBS; lia).
Qed.

Lemma land_m4096 a : 0 <= a < 2^64 -> Z.land a 18446744073709547520 = a - a mod 4096.
Proof using .
  intros Ha.
  replace (a - a mod 4096) with (Z.shiftl (Z.shiftr a 12) 12) by (rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; change (2^12) with 4096; Z.div_mod_to_equations; lia).
  change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, !Z.testbit_ones by lia.
  destruct (Z.lt_ge_cases i 12).
  - rewrite Z.shiftl_spec_low by lia. replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
    replace (i <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb negb]. rewrite !andb_false_r. reflexivity.
  - rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 12 + 12) with i by lia.
    replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
    replace (i <? 12) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (Z.lt_ge_cases i 64).
    + replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn. rewrite andb_true_r. reflexivity.
    + replace (Z.testbit a i) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec a 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia|lia].
Qed.

(* [comment removed for export] *)
Lemma renframe_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gw nw prev next : word) F fc m
    (B stride n k ctr avail freed last_idx freeable sc maplen vb3 v16 : Z),
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let P0 := B + 16 + stride * k in
  let slack := (stride - 4 - n) / 16 in
  let off0 := (if vb3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255) in
  let off := fold_off off0 slack in
  bv_unsigned nw = n ->
  stride = (if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc) ->
  ((last_idx =? 0) && negb (maplen =? 0) = false -> sc < 48) ->
  mem_inv psegs m ->
  rw_cells psegs m (bv_unsigned gw) [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  wr_at psegs m (P0 - 4) stride ->
  ov_read_bytes psegs m (wa (P0 - 3)) 1 = Some [b8 vb3] ->
  ov_read_bytes psegs m (wa (P0 - 2)) 2 = Some (le2 (wz v16)) ->
  ov_read_bytes psegs m (wa (P0 - 4)) 1 = Some [b8 0] ->
  P0 + stride <= 2^64 -> (P0 + stride <= bv_unsigned gw \/ bv_unsigned gw + 40 <= P0 - 4) ->
  0 <= B -> 0 <= n -> n + 4 <= stride -> stride - 4 - n < 2^31 ->
  (forall off', 0 <= off' -> 16 * off' + n + 4 <= stride -> P0 + 16 * off' - B < 2^31) -> 0 <= k < 32 ->
  0 <= ctr < 2^32 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  0 <= vb3 < 256 -> 0 <= v16 < 65536 ->
  evt psegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw (wz (sxv ctr)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x168c4) fc None m (seg_rom psegs)).
Proof using .
  intros until v16. intros mword P0 slack off0 off HN HS SC48 MI MM WR R3 R2 R4 PTOP SEPG B0 N0 NS SS PBS HK CT LI FB SC ML VB V16.
  pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (MW5 : Z.land (Z.shiftr mword 5) 126 = 2 * sc) by (subst mword; apply mword_sc; lia).
  assert (MW12 : Z.land mword 18446744073709547520 = 4096 * maplen).
  { rewrite land_m4096 by lia. subst mword. Z.div_mod_to_equations. lia. }
  assert (MZ : Z.shiftr mword 12 = maplen).
  { rewrite Z.shiftr_div_pow2 by lia. subst mword. change (2^12) with 4096. Z.div_mod_to_equations. lia. }
  assert (L255 : Z.land (sxv ctr) 255 = Z.land ctr 255).
  { change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
    rewrite <- (mod_mod_pow2 (sxv ctr) 8 32), sxv_mod32, (mod_mod_pow2 ctr 8 32) by lia. reflexivity. }
  assert (OF0 : 0 <= off0 < 256).
  { subst off0. destruct (vb3 =? 0); (split; [apply Z.land_nonneg; lia|]);
      change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia. }
  assert (SK0 : 0 <= stride * k) by (apply Z.mul_nonneg_nonneg; lia).
  assert (ST16 : 16 <= stride /\ B + 16 <= P0).
  { split; [| subst P0; lia]. rewrite HS. destruct ((last_idx =? 0) && negb (maplen =? 0)) eqn:E.
    - apply andb_prop in E. destruct E as [_ E2]. destruct (Z.eqb_spec maplen 0); [discriminate|]. lia.
    - pose proof (size_class_range sc ltac:(specialize (SC48 eq_refl); lia)). lia. }
  destruct ST16 as [ST16 BP0].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. rewrite (wz_unsigned mword), MZ by lia.
  (* [comment removed for export] *)
  assert (JOIN : forall a5',
    evt psegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw (wz (sxv ctr)) (Z_to_bv 64 stride) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16904) fc None m (seg_rom psegs))).
  { intros a5'.
    pose proof (sxv_range ctr) as RC.
    assert (Eoff0 : off0 = (if vb3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255)) by reflexivity.
    assert (EP0 : P0 = B + 16 + stride * k) by reflexivity.
    assert (Eoff : off = fold_off off0 slack) by reflexivity.
    assert (Esl : slack = (stride - 4 - n) / 16) by reflexivity.
    clearbody off slack off0 P0 mword. clear MW1 MW5 MW12 MZ HS SC48.
    (* [comment removed for export] *)
    step. step. step. rewrite ?(wz_unsigned k), ?(wz_unsigned B), ?(unsigned_lit stride) by lia.
    (* [comment removed for export] *)
    replace (wa (P0 - 3)) with (Z_to_bv 64 (B + stride * k + 13)) in R3 by (unfold wa; f_equal; lia).
    lazymatch type of R2 with ?T => change T with (frozen T) in R2 end.
    lazymatch type of R4 with ?T => change T with (frozen T) in R4 end.
    step. rewrite ?zxb_b8 by lia. clear R3.
    (* [comment removed for export] *)
    step. rewrite HN. step. step. replace (B + stride * k + 16) with P0 by lia.
    set (p0w := Z_to_bv 64 P0). assert (HP0 : bv_unsigned p0w = P0) by (subst p0w; apply unsigned_lit; lia). clearbody p0w.
    replace (wa (P0 - 2)) with (Z_to_bv 64 (bv_unsigned p0w + -2)) in R2 by (unfold wa; f_equal; lia).
    replace (wa (P0 - 4)) with (Z_to_bv 64 (bv_unsigned p0w + -4)) in R4 by (unfold wa; f_equal; lia).
    (* [comment removed for export] *)
    step. if_cases KB; zify_cond KB; rewrite ?(wz_unsigned vb3), ?(unsigned_lit vb3) in KB by lia.
    - (* [comment removed for export] *)
      clear R2. unfold frozen in R4. step. rewrite ?zxb_b8 by lia. clear R4.
      step. rewrite (unsigned_lit (stride + - n + -4)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
      replace ((stride + - n + -4) / 16) with ((stride - 4 - n) / 16) by (f_equal; lia).
      step. rewrite ?(wz_unsigned (sxv ctr)), ?L255 by lia.
      step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?(wz_unsigned 0), ?(unsigned_lit 0) in K4 by lia. lia. }
      replace (Z.land ctr 255) with off0 by (rewrite Eoff0, KB; reflexivity).
      rewrite Eoff, Esl. eapply renframe_fold_walk.
      all: lazymatch goal with
           | |- rw_cells _ _ _ [_; _; _; _; _; _] => exact MM
           | |- mem_inv _ _ => exact MI
           | |- wr_at _ _ _ _ => exact WR
           | |- _ => idtac end.
      all: first [lia | exact PBS].
    - (* [comment removed for export] *)
      unfold frozen in R2.
      step. rewrite ?zx16_wz by lia. clear R2. step. rewrite (wz_unsigned v16) by lia.
      unfold frozen in R4. step. rewrite ?zxb_b8 by lia. clear R4.
      step. rewrite (unsigned_lit (stride + - n + -4)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
      replace ((stride + - n + -4) / 16) with ((stride - 4 - n) / 16) by (f_equal; lia).
      step. rewrite ?(unsigned_lit (v16 + 1)) by lia.
      step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?(wz_unsigned 0), ?(unsigned_lit 0) in K4 by lia. lia. }
      replace (Z.land (v16 + 1) 255) with off0 by (rewrite Eoff0; replace (vb3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      rewrite Eoff, Esl. eapply renframe_fold_walk.
      all: lazymatch goal with
           | |- rw_cells _ _ _ [_; _; _; _; _; _] => exact MM
           | |- mem_inv _ _ => exact MI
           | |- wr_at _ _ _ _ => exact WR
           | |- _ => idtac end.
      all: first [lia | exact PBS]. }
  (* [comment removed for export] *)
  assert (JOIN2 : forall a5', stride = 16 * size_class sc -> sc < 48 ->
    evt psegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw (wz (sxv ctr)) (wz mword) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x168e8) fc None m (seg_rom psegs))).
  { intros a5' HS16 SC'.
    lazymatch type of R2 with ?T => change T with (frozen T) in R2 end.
    lazymatch type of R3 with ?T => change T with (frozen T) in R3 end.
    lazymatch type of R4 with ?T => change T with (frozen T) in R4 end.
    pose proof (Z_shiftr_range mword 5 MWR ltac:(lia)) as R5.
    pose proof (size_class_range sc ltac:(lia)) as SZ.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned mword) by lia. step. step. rewrite (unsigned_lit (mword ≫ 5)), MW5 by lia.
    step. step. rewrite ?(unsigned_lit (2 * sc)) by lia.
    pose proof (rsize_classes_read m sc MI ltac:(lia)) as RS. unfold RSIZE_CLASSES in RS.
    (* [comment removed for export] *)
    step. rewrite ?zx16_wz by lia.
    step. rewrite (wz_unsigned (size_class sc)), Z.shiftl_mul_pow2 by lia.
    replace (size_class sc * 2 ^ 4) with stride by lia.
    apply JOIN. }
  (* [comment removed for export] *)
  step. if_cases KM; zify_cond KM; rewrite ?(unsigned_lit maplen) in KM by lia.
  - (* [comment removed for export] *)
    apply JOIN2; [| apply SC48]; rewrite ?HS; replace (maplen =? 0) with true by (symmetry; apply Z.eqb_eq; lia); rewrite ?andb_false_r; cbn [negb andb]; try reflexivity.
    all: destruct (last_idx =? 0); reflexivity.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned mword), MW1 by lia.
    step. if_cases KL; zify_cond KL; rewrite ?(unsigned_lit last_idx) in KL by lia.
    + (* [comment removed for export] *)
      apply JOIN2; [| apply SC48]; rewrite ?HS; replace (last_idx =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity.
    + (* [comment removed for export] *)
      step. step. rewrite (wz_unsigned mword) by lia. rewrite MW12.
      step. replace (4096 * maplen + -16) with stride.
      2:{ rewrite HS. replace (last_idx =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
          replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. lia. }
      step. apply JOIN.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac read_k := lazymatch goal with BKc : bytes_at psegs ?mc (?P - 3) [b8 ?k] |- _ =>
      pose proof (bytes_at_read psegs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
      cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
      change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.
Ltac sok off len addr := lazymatch goal with W : wr_at psegs ?mc (?P - 3) _ |- _ =>
    let H := fresh "SO" in
    pose proof (wr_at_store_ok psegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
    replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.
End RF_enframe.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocRep.
Module RF_realloc_C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep RF_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition rss_mem (m : word -> option byte) (P E n k : Z) : word -> option byte :=
  let r := E - P - n in
  let m3 := if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0] in
  let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m3, r) in
  write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].

(* [comment removed for export] *)
Definition rr_frame (ra s0 s1 s2 s3 s4 s5 s6 : word) : list cell :=
  [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition rr_ret_post (sp' gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (vra v0 v1 v2 v3 v4 v5 v6 : word) (P : Z) (lo : Z) (m' : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp' + 64)) gp tp t0 t1 t2 v0 v1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc vra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp' + 64).

Section TAILS.
Variables (sp' gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (vra v0 v1 v2 v3 v4 v5 v6 : word) (lo : Z).

(* [comment removed for export] *)
Lemma rr_tail_walk : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m (P k r' : Z),
  bv_unsigned a0 = P -> a1 = Z_to_bv 64 r' -> 0 <= r' <= 5 -> 0 <= k < 256 -> 4 <= P -> P < 2^64 ->
  mem_inv psegs m ->
  bytes_at psegs m (P - 3) [b8 k] -> wr_at psegs m (P - 3) 1 ->
  rw_cells psegs m (bv_unsigned sp') (rr_frame vra v0 v1 v2 v3 v4 v5 v6) ->
  stk psegs m lo (bv_unsigned sp') -> P <= lo -> lo <= bv_unsigned sp' ->
  evt psegs (rr_ret_post sp' gp tp s7 s8 s9 s10 s11 F fc vra v0 v1 v2 v3 v4 v5 v6 P lo
               (write_to_mem m (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)]))
      (MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16f94) fc None m (seg_rom psegs)).
Proof using .
  intros until r'. intros HP -> R5 HK P4 P64 MI BK WR FR ST PLO LOSP. unfold rr_frame in FR.
  pose proof (bv_unsigned_in_range _ sp') as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (K31 : 0 <= Z.land k 31 < 32).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32. apply Z.mod_pos_bound. lia. }
  pose proof (bytes_at_read psegs m (P - 3) [b8 k] 0 1 BK ltac:(lia) ltac:(cbn; lia)) as RK.
  cbv [take drop Z.to_nat] in RK. replace (P - 3 + 0) with (bv_unsigned a0 + -3) in RK by lia.
  (* [comment removed for export] *)
  step. clear RK. rewrite ?zxb_b8 by lia.
  step. step. step. rewrite ?(unsigned_lit r'), ?(wz_unsigned k) by lia. rewrite ?(unsigned_lit (Z.land k 31)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite ?(unsigned_lit (r' * 2 ^ 5)) by (change (2^5) with 32; lia).
  rewrite (lor_shl5 r' (Z.land k 31)) by lia.
  replace (Z.land (Z.land k 31) 31) with (Z.land k 31) by (rewrite <- Z.land_assoc; reflexivity).
  rewrite (Z.shiftl_mul_pow2 r' 5) by lia.
  (* [comment removed for export] *)
  pose proof (wr_at_store_ok psegs m _ _ 0 1 WR ltac:(lia) ltac:(lia)) as SO.
  replace (P - 3 + 0) with (bv_unsigned a0 + -3) in SO by lia. change (wa (bv_unsigned a0 + -3)) with (Z_to_bv 64 (bv_unsigned a0 + -3)) in SO.
  assert (KV : 0 <= Z.land k 31 + r' * 2 ^ 5 < 256) by (change (2^5) with 32; lia).
  step. change (le1 (Z_to_bv 64 (Z.land k 31 + r' * 2 ^ 5))) with (le1 (wz (Z.land k 31 + r' * 2 ^ 5))).
  rewrite (le1_wz (Z.land k 31 + r' * 2 ^ 5)) by heap_lia_pruned. sdk.
  (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp' + 64).
  rewrite HP in EQm0. replace (P + -3) with (P - 3) in EQm0 by lia. rewrite <- EQm0.
  apply evt_done. unfold rr_ret_post. do 14 eexists.
  split; [| split; [exact MI| exact ST]].
  replace (Z_to_bv 64 P) with a0 by (rewrite <- HP; symmetry; apply Z_to_bv_bv_unsigned). reflexivity.
Qed.
End TAILS.

Section SS.
Variables (sp' gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (vra v0 v1 v2 v3 v4 v5 v6 : word) (lo : Z).

(* [comment removed for export] *)
Lemma rr_ss1_walk : forall (ra t1 t2 a0 a1 a2 a3 a4 a5 a7 t3 t4 t5 t6 : word) m (P E n k : Z),
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> 0 <= n -> P + n <= E -> E - P - n < 2^31 -> 0 <= k < 256 -> 4 <= P -> E + 1 <= 2^64 ->
  mem_inv psegs m ->
  bytes_at psegs m (P - 3) [b8 k] -> wr_at psegs m (P - 3) (E - P + 3) ->
  rw_cells psegs m (bv_unsigned sp') (rr_frame vra v0 v1 v2 v3 v4 v5 v6) ->
  stk psegs m lo (bv_unsigned sp') -> E <= lo -> lo <= bv_unsigned sp' ->
  evt psegs (rr_ret_post sp' gp tp s7 s8 s9 s10 s11 F fc vra v0 v1 v2 v3 v4 v5 v6 P lo (rss_mem m P E n k))
      (MS (mkR ra sp' gp tp (Z_to_bv 64 E) t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (E + 4)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16f58) fc None m (seg_rom psegs)).
Proof using .
  intros until k. intros HP HN N0 PNE RS HK P4 E64 MI BK WR FR ST ELO LOSP.
  pose proof (bv_unsigned_in_range _ sp') as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ a0) as A0R. change (bv_modulus 64) with (2^64) in A0R.
  set (r := E - P - n).
  (* [comment removed for export] *)
  step. rewrite HN, HP.
  step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
  replace (E - (n + P)) with r by lia.
  (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by heap_lia_pruned.
  - (* [comment removed for export] *)
    step. step.
    eapply evt_mono.
    { eapply (rr_tail_walk sp' gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc vra v0 v1 v2 v3 v4 v5 v6 lo) with (k := k) (r' := 0);
        first [exact HP| reflexivity| exact MI| exact BK| exact FR| exact ST| heap_lia_pruned| idtac].
      eapply wr_at_sub; [exact WR| lia| lia]. }
    intros ms' H. unfold rss_mem. fold r. rewrite KR. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta. exact H.
  - (* [comment removed for export] *)
    step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    pose proof (wr_at_store_ok psegs m _ _ (n + 3) 1 WR ltac:(lia) ltac:(lia)) as SO1.
    replace (P - 3 + (n + 3)) with (E - r + 0) in SO1 by lia. change (wa (E - r + 0)) with (Z_to_bv 64 (E - r + 0)) in SO1.
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    + (* [comment removed for export] *)
      step.
      eapply evt_mono.
      { eapply (rr_tail_walk sp' gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc vra v0 v1 v2 v3 v4 v5 v6 lo) with (k := k) (r' := r);
          first [exact HP| reflexivity| exact MI| exact BK| exact FR| exact ST| heap_lia_pruned| idtac].
        eapply wr_at_sub; [exact WR| lia| lia]. }
      intros ms' H. unfold rss_mem. fold r. replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      replace (E - r + 0) with (E - r) in EQm0 by lia. rewrite <- EQm0. exact H.
    + (* [comment removed for export] *)
      pose proof (wr_at_store_ok psegs m0 _ _ (E - P - 2) 1 WR ltac:(lia) ltac:(lia)) as SO2.
      replace (P - 3 + (E - P - 2)) with (E + 4 + -9) in SO2 by lia. change (wa (E + 4 + -9)) with (Z_to_bv 64 (E + 4 + -9)) in SO2.
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      pose proof (wr_at_store_ok psegs m1 _ _ (E - P - 1) 4 WR ltac:(lia) ltac:(lia)) as SO3.
      replace (P - 3 + (E - P - 1)) with (E + 4 + -8) in SO3 by lia. change (wa (E + 4 + -8)) with (Z_to_bv 64 (E + 4 + -8)) in SO3.
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      eapply evt_mono.
      { eapply (rr_tail_walk sp' gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc vra v0 v1 v2 v3 v4 v5 v6 lo) with (k := k) (r' := 5);
          first [exact HP| reflexivity| exact MI| exact BK| exact FR| exact ST| heap_lia_pruned| idtac].
        eapply wr_at_sub; [exact WR| lia| lia]. }
      intros ms' H. unfold rss_mem. fold r. replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      replace (E - r + 0) with (E - r) in EQm0 by lia. replace (E + 4 + -9) with (E - 5) in EQm1 by lia. replace (E + 4 + -8) with (E - 4) in EQm2 by lia.
      rewrite <- EQm0, <- EQm1, <- EQm2. exact H.
Qed.
End SS.

Section SS2.
Variables (sp' gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (vra v0 v1 v2 v3 v4 v5 v6 : word) (lo : Z).

(* [comment removed for export] *)
Lemma rr_ss2_walk : forall (ra t0 t1 t2 a2 a5 a7 t3 t4 t5 t6 : word) m (P E n k : Z),
  0 <= n -> 4 <= P -> P + n <= E -> E - P - n < 2^31 -> 0 <= k < 256 -> E + 1 <= 2^64 ->
  mem_inv psegs m ->
  bytes_at psegs m (P - 3) [b8 k] -> wr_at psegs m (P - 3) (E - P + 3) ->
  rw_cells psegs m (bv_unsigned sp') (rr_frame vra v0 v1 v2 v3 v4 v5 v6) ->
  stk psegs m lo (bv_unsigned sp') -> E <= lo -> lo <= bv_unsigned sp' ->
  evt psegs (rr_ret_post sp' gp tp s7 s8 s9 s10 s11 F fc vra v0 v1 v2 v3 v4 v5 v6 P lo (rss_mem m P E n k))
      (MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 (n + P)) a2 (Z_to_bv 64 (E + 4)) (Z_to_bv 64 E) a5
               (Z_to_bv 64 (bv_swrap 32 (E - (n + P)))) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16eb8) fc None m (seg_rom psegs)).
Proof using .
  intros until k. intros N0 P4 PNE RS HK E64 MI BK WR FR ST ELO LOSP.
  pose proof (bv_unsigned_in_range _ sp') as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (HP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  set (r := E - P - n).
  rewrite (swrap32_small (E - (n + P))) by lia. replace (E - (n + P)) with r by lia.
  (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by heap_lia_pruned.
  - (* [comment removed for export] *)
    step. step.
    eapply evt_mono.
    { eapply (rr_tail_walk sp' gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc vra v0 v1 v2 v3 v4 v5 v6 lo) with (k := k) (r' := 0);
        first [exact HP| reflexivity| exact MI| exact BK| exact FR| exact ST| heap_lia_pruned| idtac].
      eapply wr_at_sub; [exact WR| lia| lia]. }
    intros ms' H. unfold rss_mem. fold r. rewrite KR. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta. exact H.
  - (* [comment removed for export] *)
    step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. rewrite ?(unsigned_lit E) by lia. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    pose proof (wr_at_store_ok psegs m _ _ (n + 3) 1 WR ltac:(lia) ltac:(lia)) as SO1.
    replace (P - 3 + (n + 3)) with (E - r + 0) in SO1 by lia. change (wa (E - r + 0)) with (Z_to_bv 64 (E - r + 0)) in SO1.
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    + (* [comment removed for export] *)
      step.
      eapply evt_mono.
      { eapply (rr_tail_walk sp' gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc vra v0 v1 v2 v3 v4 v5 v6 lo) with (k := k) (r' := r);
          first [exact HP| reflexivity| exact MI| exact BK| exact FR| exact ST| heap_lia_pruned| idtac].
        eapply wr_at_sub; [exact WR| lia| lia]. }
      intros ms' H. unfold rss_mem. fold r. replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      replace (E - r + 0) with (E - r) in EQm0 by lia. rewrite <- EQm0. exact H.
    + (* [comment removed for export] *)
      pose proof (wr_at_store_ok psegs m0 _ _ (E - P - 2) 1 WR ltac:(lia) ltac:(lia)) as SO2.
      replace (P - 3 + (E - P - 2)) with (E + 4 + -9) in SO2 by lia. change (wa (E + 4 + -9)) with (Z_to_bv 64 (E + 4 + -9)) in SO2.
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      pose proof (wr_at_store_ok psegs m1 _ _ (E - P - 1) 4 WR ltac:(lia) ltac:(lia)) as SO3.
      replace (P - 3 + (E - P - 1)) with (E + 4 + -8) in SO3 by lia. change (wa (E + 4 + -8)) with (Z_to_bv 64 (E + 4 + -8)) in SO3.
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      eapply evt_mono.
      { eapply (rr_tail_walk sp' gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc vra v0 v1 v2 v3 v4 v5 v6 lo) with (k := k) (r' := 5);
          first [exact HP| reflexivity| exact MI| exact BK| exact FR| exact ST| heap_lia_pruned| idtac].
        eapply wr_at_sub; [exact WR| lia| lia]. }
      intros ms' H. unfold rss_mem. fold r. replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      replace (E - r + 0) with (E - r) in EQm0 by lia. replace (E + 4 + -9) with (E - 5) in EQm1 by lia. replace (E + 4 + -8) with (E - 4) in EQm2 by lia.
      rewrite <- EQm0, <- EQm1, <- EQm2. exact H.
Qed.
End SS2.


End CeilWrap.
End RF_realloc_C.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_entry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Realloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_ReallocM.
Module RF_realloc_D.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Realloc.

Import RF_realloc_C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section BIG.
Variables (ra sp' gp tp s0 s2 s7 s8 s9 s10 s11 t5 t6 a0 a1 gw t2v t3v a5v s3v s4v s5v s6v t4v : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (P n B sc mword maplen E rsv stride idx : Z).
Variable Q : machine_state -> Prop.
Let start := B + stride * idx + 16.
Let base := P - start.
Let nn := rr_needed n base.

Hypothesis HP : bv_unsigned a0 = P.
Hypothesis HN : bv_unsigned a1 = n.
Hypothesis N32 : 0 <= n < 2^32.
Hypothesis B0 : 0 <= B.
Hypothesis ST0 : start <= P.
Hypothesis SI0 : 0 <= stride * idx.
Hypothesis P63 : P < 2^62.
Hypothesis MW : 0 <= mword < 2^64.
Hypothesis MWP : mword - mword mod 4096 = maplen * 4096.

(* [comment removed for export] *)
Hypothesis KEQ : maplen * 4096 = nn ->
  forall a3' a5',
  evt psegs Q (MS (mkR ra sp' gp tp (Z_to_bv 64 E) (Z_to_bv 64 start) t2v (Z_to_bv 64 nn) gw a0 a1 (wz B) a3' (Z_to_bv 64 (maplen * 4096)) a5'
                    (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P)) (Z_to_bv 64 (E - rsv)) (Z_to_bv 64 base) (Z_to_bv 64 4095) s5v s6v s7 s8 s9 s10 s11 t3v t4v t5 t6)
                  F (Z_to_bv 64 0x16e80) fc None m (seg_rom psegs)).
(* [comment removed for export] *)
Hypothesis KCALL : maplen * 4096 <> nn ->
  forall a5',
  evt psegs Q (MS (mkR (Z_to_bv 64 0x16e74) sp' gp tp (Z_to_bv 64 E) (Z_to_bv 64 start) t2v (Z_to_bv 64 nn) gw (wz B) (Z_to_bv 64 (maplen * 4096)) (Z_to_bv 64 nn) (Z_to_bv 64 1) (Z_to_bv 64 (maplen * 4096)) a5'
                    (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P)) (Z_to_bv 64 (E - rsv)) (Z_to_bv 64 base) (Z_to_bv 64 4095) a0 a1 s7 s8 s9 s10 s11 t3v t4v t5 t6)
                  F (Z_to_bv 64 rmremap_entry) fc None m (seg_rom psegs)).

Lemma rr_big_walk :
  evt psegs Q (MS (mkR ra sp' gp tp (Z_to_bv 64 E) (Z_to_bv 64 start) t2v s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) a5v
                    (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E + - bv_unsigned a0)) (Z_to_bv 64 (E - rsv)) s3v s4v s5v s6v s7 s8 s9 s10 s11 t3v t4v t5 t6)
                  F (Z_to_bv 64 0x16e30) fc None m (seg_rom psegs)).
Proof using B0 HN HP KCALL KEQ MW MWP N32 P63 SI0 ST0.
  pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R.
  replace (E + - bv_unsigned a0) with (E - P) by lia.
  assert (ES : bv_unsigned (Z_to_bv 64 start) = start) by (apply unsigned_lit; subst start; lia).
  (* [comment removed for export] *)
  step. step. rewrite HP, ES. fold base. step. step.
  (* [comment removed for export] *)
  step. rewrite HN. step. rewrite ?(unsigned_lit (n + 4095)), ?(unsigned_lit base) by (subst base start; lia). step. step.
  rewrite ?(unsigned_lit (n + 4095 + base + 20)) by (subst base start; lia).
  rewrite land_pgmask by (subst base start; lia).
  assert (ENN : n + 4095 + base + 20 - (n + 4095 + base + 20) mod 4096 = nn).
  { subst nn. rewrite KB_ReallocM.rr_needed_eq. unfold UNIT, IB. f_equal; [lia|]. f_equal. lia. }
  rewrite ENN.
  (* [comment removed for export] *)
  step. rewrite ?(wz_unsigned mword) by lia. rewrite land_pgmask by lia. rewrite MWP.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (subst nn base start; try lia).
  - apply KEQ. exact K1.
  - (* [comment removed for export] *)
    step. step. step. step. step. step. step.
    apply KCALL. exact K1.
Qed.
End BIG.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rr_fin2_post (sp' gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (vra v0 v1 v2 v3 v4 v5 v6 : word) (P' E' n k G NEW mword' : Z) (prev next : word) (avail freed : Z) (lo : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists mF,
    rr_ret_post sp' gp tp s7 s8 s9 s10 s11 F fc vra v0 v1 v2 v3 v4 v5 v6 P' lo (rss_mem mF P' E' n k) ms'
    /\ munch [(G + 16, G + 24); (G + 32, G + 40); (E', E' + 1)] m mF /\ wmono psegs m mF /\ mem_inv psegs mF
    /\ rw_cells psegs mF G [C8 prev; C8 next; C8 (wz NEW); C4 (wz avail); C4 (wz freed); C8 (wz mword')]
    /\ bytes_at psegs mF E' [b8 0].

Section FIN2.
Variables (sp' gp tp s2 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (vra v0 v1 v2 v3 v4 v5 v6 : word) (lo : Z).

Lemma rr_fin2_walk : forall (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 gw prev next u5 u6 : word) m
    (P n NEW needed base G mword avail freed Bold k : Z),
  let P' := NEW + base + 16 in
  let E' := NEW + needed - 4 in
  let mword' := Z.lor (Z.land mword 4095) needed in
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> bv_unsigned gw = G ->
  0 < NEW -> NEW + needed <= lo -> NEW + needed < 2^63 -> 0 <= base -> 0 <= n -> base + 16 + n + 4 <= needed -> needed - 20 - base - n < 2^31 ->
  0 <= mword < 2^64 -> 0 <= needed -> 0 <= k < 256 -> G + 40 <= lo ->
  (G + 40 <= P' - 3 \/ E' + 1 <= G) ->
  mem_inv psegs m ->
  rw_cells psegs m G [C8 prev; C8 next; C8 (wz Bold); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  bytes_at psegs m (P' - 3) [b8 k] -> wr_at psegs m (P' - 3) (E' - P' + 4) ->
  rw_cells psegs m (bv_unsigned sp') (rr_frame vra v0 v1 v2 v3 v4 v5 v6) ->
  stk psegs m lo (bv_unsigned sp') -> lo <= bv_unsigned sp' ->
  evt psegs (rr_fin2_post sp' gp tp s7 s8 s9 s10 s11 F fc vra v0 v1 v2 v3 v4 v5 v6 P' E' n k G NEW mword' prev next avail freed lo m)
      (MS (mkR ra sp' gp tp t0 t1 t2 (Z_to_bv 64 needed) gw a0 a1 (Z_to_bv 64 NEW) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 base) (Z_to_bv 64 4095) u5 u6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16e80) fc None m (seg_rom psegs)).
Proof using .
  intros until k. intros P' E' mword' HP HN HG NEW0 NLO N63 BS0 N0 FIT RS MW ND0 HK GLO GSEP MI MM BK WR FR ST LOSP.
  pose proof (bv_unsigned_in_range _ sp') as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(G + 16, G + 24); (G + 32, G + 40); (E', E' + 1)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  assert (MWL : 0 <= Z.land mword 4095 < 4096).
  { change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (MW' : 0 <= mword' < 2^64).
  { subst mword'. pose proof (F_malloc_entry.lor_small 63 (Z.land mword 4095) needed ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
  rewrite <- HG in MM.
  (* [comment removed for export] *)
  step. step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  { exfalso. lia. }
  (* [comment removed for export] *)
  step. step. step. step. step. rewrite ?(wz_unsigned mword) by lia.
  step. step. rewrite HN. rewrite ?(unsigned_lit (NEW + base + 16)) by lia.
  step. rewrite ?(unsigned_lit (Z.land mword 4095)), ?(unsigned_lit needed) by lia. fold mword'.
  step. rewrite ?(unsigned_lit (NEW + needed + -4)), ?(unsigned_lit (n + (NEW + base + 16))) by lia.
  fold P'. replace (NEW + needed + -4) with E' by (subst E'; lia).
  (* [comment removed for export] *)
  step. step.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (wr_at_store_ok psegs mX _ _ (E' - P' + 3) 1 ltac:(eassumption) ltac:(lia) ltac:(lia)) as SO1 end.
  replace (P' - 3 + (E' - P' + 3)) with (NEW + needed + -4) in SO1 by lia. change (wa (NEW + needed + -4)) with (Z_to_bv 64 (NEW + needed + -4)) in SO1.
  step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
  replace (NEW + needed + -4) with E' in EQm0 by lia.
  assert (BE : bytes_at psegs m0 E' [b8 0]).
  { rewrite EQm0. apply bytes_at_write_same; cbn; lia. }
  replace (Z_to_bv 64 (NEW + needed)) with (Z_to_bv 64 (E' + 4)) by (f_equal; subst E'; lia).
  eapply evt_mono.
  { eapply (rr_ss2_walk sp' gp tp (Z_to_bv 64 needed) gw s2 (Z_to_bv 64 base) (Z_to_bv 64 4095) u5 u6 s7 s8 s9 s10 s11 F fc vra v0 v1 v2 v3 v4 v5 v6 lo)
      with (k := k); first [eassumption| subst P' E'; lia| idtac].
    eapply wr_at_sub; [eassumption| lia| subst P' E'; lia]. }
  intros ms' H. exists m0. split; [exact H|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [| exact BE].
  rewrite HG in *. change (Z_to_bv 64 NEW) with (wz NEW) in MM. change (Z_to_bv 64 mword') with (wz mword') in MM. exact MM.
Qed.
End FIN2.


End CeilWrap.
End RF_realloc_D.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_ntf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
Module RMallocKit_B2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.MallocKit_B2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.



(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rimplT_guard {R} o t (c : bool) (k bail : Malloc.M R) s Q ms :
  (c = true -> rimplT o k s Q ms) -> rimplT o (guard t c k bail) s Q ms.
Proof using . intros H. unfold guard. destruct c; [apply H; reflexivity| apply rimplT_undef]. Qed.

Lemma rimplT_rd8 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q)) s Q ms -> rimplT o (rd8 st q k) s Q ms.
Proof using .
  intros H. unfold rd8. unfold rdv in H.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h]; [exact H|].
  apply rimplT_peek. rewrite peek_ok_pans. exact H.
Qed.

Lemma rimplT_rd16 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> rimplT o (rd16 st q k) s Q ms.
Proof using . intros H. unfold rd16. apply rimplT_rd8, rimplT_rd8. exact H. Qed.

Lemma rimplT_rd32 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
             + 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
  rimplT o (rd32 st q k) s Q ms.
Proof using . intros H. unfold rd32. apply rimplT_rd8, rimplT_rd8, rimplT_rd8, rimplT_rd8. exact H. Qed.

(* [comment removed for export] *)
Lemma rimplT_if {R} o (c : bool) (t1 t2 : Malloc.M R) s Q ms :
  (c = true -> rimplT o t1 s Q ms) -> (c = false -> rimplT o t2 s Q ms) -> rimplT o (if c then t1 else t2) s Q ms.
Proof using . intros H1 H2. destruct c; auto. Qed.

(* [comment removed for export] *)
Lemma rrdv_range : forall o st m q r,
  rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  0 <= rdv pans_mem o st q < 256.
Proof using .
  intros o st m q r MR Hr Hk Ho. unfold rdv.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - exact (proj2 (rmrep_shadow_read st m (fst q) r (snd q) v MR Hr Hk Ho E)).
  - apply pans_mem_range.
Qed.

(* [comment removed for export] *)
Lemma rrdv_cur : forall o st mX q r (x : byte),
  rmrep st mX ->
  (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  (forall h, cell_read (get_shadow st (fst q)) (snd q) = Unknown h -> o (wa (r_base r + snd q)) = mX (wa (r_base r + snd q))) ->
  bytes_at psegs mX (r_base r + snd q) [x] ->
  rdv pans_mem o st q = bv_unsigned x.
Proof using .
  intros o st mX q r x MR Hr Hk Ho AG Hb. unfold rdv.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st mX (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read psegs mX _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite (conc_region' st q r Hr).
    destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *. rewrite (AG h eq_refl).
    destruct (mX (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). unfold alloc_ceiling in RBC.
    pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rwview_ext : forall m m' a, m' a = m a -> wview psegs m' a = wview psegs m a.
Proof using . intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.

Lemma rwr_at_agree : forall m m' A n, wr_at psegs m A n -> agree_on m m' A n -> wr_at psegs m' A n.
Proof using .
  intros m m' A n (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (rwview_ext m m') by (apply AG; lia). apply HW. exact Hi.
Qed.

Lemma rrw_cells_agree' : forall m m' A cs,
  rw_cells psegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells psegs m' A cs.
Proof.
  intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

Lemma ru64arr_agree' : forall m m' A ws,
  u64arr psegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr psegs m' A ws.
Proof using .
  intros m m' A ws [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma ru8arr_agree' : forall m m' A bs,
  u8arr psegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr psegs m' A bs.
Proof using . intros m m' A bs [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

Lemma rstk_agree : forall m m' lo hi, stk psegs m lo hi -> agree_on m m' lo (hi - lo) -> stk psegs m' lo hi.
Proof using .
  intros m m' lo hi (H0 & H1 & HS) AG. split; [exact H0|]. split; [exact H1|].
  intros a Ha. rewrite (rwview_ext m m') by (apply AG; lia). unfold mrd. rewrite (AG a) by lia. apply HS. exact Ha.
Qed.



(* [comment removed for export] *)
Definition rgrp_region_addr (st : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).

Lemma rmrep_transport_agree : forall st m m',
  rmrep st m ->
  (forall a, 0 <= a < 2^64 -> rrepfoot st a -> m' (wa a) = m (wa a)) ->
  (forall a, 0 <= a < 2^64 -> rgrp_region_addr st a -> wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None) ->
  rmrep st m'.
Proof.
  intros st m m' (WF & CX & GL & AR & GR & SH) AG WG.
  pose proof WF as (Hres & WR & DJ & WA & WGr).
  assert (TC : forall A cs, rw_cells psegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells psegs m' A cs).
  { intros A cs H HP. pose proof (rw_cells_bound psegs m A cs H). eapply rrw_cells_agree'; eauto. intros a Ha. apply AG; [lia| apply HP; exact Ha]. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    pose proof (u64arr_bound psegs m _ _ C2) as B2. pose proof (u64arr_bound psegs m _ _ C3) as B3.
    pose proof (u8arr_bound psegs m _ _ C4) as B4. pose proof (u8arr_bound psegs m _ _ C5) as B5.
    rewrite actives_length in B2. rewrite usages_length in B3. rewrite unmap_seqs_length in B4. rewrite bouncess_length in B5.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
    + eapply ru64arr_agree'; eauto. rewrite actives_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru64arr_agree'; eauto. rewrite usages_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree'; eauto. rewrite unmap_seqs_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree'; eauto. rewrite bouncess_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + apply TC; [exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
  - destruct GL as (G1 & G2 & G3 & G4 & G5). split; [|split; [|split; [|split]]].
    + apply TC; [exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. unfold RMLOCK in *. lia.
    + apply TC; [exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. unfold RNEED_LOCKS in *. lia.
    + apply TC; [exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. unfold RPAGE_SIZE in *. lia.
    + apply TC; [exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. unfold RGOT_SSP in *. lia.
    + apply TC; [exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. unfold RSSP_GUARD in *. lia.
  - intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
    split; [|split].
    + apply TC; [exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [exact Ha|lia].
    + apply TC; [exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [exact Hb|lia].
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
    destruct (WR rid r Hr) as (RB0 & _ & _ & RBC & _). unfold alloc_ceiling in RBC.
    split.
    + destruct HWr as (W0 & W1 & HW). split; [exact W0|]. split; [exact W1|].
      intros i Hi. apply WG; [lia| exists rid, r; repeat split; auto; lia| apply HW; exact Hi].
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. intros a Ha. apply AG; [lia|].
      eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rmrep_transport_agree' : forall st m m',
  rmrep st m ->
  (forall a, 0 <= a < 2^64 -> rrepfoot st a \/ rgrp_region_addr st a -> m' (wa a) = m (wa a)) ->
  rmrep st m'.
Proof.
  intros st m m' MR AG. eapply rmrep_transport_agree; [exact MR| |].
  - intros a Ha Hf. apply AG; auto.
  - intros a Ha Hg. rewrite (rwview_ext m m'); [tclose|]. apply AG; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_except_of_munch_nw : forall C W m m',
  munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof.
  intros C W m m' MU HW a Ha Hc.
  assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. rewrite (rwview_ext m m' (wa a) E). tclose.
Qed.

Lemma rpres_except_agree : forall C m m' A n,
  rpres_except C m m' -> 0 <= A -> A + n <= 2^64 -> (forall a, A <= a < A + n -> ~ C a) -> agree_on m m' A n.
Proof. intros C m m' A n HP HA HB HC a Ha. apply (HP a); [lia| apply HC; exact Ha]. Qed.

Lemma ru64arr_pres : forall C m m' A ws,
  rpres_except C m m' -> u64arr psegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> ~ C a) -> u64arr psegs m' A ws.
Proof using .
  intros C m m' A ws HP H HC. pose proof (u64arr_bound psegs m A ws H).
  eapply ru64arr_agree'; [exact H|]. eapply rpres_except_agree; eauto; lia.
Qed.

Lemma ru8arr_pres : forall C m m' A bs,
  rpres_except C m m' -> u8arr psegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> u8arr psegs m' A bs.
Proof using .
  intros C m m' A bs HP H HC. pose proof (u8arr_bound psegs m A bs H).
  eapply ru8arr_agree'; [exact H|]. eapply rpres_except_agree; eauto; lia.
Qed.



End CeilWrap.
End RMallocKit_B2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_F.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WRemap.
Module RF_realloc_K2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Realloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B RMallocKit_B2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition rr_ptrs (rid : N) (g : aptr) (st : mstate) : Prop :=
  let P := fun x => x <> rid in
  let c := ctx st in
  optr_in P (c_free_meta_head c) /\ optr_in P (c_avail_meta c) /\ optr_in P (c_meta_area_head c)
  /\ optr_in P (c_meta_area_tail c) /\ optr_in P (c_avail_meta_areas c)
  /\ (forall sc, optr_in P (active st sc))
  /\ match c_brk c with BrkLive rid' _ => P rid' | _ => True end
  /\ (forall q, optr_in P (m_prev (get_meta_rec st q)) /\ optr_in P (m_next (get_meta_rec st q))
             /\ (forall b', m_mem (get_meta_rec st q) = Some b' -> fst b' = rid -> q = g /\ b' = (rid, 0)))
  /\ (forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar))
  /\ (forall b gh, (s_groups st) !! b = Some gh -> optr_in P (g_meta gh) /\ (fst b = rid -> b = (rid, 0))).

(* [comment removed for export] *)
Definition remap_mem (m2 mF : mem) (B d on nn pa_len G : Z) : Prop :=
  (forall a, 0 <= a < 2^64 -> ~ (B <= a < B + on) -> ~ (d <= a < d + nn) -> ~ (G + 16 <= a < G + 24) -> ~ (G + 32 <= a < G + 40) ->
             mF (wa a) = m2 (wa a))
  /\ (forall i, 0 <= i < pa_len -> i <> nn - IB -> mF (wa (d + i)) = m2 (wa (B + i)))
  /\ mF (wa (d + (nn - IB))) = Some (b8 0)
  /\ (forall i, 0 <= i < nn -> mF (wa (d + i)) <> None)
  /\ (forall i, pa_len <= i < nn -> i <> nn - IB -> mF (wa (d + i)) = Some (b8 0)).

Section REMAPREP.
Variables (st1 : mstate) (L : KInv.mled) (BL1 : list blk) (LS : lhead -> list aptr).
Variables (m2 mF : mem) (c : cptr) (g : aptr) (ai : Z) (r : region) (d nn : Z).
Let rid := fst c.
Let b : aptr := (rid, 0).
Let B := r_base r.
Let on := m_maplen (MR st1 g) * 4096.
Let G := conc st1 g.
Let sA := pa_s5 st1 c g d nn.
Let mr := MR st1 g.
Let mword' := meta_word (m_set_maplen (nn / 4096) mr).

Hypothesis MRP : rmrep st1 m2.
Hypothesis PAF : (* [comment removed for export] *)
  MR sA g = pa_R' st1 g nn /\ m_last_idx (pa_R' st1 g nn) = m_last_idx mr
  /\ s_slots sA = s_slots st1 /\ s_groups sA = s_groups st1 /\ s_tick sA = s_tick st1
  /\ (forall o, 0 <= o < pa_len st1 g nn -> o <> nn - IB -> cell_read (get_shadow sA rid) o = cell_read (get_shadow st1 rid) o)
  /\ cell_read (get_shadow sA rid) (nn - IB) = Known 0
  /\ (forall o, pa_len st1 g nn <= o -> o <> nn - IB -> cell_read (get_shadow sA rid) o = Known 0)
  /\ PGSZ <= pa_len st1 g nn.
Hypothesis Hr : (s_regions st1) !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Hlen : round_up_pg (r_len r) = on.
Hypothesis Hgb : (s_groups st1) !! b = Some (mkGhdr (Some g) ai).
Hypothesis MEMg : m_mem mr = Some b.
Hypothesis MSg : meta_slot st1 g.
Hypothesis PTR : rr_ptrs rid g st1.
Hypothesis MW : 0 <= m_avail mr < 2^32 /\ 0 <= m_freed mr < 2^32 /\ 0 < m_maplen mr.
Hypothesis Hd : 0 < d.
Hypothesis Hda : d mod 4096 = 0.
Hypothesis Hnn : 2 * PGSZ <= nn.
Hypothesis Hnna : nn mod 4096 = 0.
Hypothesis HnnM : nn < 2^52 * 4096.
Hypothesis Hce : d + nn <= alloc_ceiling.
Hypothesis RFd : ranges_free ref_reserved d nn = true.
Hypothesis DJd : forall q rq, (s_regions st1) !! q = Some rq -> q <> rid ->
  r_base rq + round_up_pg (r_len rq) <= d \/ d + nn <= lr_lo rq.
Hypothesis RM : remap_mem m2 mF B d on nn (pa_len st1 g nn) G.
Definition rr_newcells : list cell :=
  [C8 (pw st1 (m_prev mr)); C8 (pw st1 (m_next mr)); C8 (wz d); C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz mword')].
Hypothesis CH : rw_cells psegs mF G rr_newcells.

Let WF := proj1 MRP.

Lemma rr_regions : s_regions sA = <[rid := pa_r' r d nn]> (s_regions st1).
Proof using Hr g. exact (pa_regions st1 c g r d nn Hr). Qed.
Lemma rr_lookup q : s_regions sA !! q = if (q =? rid)%N then Some (pa_r' r d nn) else s_regions st1 !! q.
Proof using Hr g. rewrite rr_regions. destruct (N.eqb_spec q rid) as [->|NE]; [apply lookup_insert_eq| rewrite lookup_insert_ne by congruence; reflexivity]. Qed.
Lemma rr_some q rq : s_regions sA !! q = Some rq -> (q = rid /\ rq = pa_r' r d nn) \/ (q <> rid /\ s_regions st1 !! q = Some rq).
Proof using Hr g. rewrite rr_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; injection H as <-; auto| auto]. Qed.
Lemma rr_r' : r_kind (pa_r' r d nn) = RKGroup /\ r_base (pa_r' r d nn) = d /\ r_len (pa_r' r d nn) = nn /\ round_up_pg nn = nn.
Proof using Hnna Kr. unfold pa_r'. cbn. split; [exact Kr|]. split; [reflexivity|]. split; [reflexivity|]. apply KStep.round_up_pg_aligned. exact Hnna. Qed.

Lemma rr_conc q : fst q <> rid -> conc sA q = conc st1 q.
Proof using Hr d g nn. intros NE. unfold conc, get_region. rewrite rr_lookup. destruct (N.eqb_spec (fst q) rid); [contradiction| reflexivity]. Qed.
Lemma rr_conc_b : conc sA b = d.
Proof using ACEIL B G Hr PAF mword' on. unfold conc, get_region. rewrite rr_lookup. unfold b. cbn [fst snd]. rewrite N.eqb_refl. unfold pa_r'. cbn. lia. Qed.
Lemma rr_conc_b0 : conc st1 b = B.
Proof using ACEIL G Hr PAF mword' on. unfold conc, get_region, b, rid. cbn [fst snd]. fold rid. rewrite Hr. subst B. lia. Qed.
Lemma rr_pw p : optr_in (fun x => x <> rid) p -> pw sA p = pw st1 p.
Proof using Hr d g nn. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rr_conc by exact H. reflexivity. Qed.

Lemma rr_areas_other a ar : s_areas st1 !! a = Some ar -> fst a <> rid.
Proof using PTR. intros Ha. exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PTR)))))))) a ar Ha)). Qed.

Lemma rr_meta_cells q : meta_cells sA (MR sA q) = if aptr_eqb q g then rr_newcells else meta_cells st1 (MR st1 q).
Proof using ACEIL B Hr MEMg PAF PTR.
  destruct PAF as (MRg & _). destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _ & _).
  rewrite (pa_MR st1 c g d nn). destruct (PM q) as (P1 & P2 & P3). destruct (aptr_eqb_spec q g) as [->|NE].
  - unfold meta_cells, rr_newcells, pa_R', m_set_maplen. cbn [m_prev m_next m_mem m_avail m_freed]. fold mr.
    rewrite !rr_pw by assumption. rewrite MEMg. unfold pw at 3. cbn [oconc]. rewrite rr_conc_b. reflexivity.
  - unfold meta_cells. rewrite !rr_pw by assumption. f_equal. f_equal. f_equal.
    destruct (m_mem (MR st1 q)) as [b'|] eqn:Em; [| reflexivity].
    destruct (N.eq_dec (fst b') rid) as [E|NE']; [exfalso; exact (NE (proj1 (P3 b' Em E)))|].
    unfold pw. cbn [oconc]. rewrite rr_conc by exact NE'. reflexivity.
Qed.


(* [comment removed for export] *)
Definition rr_mod (a : Z) : Prop :=
  (B <= a < B + on) \/ (d <= a < d + nn) \/ (G + 16 <= a < G + 24) \/ (G + 32 <= a < G + 40).

Lemma rr_F1 a : 0 <= a < 2^64 -> ~ rr_mod a -> mF (wa a) = m2 (wa a).
Proof using RM. intros Ha NM. destruct RM as (F1 & _). apply F1; [exact Ha| | | |]; intros X; apply NM; unfold rr_mod; auto 8. Qed.

Lemma rr_agree A n : (forall a, A <= a < A + n -> ~ rr_mod a) -> 0 <= A -> A + n <= 2^64 -> agree_on m2 mF A n.
Proof using ACEIL Hd PAF RM. intros H HA HN a Ha. apply rr_F1; [lia| apply H; exact Ha]. Qed.

(* [comment removed for export] *)
Lemma rr_old : 0 < B /\ B mod 4096 = 0 /\ B + on <= alloc_ceiling /\ ranges_free ref_reserved B on = true
  /\ (B + on <= 0x10000 \/ 0x55000 <= B) /\ 4096 <= on.
Proof using G Hd Hlen Hr MW PAF WF mword'.
  pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (R0 & RAL & RL & RC & RF). fold B in R0, RAL, RC, RF. rewrite Hlen in RC, RF.
  assert (ONP : 4096 <= on) by (destruct MW as (_ & _ & MP); unfold on, mr in *; lia).
  pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)). auto 7.
Qed.

Lemma rr_new : d + nn <= 0x10000 \/ 0x55000 <= d.
Proof using ACEIL B G Hnn PAF RFd mword' on. apply (rreserved_disjoint1 _ _ RFd). unfold PGSZ in Hnn. lia. Qed.

(* [comment removed for export] *)
Lemma rr_garea : exists a ar k ra, s_areas st1 !! a = Some ar /\ 0 <= k < NSLOTS /\ g = aadd a (AREA_HDR + META_SIZE * k)
  /\ s_regions st1 !! (fst a) = Some ra /\ conc st1 a = r_base ra + snd a /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len ra)
  /\ snd a mod 4096 = 0 /\ r_kind ra <> RKGroup /\ lr_lo ra <= r_base ra + snd a /\ fst a <> rid
  /\ G = conc st1 a + AREA_HDR + META_SIZE * k /\ (conc st1 a + 4096 <= 0x10000 \/ 0x55000 <= conc st1 a).
Proof using B Hd Hr Kr MSg PAF WF mword'.
  destruct MSg as (a & ar & k & Ha & Hk & Eg). pose proof WF as (_ & WR & _ & WA & _).
  destruct (WA a ar Ha) as (ra & Hra & A0 & A1 & AL & NK & LR).
  destruct (WR _ _ Hra) as (R0 & _ & _ & RC & RF). pose proof (rreserved_disjoint1 _ _ RF ltac:(pose proof (round_up_pg_ge (r_len ra)); lia)) as DI.
  exists a, ar, k, ra. refine (conj Ha (conj Hk (conj Eg (conj Hra (conj _ (conj A0 (conj A1 (conj AL (conj NK (conj LR (conj _ (conj _ _)))))))))))).
  - apply conc_region'. exact Hra.
  - intros E. rewrite E, Hr in Hra. injection Hra as <-. exact (NK Kr).
  - unfold G. rewrite Eg, conc_aadd by (rewrite Hra; eexists; reflexivity). lia.
  - rewrite (conc_region' st1 a ra Hra). lia.
Qed.

(* [comment removed for export] *)
Lemma rr_grp_zone q rq a : s_regions st1 !! q = Some rq -> q <> rid -> r_kind rq = RKGroup ->
  r_base rq <= a < r_base rq + round_up_pg (r_len rq) -> ~ rr_mod a.
Proof using DJd Hd Hlen Hr Kr MSg PAF WF.
  intros Hq NE Kq Ha. pose proof WF as (_ & WR & DJ & WA & _).
  pose proof (DJ _ _ _ _ Hq Hr NE) as D1. rewrite (lr_lo_group rq Kq), (lr_lo_group r Kr), Hlen in D1. fold B in D1.
  pose proof (DJd q rq Hq NE) as D2. rewrite (lr_lo_group rq Kq) in D2.
  destruct rr_garea as (aa & ar & k & ra & Haa & Hk & Eg & Hra & Ca & A0 & A1 & AL & NK & LR & NRa & EG & _).
  assert (NEa : fst aa <> q) by (intros E; rewrite E, Hq in Hra; injection Hra as <-; exact (NK Kq)).
  pose proof (DJ _ _ _ _ Hra Hq NEa) as D3. rewrite (lr_lo_group rq Kq) in D3.
  unfold rr_mod. unfold AREA_HDR, META_SIZE, NSLOTS in *. clear - Ha D1 D2 D3 LR EG Ca A1 A0 Hk; lia.
Qed.

(* [comment removed for export] *)
Lemma rr_cells_shift cs : rw_cells psegs m2 B cs -> Z.of_nat (cells_size cs) <= 9 -> rw_cells psegs mF d cs.
Proof using Hce Hd Hda Hlen Hnn Hr MW PAF RFd RM WF mword'.
  intros [[Hwf HB] HW] SZ. destruct RM as (_ & F2 & _ & F4 & _). destruct PAF as (_ & _ & _ & _ & _ & _ & _ & _ & PL).
  pose proof rr_old as (R0 & _ & RC & _ & RI & ON4). pose proof rr_new as NI. unfold alloc_ceiling in *. unfold PGSZ, IB in *.
  destruct HW as (W0 & W1 & W).
  split; [split; [exact Hwf|]|].
  - destruct HB as (B0 & B1 & HBt). split; [lia|]. split; [rewrite cells_bytes_length by assumption; lia|].
    intros i Hi. rewrite cells_bytes_length in Hi by assumption. specialize (HBt i ltac:(rewrite cells_bytes_length by assumption; exact Hi)).
    unfold mrd in HBt |- *. rewrite (F2 (Z.of_nat i)) by lia.
    specialize (W (Z.of_nat i) ltac:(lia)). rewrite ref_wview_overlay in W by (rewrite wa_unsigned by lia; lia).
    destruct (m2 (wa (B + Z.of_nat i))); [exact HBt| exfalso; apply W; reflexivity].
  - split; [lia|]. split; [lia|]. intros i Hi. rewrite ref_wview_overlay by (rewrite wa_unsigned by lia; lia). apply F4. lia.
Qed.

Theorem rmrep_remap : rmrep sA mF.
Proof using CH DJd Hce Hd Hda Hlen Hnn Hnna Hr Kr MEMg MSg MW PAF PTR RFd RM WF.
  pose proof MRP as (_ & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct PAF as (MRg & LIg & SLe & GRe & TKe & RDlow & RDend & RDhigh & PL).
  pose proof PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
  pose proof rr_old as (R0 & RAL & RC & RF & RI & ON4). pose proof rr_new as NI. pose proof rr_r' as (K' & B' & L' & RU').
  destruct rr_garea as (aa & ar0 & kg & ra & Haa & Hkg & Eg & Hra & Ca & A0 & A1 & ALa & NKa & LRa & NRa & EG & AIa).
  assert (ONP : 0 < on) by (destruct MW as (_ & _ & MP); unfold on, mr in *; lia).
  unfold alloc_ceiling in RC, Hce. unfold PGSZ, IB, AREA_HDR, META_SIZE, NSLOTS in *.
  assert (Hctx : ctx sA = ctx st1) by (unfold ctx; apply (pa_ctx st1 c g d nn)).
  assert (Hconc_ctx : rctx_head_cells sA = rctx_head_cells st1).
  { unfold rctx_head_cells. rewrite (rsec_ext st1 sA ltac:(rewrite Hctx; reflexivity) (pa_areas st1 c g d nn)).
    rewrite Hctx. rewrite !rr_pw by assumption. reflexivity. }
  assert (Hact : actives sA = actives st1).
  { unfold actives. apply map_ext. intros i. unfold active. rewrite Hctx. apply rr_pw. apply PA. }
  assert (Husg : usages sA = usages st1) by (unfold usages, usage; rewrite Hctx; reflexivity).
  assert (Hums : unmap_seqs sA = unmap_seqs st1) by (unfold unmap_seqs, unmap_seq; rewrite Hctx; reflexivity).
  assert (Hbnc : bouncess sA = bouncess st1) by (unfold bouncess, bounces; rewrite Hctx; reflexivity).
  assert (Htail : ctx_tail_cells sA = ctx_tail_cells st1).
  { unfold ctx_tail_cells, brk_word. rewrite Hctx.
    destruct (c_brk (ctx st1)) as [| |brid boff]; try reflexivity. rewrite (rr_conc (brid, boff)) by exact PB. reflexivity. }
  (* [comment removed for export] *)
  assert (ZIMG : forall a, 0x10000 <= a < 0x55000 -> ~ rr_mod a) by (intros a Ha; unfold rr_mod; lia).
  split; [| split; [| split; [| split; [| split]]]].
  - (* [comment removed for export] *)
    split; [rewrite (pa_reserved st1 c g d nn); exact Hres|]. split; [| split; [| split]].
    + intros q rq Hq. apply rr_some in Hq as [[-> ->]|[NE Hq]]; [| exact (WR q rq Hq)].
      rewrite B', L', RU'. unfold alloc_ceiling. split; [lia|]. split; [exact Hda|]. split; [lia|]. split; [lia| exact RFd].
    + intros q1 r1 q2 r2 H1 H2 NE.
      apply rr_some in H1 as [[-> ->]|[N1 H1]]; apply rr_some in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (DJ q1 r1 q2 r2 H1 H2 NE)].
      * rewrite B', L', RU', (lr_lo_group _ K'). destruct (DJd q2 r2 H2 N2); lia.
      * rewrite B', L', RU', (lr_lo_group _ K'). destruct (DJd q1 r1 H1 N1); lia.
    + intros a ar Ha. rewrite (pa_areas st1 c g d nn) in Ha. destruct (WA a ar Ha) as (rq & Hq & REST). exists rq.
      rewrite rr_lookup. destruct (N.eqb_spec (fst a) rid) as [E|NE]; [exfalso; exact (rr_areas_other a ar Ha E)| auto].
    + intros b0 gh Hb0. rewrite GRe in Hb0. destruct (WG b0 gh Hb0) as (rq & Hq & Kq & S0 & S1 & SAL). rewrite rr_lookup.
      destruct (N.eqb_spec (fst b0) rid) as [E|NE]; [| exists rq; auto].
      destruct (PG b0 gh Hb0) as [_ PGb]. specialize (PGb E). subst b0. exists (pa_r' r d nn). rewrite K', L', RU'. cbn [snd]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia| reflexivity].
  - (* [comment removed for export] *)
    unfold rmrep_ctx. rewrite Hconc_ctx, Hact, Htail, Husg, Hums, Hbnc.
    destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold RCTX in *.
    assert (L1 : length (actives st1) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st1) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st1) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st1) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    split; [| split; [| split; [| split; [| split]]]].
    + eapply rrw_cells_agree'; [exact C1|]. apply rr_agree; [intros a Ha; apply ZIMG; cbn in Ha; lia| lia| cbn; lia].
    + eapply ru64arr_agree'; [exact C2|]. rewrite L1. apply rr_agree; [intros a Ha; apply ZIMG; lia| lia| lia].
    + eapply ru64arr_agree'; [exact C3|]. rewrite L2. apply rr_agree; [intros a Ha; apply ZIMG; lia| lia| lia].
    + eapply ru8arr_agree'; [exact C4|]. rewrite L3. apply rr_agree; [intros a Ha; apply ZIMG; lia| lia| lia].
    + eapply ru8arr_agree'; [exact C5|]. rewrite L4. apply rr_agree; [intros a Ha; apply ZIMG; lia| lia| lia].
    + eapply rrw_cells_agree'; [exact C6|]. apply rr_agree; [intros a Ha; apply ZIMG; cbn in Ha; lia| lia| cbn; lia].
  - (* [comment removed for export] *)
    destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
    split; [| split; [| split; [| split]]]; (eapply rrw_cells_agree'; [eassumption|]; apply rr_agree; [intros a Ha; apply ZIMG; cbn in Ha; lia| lia| cbn; lia]).
  - (* [comment removed for export] *)
    intros a ar Ha. rewrite (pa_areas st1 c g d nn) in Ha. destruct (PAR a ar Ha) as [Pa Pn]. destruct (AR a ar Ha) as (HD & SLT & PD).
    destruct (rarea_conc st1 a ar WF Ha) as (rq & Hq & Cq & Sa0 & Sa1 & SaL & NKq & Rq0 & RqAL & RqC). unfold alloc_ceiling in RqC.
    pose proof (rarea_lr_lo st1 a ar rq WF Ha Hq) as LRq.
    (* [comment removed for export] *)
    assert (ZP : forall x, conc st1 a <= x < conc st1 a + 4096 -> ~ (B <= x < B + on) /\ ~ (d <= x < d + nn)).
    { intros x Hx.
      assert (NE : fst a <> rid) by exact Pa.
      pose proof (DJ _ _ _ _ Hq Hr NE) as D1. rewrite (lr_lo_group r Kr), Hlen in D1. fold B in D1.
      pose proof (DJd _ _ Hq NE) as D2. clear - Hx D1 D2 LRq Cq Sa1 Sa0; lia. }
    unfold rarea_rep. unfold AREA_HDR, META_SIZE, NSLOTS in *. rewrite (rr_conc a) by exact Pa. rewrite rr_pw by exact Pn.
    split; [| split].
    + eapply rrw_cells_agree'; [exact HD|]. apply rr_agree; [| lia| cbn; lia]. intros x Hx. cbn in Hx.
      destruct (ZP x ltac:(lia)) as [Z1 Z2]. unfold rr_mod. rewrite EG.
      destruct (decide (a = aa)) as [->|NEa]; [clear - Z1 Z2 Hx Hkg; lia|].
      (* [comment removed for export] *)
      assert (DD : conc st1 a + 4096 <= conc st1 aa \/ conc st1 aa + 4096 <= conc st1 a).
      { destruct (N.eq_dec (fst a) (fst aa)) as [E|NEr].
        - rewrite Cq, Ca. rewrite E, Hra in Hq. injection Hq as ->.
          assert (NS2 : snd a <> snd aa) by (intros E2; apply NEa; destruct a, aa; cbn in *; congruence). clear - SaL ALa NS2 A0 Sa0; Z.div_mod_to_equations; first [lia | nia].
        - pose proof (rarea_lr_lo st1 aa ar0 ra WF Haa Hra) as LRaa. pose proof (DJ _ _ _ _ Hq Hra NEr) as DJa. rewrite Cq, Ca. clear - LRaa DJa LRq Sa1 A1 Sa0 A0; lia. }
      clear - Z1 Z2 Hx DD Hkg; lia.
    + intros k Hk. rewrite rr_meta_cells. destruct (aptr_eqb_spec (aadd a (24 + 40 * k)) g) as [E|NE].
      * replace (conc st1 a + 24 + 40 * k) with G; [exact CH|].
        unfold G. rewrite <- E. rewrite conc_aadd by (rewrite Hq; eexists; reflexivity). lia.
      * eapply rrw_cells_agree'; [apply SLT; exact Hk|]. apply rr_agree; [| lia| unfold meta_cells; cbn; lia]. intros x Hx. unfold meta_cells in Hx. cbn in Hx.
        destruct (ZP x ltac:(lia)) as [Z1 Z2]. unfold rr_mod. rewrite EG.
        destruct (decide (a = aa)) as [->|NEa].
        -- assert (NKG : k <> kg) by (intros ->; apply NE; rewrite Eg; reflexivity). clear - Z1 Z2 Hx NKG Hk Hkg; lia.
        -- assert (DD : conc st1 a + 4096 <= conc st1 aa \/ conc st1 aa + 4096 <= conc st1 a).
           { destruct (N.eq_dec (fst a) (fst aa)) as [E|NEr].
             - rewrite Cq, Ca. rewrite E, Hra in Hq. injection Hq as ->.
               assert (NS2 : snd a <> snd aa) by (intros E2; apply NEa; destruct a, aa; cbn in *; congruence). clear - SaL ALa NS2 A0 Sa0; Z.div_mod_to_equations; first [lia | nia].
             - pose proof (rarea_lr_lo st1 aa ar0 ra WF Haa Hra) as LRaa. pose proof (DJ _ _ _ _ Hq Hra NEr) as DJa. rewrite Cq, Ca. clear - LRaa DJa LRq Sa1 A1 Sa0 A0; lia. }
           clear - Z1 Z2 Hx DD Hkg Hk; lia.
    + eapply rrw_cells_agree'; [exact PD|]. apply rr_agree; [| lia| cbn; lia]. intros x Hx. cbn in Hx.
      destruct (ZP x ltac:(lia)) as [Z1 Z2]. unfold rr_mod. rewrite EG.
      destruct (decide (a = aa)) as [->|NEa]; [clear - Z1 Z2 Hx Hkg; lia|].
      assert (DD : conc st1 a + 4096 <= conc st1 aa \/ conc st1 aa + 4096 <= conc st1 a).
      { destruct (N.eq_dec (fst a) (fst aa)) as [E|NEr].
        - rewrite Cq, Ca. rewrite E, Hra in Hq. injection Hq as ->.
          assert (NS2 : snd a <> snd aa) by (intros E2; apply NEa; destruct a, aa; cbn in *; congruence). clear - SaL ALa NS2 A0 Sa0; Z.div_mod_to_equations; first [lia | nia].
        - pose proof (rarea_lr_lo st1 aa ar0 ra WF Haa Hra) as LRaa. pose proof (DJ _ _ _ _ Hq Hra NEr) as DJa. rewrite Cq, Ca. clear - LRaa DJa LRq Sa1 A1 Sa0 A0; lia. }
      clear - Z1 Z2 Hx DD Hkg; lia.
  - (* [comment removed for export] *)
    intros b0 gh Hb0. rewrite GRe in Hb0. destruct (PG b0 gh Hb0) as [Pm PGb]. destruct (GR b0 gh Hb0) as (w8 & RW & Hw8). exists w8. split; [| exact Hw8].
    rewrite rr_pw by exact Pm.
    destruct (N.eq_dec (fst b0) rid) as [E|NE].
    + specialize (PGb E). subst b0. rewrite rr_conc_b. rewrite rr_conc_b0 in RW. apply rr_cells_shift; [exact RW| cbn; lia].
    + rewrite (rr_conc b0) by exact NE. destruct (rgroup_conc st1 b0 gh WF Hb0) as (rq & Hq & Cq & Kq & S0 & S16 & _).
      eapply rrw_cells_agree'; [exact RW|]. apply rr_agree; [| pose proof (WR _ _ Hq); lia| cbn; destruct (WR _ _ Hq) as (_ & _ & _ & X & _); unfold alloc_ceiling in X; lia].
      intros x Hx. cbn in Hx. apply (rr_grp_zone (fst b0) rq x Hq NE Kq). rewrite Cq in Hx. lia.
  - (* [comment removed for export] *)
    intros q rq Hq Kq. apply rr_some in Hq as [[-> ->]|[NE Hq]].
    + (* [comment removed for export] *)
      destruct RM as (F1 & F2 & F3 & F4 & F6). unfold IB in F2, F3, F6. unfold rshadow_rep. rewrite B', L', RU'. split.
      * split; [lia|]. split; [lia|]. intros i Hi. rewrite ref_wview_overlay by (rewrite wa_unsigned by lia; lia). apply F4. exact Hi.
      * intros o v Ho RD.
        assert (PRES : forall i, 0 <= i < nn -> bytes_at psegs mF (d + i) [b8 0] \/ exists w, mF (wa (d + i)) = Some w).
        { intros i Hi. right. destruct (mF (wa (d + i))) as [w|] eqn:E; [exists w; reflexivity| exfalso; exact (F4 i Hi E)]. }
        destruct (Z.eq_dec o (nn - 4)) as [->|NEo].
        { rewrite RDend in RD. injection RD as <-. split; [| lia].
          split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [| cbn in Hi; lia]. cbn [nth_error]. rewrite Z.add_0_r. unfold mrd. rewrite F3. reflexivity. }
        destruct (Z.lt_ge_cases o (pa_len st1 g nn)) as [LOW|HIGH].
        -- rewrite RDlow in RD by lia. destruct (SH rid r Hr Kr) as [HWo HBo]. rewrite Hlen in HBo. fold B in HBo.
           assert (OPL : pa_len st1 g nn <= on) by (unfold pa_len; fold on; lia).
           destruct (HBo o v ltac:(lia) RD) as [Bt Hv]. split; [| exact Hv].
           destruct Bt as (_ & _ & Bt). specialize (Bt 0%nat ltac:(cbn; lia)). cbn [nth_error] in Bt. rewrite Z.add_0_r in Bt.
           split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [| cbn in Hi; lia]. cbn [nth_error]. rewrite Z.add_0_r.
           unfold mrd in Bt |- *. rewrite (F2 o) by lia.
           destruct HWo as (_ & _ & Wo). specialize (Wo o ltac:(rewrite Hlen; lia)). rewrite ref_wview_overlay in Wo by (rewrite wa_unsigned by lia; lia).
           fold B in Wo. destruct (m2 (wa (B + o))); [exact Bt| exfalso; apply Wo; reflexivity].
        -- rewrite RDhigh in RD by lia. injection RD as <-. split; [| lia].
           split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [| cbn in Hi; lia]. cbn [nth_error]. rewrite Z.add_0_r. unfold mrd. rewrite (F6 o) by lia. reflexivity.
    + (* [comment removed for export] *)
      unfold rshadow_rep. rewrite (pa_get_shadow st1 c g d nn q). replace (q =? rid)%N with false by (symmetry; apply N.eqb_neq; exact NE).
      destruct (SH q rq Hq Kq) as [HWq HBq]. destruct (WR _ _ Hq) as (Rq0 & _ & _ & RqC & _). unfold alloc_ceiling in RqC.
      assert (AG : agree_on m2 mF (r_base rq) (round_up_pg (r_len rq))).
      { apply rr_agree; [| lia| lia]. intros x Hx. apply (rr_grp_zone q rq x Hq NE Kq). lia. }
      split; [eapply rwr_at_agree; [exact HWq| exact AG]|].
      intros o v Ho RD. destruct (HBq o v Ho RD) as [Bt Hv]. split; [| exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. intros x Hx. apply AG. cbn in Hx. lia.
Qed.
End REMAPREP.


End CeilWrap.
End RF_realloc_K2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv.
Module RF_realloc_P.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap.
Import RF_realloc_K2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


Lemma rr_ptrs_intro st LB0 L BL LS b g r m :
  CINV st LB0 -> INVL x0 st L BL LS -> rmrep st m ->
  hosts st b g -> 48 <= m_sizeclass (MR st g) ->
  s_regions st !! (fst b) = Some r -> r_kind r = RKGroup -> snd b = 0 ->
  rr_ptrs (fst b) g st.
Proof using .
  intros C INV MRP Hg Hsc Hr Kr Hb0.
  pose proof MRP as (WF & _). pose proof WF as (_ & WR & DJ & WA & WG).
  pose proof (ci_links _ _ C) as CL. pose proof (ci_heads _ _ C) as CH. pose proof (ci_mp _ _ C) as (MP1 & MP2 & MP3 & MP4 & MP5).
  assert (Eb : b = (fst b, 0)) by (destruct b as [q o]; cbn in Hb0 |- *; subst; reflexivity).
  (* [comment removed for export] *)
  assert (MS : forall q, meta_slot st q -> fst q <> fst b).
  { intros q (a & ar & k & Ha & Hk & ->) E. unfold aadd in E. cbn [fst] in E.
    destruct (WA a ar Ha) as (ra' & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. injection Hra as <-. exact (NK Kr). }
  assert (NG : forall o, ng_ptr st o -> optr_in (fun x => x <> fst b) o).
  { intros [q|] H; cbn in H |- *; [| exact I]. destruct H as (rq & Hq & NK). intros E. rewrite E, Hr in Hq. injection Hq as <-. exact (NK Kr). }
  unfold rr_ptrs. cbv zeta.
  split. { destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH; cbn; [| exact I].
           destruct (ch_free _ CH h FH) as [NX _]. apply MS. apply (cl_self _ CL). exact NX. }
  split; [apply NG; exact MP1|]. split; [apply NG; exact MP2|]. split; [apply NG; exact MP3|]. split; [apply NG; exact MP4|].
  split. { intros sc. destruct (active st sc) as [a|] eqn:HA; cbn; [| exact I].
           destruct (ch_active _ CH sc a HA) as (_ & NX & _). apply MS. apply (cl_self _ CL). exact NX. }
  split. { destruct (c_brk (ctx st)) as [| |rid boff] eqn:HB; try exact I.
           destruct (ci_bk _ _ C rid boff HB) as (rb & Hrb & Kb). intros E. rewrite E, Hr in Hrb. injection Hrb as <-. rewrite Kr in Kb. discriminate. }
  split. { intros q. split; [| split].
    - destruct (m_prev (get_meta_rec st q)) as [pv|] eqn:HP; cbn; [| exact I]. destruct (cl_prev _ CL q pv HP) as [_ M]. apply MS. exact M.
    - destruct (m_next (get_meta_rec st q)) as [nx|] eqn:HN; cbn; [| exact I]. destruct (cl_next _ CL q nx HN) as [_ M]. apply MS. exact M.
    - intros b' Hm E. pose proof (ci_memh _ _ C q b' Hm) as HH.
      destruct (alone x0 st L BL LS INV g b Hg Hsc b' q HH E) as [-> ->]. split; [reflexivity| exact Eb]. }
  split. { intros a ar Ha. split.
    - destruct (WA a ar Ha) as (ra' & Hra & _ & _ & _ & NK & _). intros E. rewrite E, Hr in Hra. injection Hra as <-. exact (NK Kr).
    - apply NG. exact (MP5 a ar Ha). }
  intros b' gh Hb'. split.
  - destruct (ci_grps _ _ C b' gh Hb') as (g' & Hg' & _). rewrite Hg'. cbn.
    assert (HH : hosts st b' g'). { exists (g_active_idx gh). rewrite Hb'. destruct gh as [gm ai]; cbn in Hg' |- *. subst. reflexivity. }
    apply MS. exact (go_slot _ _ _ (ci_gmetas _ _ C b' g' HH)).
  - intros E. destruct (ci_grps _ _ C b' gh Hb') as (g' & Hg' & _).
    assert (HH : hosts st b' g'). { exists (g_active_idx gh). rewrite Hb'. destruct gh as [gm ai]; cbn in Hg' |- *. subst. reflexivity. }
    destruct (alone x0 st L BL LS INV g b Hg Hsc b' g' HH E) as [-> ->]. exact Eb.
Qed.


End CeilWrap.
End RF_realloc_P.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_fp.
Module RMalloc_fp.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


Notation RMFACTS := (@MFACTS_g ref_reserved).

(* [comment removed for export] *)
Lemma rreserved_disjoint2 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
  (b + n <= 0x10000 \/ 0x22000 <= b) /\ (b + n <= 0x22000 \/ 0x55000 <= b).
Proof. intros b n H Hn. pose proof (rreserved_disjoint b n H). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wr8_comm p q v w st : fst p = fst q -> snd p <> snd q -> wr8 p v (wr8 q w st) = wr8 q w (wr8 p v st).
Proof using .
  intros Hf Hs.
  assert (E : forall (a b : aptr) x y s, fst a = fst b -> snd a <> snd b ->
     wr8 a x (wr8 b y s) = set_shadow (<[fst a := mkShadow (<[snd a := (Z.land x 255, s_tick s)]> (<[snd b := (Z.land y 255, s_tick s)]> (r_cells (get_shadow s (fst a))))) (r_hav (get_shadow s (fst a))) (r_havp (get_shadow s (fst a)))]> (s_shadow s)) s).
  { intros a b x y s Ef Ns. unfold wr8 at 1. unfold upd_shadow. rewrite Ef, get_shadow_wr8_same. cbn [r_cells r_hav r_havp].
    rewrite s_shadow_wr8, <- Ef. change (s_tick (wr8 b y s)) with (s_tick s). rewrite insert_insert_eq. reflexivity. }
  rewrite (E p q), (E q p) by (congruence || (symmetry; congruence) || auto). rewrite Hf.
  rewrite (insert_insert_ne _ (snd p) (snd q)) by exact Hs. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : rmrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.

Lemma rconc_b : B = r_base r + snd b.
Proof using Hr. unfold B. apply (conc_region' st2 b r Hr). Qed.

Lemma rsk_nonneg : 0 <= stride * k.
Proof using K0 P0 S16 off. apply Z.mul_nonneg_nonneg; lia. Qed.

(* [comment removed for export] *)
Lemma rwr8_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o < snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 256 ->
  rmrep (wr8 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst b, o) v stx).
Proof using B0 Hk Hr K0 NOGRP P0 S16 SPAN off.
  intros stx mx o v MRx TKx ER EG Ho Hv. pose proof rsk_nonneg.
  split; [|apply ticks_ok_wr8; exact TKx].
  apply (rmrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma rwr16_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o -> o + 2 <= snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 65536 ->
  rmrep (wr16 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le2 (wz v))) /\ ticks_ok (wr16 (fst b, o) v stx).
Proof using B0 Hk Hr K0 NOGRP P0 S16 SPAN off.
  intros stx mx o v MRx TKx ER EG Ho Ho2 Hv. pose proof rsk_nonneg.
  split; [|apply ticks_ok_wr16; exact TKx].
  apply (rmrep_wr16 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma rwr32_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o -> o + 4 <= snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 2^32 ->
  rmrep (wr32 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst b, o) v stx).
Proof using B0 Hk Hr K0 NOGRP P0 S16 SPAN off.
  intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof rsk_nonneg.
  apply (rmrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

(* [comment removed for export] *)
Lemma wr16_wr8_comm p q v w st : fst p = fst q -> snd q <> snd p -> snd q <> snd p + 1 ->
  wr8 q w (wr16 p v st) = wr16 p v (wr8 q w st).
Proof using K0 P0 off.
  intros Hf H0 H1. unfold wr16.
  rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

Lemma wr32_wr8_comm p q v w st : fst p = fst q -> snd q + 1 = snd p ->
  wr8 q w (wr32 p v st) = wr32 p v (wr8 q w st).
Proof using K0 P0 off.
  intros Hf H1. unfold wr32.
  rewrite (wr8_comm q (aadd p 3)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 2)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

Lemma renframe_mrep :
  let res := enframe_at st2 g k n off in
  rmrep (fst res) (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
  /\ ticks_ok (fst res)
  /\ conc st2 (snd res) = P0 + 16 * off /\ fst (snd res) = fst b /\ snd (snd res) = snd b + 16 + stride * k + 16 * off.
Proof using B0 FIT Hk Hmem Hr K0 MR N0 NOGRP OFF0 Q16 S16 S31 SPAN TK.
  pose proof rconc_b as CB. pose proof rsk_nonneg as SK.
  cbv zeta. unfold enframe_at. fold mr. fold stride. rewrite Hmem. cbn [default from_option id fst snd].
  unfold aadd. cbn [fst snd].
  (* [comment removed for export] *)
  set (stC := if negb (off =? 0) then _ else _).
  assert (PRE : rmrep (fst stC) (renframe_off_mem m4 P0 off) /\ ticks_ok (fst stC)
                /\ snd stC = (fst b, snd b + (UNIT + stride * k) + UNIT * off)
                /\ s_regions (fst stC) = s_regions st2 /\ s_groups (fst stC) = s_groups st2
                /\ (forall q, conc (fst stC) q = conc st2 q)).
  { subst stC. unfold renframe_off_mem. destruct (Z.eqb_spec off 0) as [E|NE]; cbn [negb fst snd].
    - subst off. rewrite Z.mul_0_r, Z.add_0_r.
      split; [exact MR|]. split; [exact TK|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
    - (* [comment removed for export] *)
      rewrite (wr16_wr8_comm (fst b, snd b + (UNIT + stride * k) + -2) (fst b, snd b + (UNIT + stride * k) + -3)) by (cbn; lia || reflexivity).
      destruct (rwr8_rep st2 m4 (snd b + (UNIT + stride * k) + -3) 224 MR TK eq_refl eq_refl) as [M1 T1]; [unfold UNIT; lia| lia|].
      destruct (rwr16_rep _ _ (snd b + (UNIT + stride * k) + -2) off M1 T1 eq_refl eq_refl) as [M2 T2]; [unfold UNIT; lia| unfold UNIT; lia| lia|].
      destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + UNIT * off + -4) 0 M2 T2 eq_refl eq_refl) as [M3 T3]; [unfold UNIT; lia| lia|].
      unfold UNIT in *.
      replace (P0 - 2) with (r_base r + (snd b + (16 + stride * k) + -2)) by (unfold P0; lia).
      replace (P0 - 3) with (r_base r + (snd b + (16 + stride * k) + -3)) by (unfold P0; lia).
      replace (P0 + 16 * off - 4) with (r_base r + (snd b + (16 + stride * k) + 16 * off + -4)) by (unfold P0; lia).
      split; [exact M3|]. split; [exact T3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity. }
  clearbody stC. destruct stC as [stc p']. cbn [fst snd] in PRE. destruct PRE as (MC & TC & -> & ERc & EGc & CONCc).
  cbn [fst snd].
  unfold renframe_tail_mem. cbv zeta.
  (* [comment removed for export] *)
  set (po := snd b + (UNIT + stride * k) + UNIT * off).
  assert (Epo : P0 + 16 * off = r_base r + po) by (unfold po, P0, UNIT; lia).
  assert (Eq : (P0 + 16 * off - B - 16) / 16 = (po - (snd b + UNIT)) / UNIT).
  { unfold po, P0, UNIT. f_equal; lia. }
  rewrite Eq.
  assert (QB : 0 <= (po - (snd b + UNIT)) / UNIT < 65536).
  { unfold po, UNIT. replace (snd b + (16 + stride * k) + 16 * off - (snd b + 16)) with (stride * k + 16 * off) by lia.
    split; [apply Z.div_pos; lia| exact Q16]. }
  (* [comment removed for export] *)
  rewrite (wr16_wr8_comm (fst b, po + -2) (fst b, po + -3)) by (cbn; lia || reflexivity).
  destruct (rwr8_rep _ _ (po + -3) k MC TC ERc EGc) as [MD TD]; [unfold po, UNIT; lia| lia|].
  destruct (rwr16_rep _ _ (po + -2) ((po - (snd b + UNIT)) / UNIT) MD TD ERc EGc) as [ME TE]; [unfold po, UNIT; lia| unfold po, UNIT; lia| lia|].
  replace (P0 + 16 * off - 2) with (r_base r + (po + -2)) by lia.
  replace (P0 + 16 * off - 3) with (r_base r + (po + -3)) by lia.
  (* [comment removed for export] *)
  unfold set_size, aadd. cbn [fst snd id].
  set (rsv := snd b + (UNIT + stride * k) + (stride - IB) - po - n).
  assert (Ersv : P0 + stride - 4 - (P0 + 16 * off) - n = rsv) by (unfold rsv, po, P0, UNIT, IB; lia).
  rewrite Ersv.
  assert (RSV : 0 <= rsv <= stride - 4 - n) by (unfold rsv, po, UNIT, IB; lia).
  set (stF := if negb (rsv =? 0) then _ else _).
  set (mF := if rsv =? 0 then _ else _).
  assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st2 /\ s_groups stF = s_groups st2).
  { subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb].
    - split; [exact ME|]. split; [exact TE|]. split; assumption.
    - destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + - rsv) 0 ME TE ERc EGc) as [MF TF]; [unfold rsv, po, UNIT, IB; lia| lia|].
      replace (P0 + stride - 4 - rsv) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + - rsv)) by (unfold P0, UNIT, IB; lia).
      split; [exact MF|]. split; [exact TF|]. split; assumption. }
  clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).
  set (stG := if 5 <=? rsv then _ else _).
  set (mG := if 5 <=? rsv then _ else _).
  assert (PG : rmrep (fst stG) (fst mG) /\ ticks_ok (fst stG) /\ snd stG = snd mG /\ 0 <= snd mG <= 5
                /\ s_regions (fst stG) = s_regions st2 /\ s_groups (fst stG) = s_groups st2).
  { subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd].
    - (* [comment removed for export] *)
      rewrite (wr32_wr8_comm (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -4) (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (cbn; lia || reflexivity).
      destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -5) 0 MF TF ERf EGf) as [M1 T1]; [unfold UNIT, IB; lia| lia|].
      destruct (rwr32_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -4) rsv M1 T1 ERf EGf) as [M2 T2]; [unfold UNIT, IB; lia| unfold UNIT, IB; lia| lia|].
      replace (P0 + stride - 4 - 4) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -4)) by (unfold P0, UNIT, IB; lia).
      replace (P0 + stride - 4 - 5) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (unfold P0, UNIT, IB; lia).
      split; [exact M2|]. split; [exact T2|]. split; [reflexivity|]. split; [lia|]. split; assumption.
    - split; [exact MF|]. split; [exact TF|]. split; [reflexivity|]. split; [lia|]. split; assumption. }
  clearbody stG mG. destruct stG as [stg r1]. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
  destruct PG as (MG & TG & -> & R2 & ERg & EGg).
  assert (KV : 0 <= Z.land k 31 + Z.shiftl r2 5 < 256).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
    assert (0 <= Z.land k 31 <= k) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]). lia. }
  destruct (rwr8_rep _ _ (po + -3) (Z.land k 31 + Z.shiftl r2 5) MG TG ERg EGg) as [MH TH]; [unfold po, UNIT; lia| exact KV|].
  split; [exact MH|]. split; [exact TH|].
  split; [|split; [reflexivity| unfold po, UNIT; lia]].
  rewrite (conc_region' st2 (fst b, po) r Hr). cbn [snd]. exact (eq_sym Epo).
Qed.
End ENFRAME.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_enframe : forall (C : Z -> Prop) m0 m4 P0 stride off n k B,
  rpres_except C m0 m4 ->
  0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= P0 -> P0 + stride <= 2^64 ->
  (forall x, P0 - 4 <= x < P0 + stride - 4 -> C x) ->
  rpres_except C m0 (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)).
Proof using .
  intros C m0 m4 P0 stride off n k B HP OFF0 N0 FIT P4 PS HC.
  assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
  assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
  assert (HO : rpres_except C m0 (renframe_off_mem m4 P0 off)).
  { unfold renframe_off_mem. destruct (off =? 0); [exact HP|].
    apply rpres_write; [| lia | cbn; lia | cbn; intros; apply HC; lia].
    apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
    apply rpres_write; [exact HP| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  unfold renframe_tail_mem. cbv zeta.
  set (mE := write_to_mem (write_to_mem (renframe_off_mem m4 P0 off) _ _) _ _).
  assert (HE : rpres_except C m0 mE).
  { subst mE. apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
    apply rpres_write; [exact HO| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  clearbody mE.
  set (rsv := P0 + stride - 4 - (P0 + 16 * off) - n).
  set (mF := if rsv =? 0 then _ else _).
  assert (HF : rpres_except C m0 mF).
  { subst mF. destruct (Z.eqb_spec rsv 0); [exact HE|]. apply rpres_write; [exact HE| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  clearbody mF.
  set (mG := if 5 <=? rsv then _ else _).
  assert (HG : rpres_except C m0 (fst mG) /\ 0 <= snd mG <= 5).
  { subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
    - split; [|lia]. apply rpres_write; [| lia | rewrite L4; lia | rewrite L4; intros; apply HC; lia].
      apply rpres_write; [exact HF| lia | cbn; lia | cbn; intros; apply HC; lia].
    - split; [exact HF| lia]. }
  clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
  apply rpres_write; [exact HG| lia | cbn; lia | cbn; intros; apply HC; lia].
Qed.

(* [comment removed for export] *)
Lemma rrdv_agree : forall st (m1 o : mem) (q : aptr) r (x : byte),
  rmrep st m1 -> unk_agree st o m1 ->
  (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  ~ grp_hdr_cov st (fst q) (snd q) ->
  bytes_at psegs m1 (r_base r + snd q) [x] ->
  rdv pans_mem o st q = bv_unsigned x.
Proof using .
  intros st m1 o q r x MR UA Hr Hk Ho NG Hb.
  unfold rdv. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st m1 (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read psegs m1 _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite (conc_region' st q r Hr).
    destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *. rewrite <- (UA (fst q) r (snd q) h Hr Hk Ho E NG).
    destruct (m1 (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). unfold alloc_ceiling in RBC.
    pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma rmeta_chunk_facts : forall st m g,
  rmrep st m -> meta_slot st g ->
  let G := conc st g in
  rw_cells psegs m G (meta_cells st (get_meta_rec st g))
  /\ 0 < G /\ G + 40 <= alloc_ceiling
  /\ (G + 40 <= 0x10000 \/ 0x22000 <= G) /\ (G + 40 <= 0x22000 \/ 0x55000 <= G)
  /\ (forall rid' r', (s_regions st) !! rid' = Some r' -> r_kind r' = RKGroup ->
        G + 40 <= r_base r' \/ r_base r' + round_up_pg (r_len r') <= G)
  /\ (exists rid0 r0, (s_regions st) !! rid0 = Some r0 /\ r_kind r0 <> RKGroup
        /\ lr_lo r0 <= G /\ G + 40 <= r_base r0 + round_up_pg (r_len r0)).
Proof.
  intros st m g MR MS G.
  split; [apply rmrep_meta_chunk; assumption|].
  pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
  destruct MS as (a & ara & kk & Ha & Hkk & Eg).
  destruct (rarea_conc st a ara WF Ha) as (rga & Hra & Ca & Sa0 & Sa1 & SaL & NK & RaB0 & RaAL & RaC).
  pose proof (rarea_lr_lo st a ara rga WF Ha Hra) as LRa.
  destruct (WR (fst a) rga Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint2 _ _ RFa ltac:(pose proof (round_up_pg_ge (r_len rga)); lia)) as [DA1 DA2].
  assert (HG : G = r_base rga + snd a + (AREA_HDR + META_SIZE * kk)).
  { subst G. rewrite Eg, conc_aadd by (rewrite Hra; eauto). rewrite (conc_region' st a rga Hra). reflexivity. }
  unfold AREA_HDR, META_SIZE, NSLOTS in HG, Hkk. clearbody G.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split.
  - intros rid' r' Hr' Hk'. pose proof (lr_lo_group r' Hk') as LR'.
    assert (NE : rid' <> fst a) by (intros ->; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
    destruct (DISJ rid' r' (fst a) rga Hr' Hra NE); lia.
  - exists (fst a), rga. split; [exact Hra|]. split; [exact NK|]. lia.
Qed.

(* [comment removed for export] *)
Lemma rregion_facts : forall st m rid r,
  rmrep st m -> (s_regions st) !! rid = Some r ->
  4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
  /\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x22000 <= r_base r)
  /\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x22000 \/ 0x55000 <= r_base r).
Proof using .
  intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
  destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  split; [|split; [exact RBAL| split; [exact RBC| split; intros Hn; destruct (rreserved_disjoint2 _ _ RFr Hn); assumption]]].
  clear RFr. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Section SLOT.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.

Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b'.
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.

Lemma rslot_facts :
  exists x3 x2 x1 : byte,
    wr_at psegs m1 (P0 - 4) stride
    /\ bytes_at psegs m1 (P0 - 4) [b8 0; b8 (bv_unsigned x3); b8 (bv_unsigned x2); b8 (bv_unsigned x1)]
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = bv_unsigned x3
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) = bv_unsigned x2
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) = bv_unsigned x1
    /\ B = r_base r + snd b /\ 4096 <= r_base r
    /\ P0 + stride <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
    /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x22000 <= r_base r).
Proof using B0 B16 HDR0 Hk Hr IDX MR S16 SMOD SPAN UA.
  pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC |- *.
  assert (CB : B = r_base r + snd b) by (apply conc_region'; exact Hr).
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst b) r Hr Hk) as [HWr HB].
  assert (WRs : wr_at psegs m1 (P0 - 4) stride) by (eapply wr_at_sub; [exact HWr| unfold P0; lia| unfold P0; lia]).
  destruct (HB (snd b + 16 + stride * idx - 4) 0 ltac:(lia) HDR0) as [Y4 _].
  assert (WR3 : wr_at psegs m1 (P0 - 3) 3) by (eapply wr_at_sub; [exact WRs|lia|lia]).
  destruct (rwr_at_bytes_exist m1 (P0 - 3) 3 WR3 ltac:(lia) ltac:(unfold P0; lia)) as (bs & Lbs & Ybs).
  destruct bs as [|x3 [|x2 [|x1 [|? ?]]]]; try discriminate. clear Lbs.
  exists x3, x2, x1.
  assert (NG : forall d, 1 <= d <= 3 -> ~ grp_hdr_cov st (fst b) (snd b + 16 + stride * idx - d)).
  { intros d Hd (b' & gh & Hb' & Hf & Hc).
    pose proof MR as (WF' & _). destruct WF' as (_ & _ & _ & _ & WG). destruct (WG b' gh Hb') as (r' & _ & _ & _ & _ & AL').
    clear - Hd Hc AL' B16 SMOD IDX S16.
    destruct (Z.mod_divide stride 16 ltac:(lia)) as [D _]. destruct (D SMOD) as [q Hq].
    assert (E : stride * idx = 16 * (q * idx)) by (rewrite Hq; ring).
    set (w := q * idx) in E. clearbody w. Z.div_mod_to_equations. lia. }
  pose proof Ybs as (_ & _ & YB).
  assert (Y3 : bytes_at psegs m1 (r_base r + (snd b + 16 + stride * idx - 3)) [x3]).
  { split; [lia|]. split; [change (Z.of_nat (length [x3])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 0%nat ltac:(cbn; lia)) as YB0. cbn [nth_error Z.of_nat] in YB0 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 3) + 0) with (P0 - 3 + 0) by (unfold P0; lia). exact YB0. }
  assert (Y2 : bytes_at psegs m1 (r_base r + (snd b + 16 + stride * idx - 2)) [x2]).
  { split; [lia|]. split; [change (Z.of_nat (length [x2])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 1%nat ltac:(cbn; lia)) as YB1. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB1 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 2) + 0) with (P0 - 3 + 1) by (unfold P0; lia). exact YB1. }
  assert (Y1 : bytes_at psegs m1 (r_base r + (snd b + 16 + stride * idx - 1)) [x1]).
  { split; [lia|]. split; [change (Z.of_nat (length [x1])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 2%nat ltac:(cbn; lia)) as YB2. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB2 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 1) + 0) with (P0 - 3 + 2) by (unfold P0; lia). exact YB2. }
  split; [exact WRs|].
  split.
  { rewrite !b8_of_byte. change [b8 0; x3; x2; x1] with ([b8 0] ++ ([x3] ++ ([x2] ++ [x1]))).
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y4); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y3); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y2); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat].
    eapply (bytes_at_at _ _ _ _ _ Y1); unfold P0; lia. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x3 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -3) with (snd b + 16 + stride * idx - 3) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y3| lia]. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x2 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -2) with (snd b + 16 + stride * idx - 2) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y2| lia]. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x1 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -2 + 1) with (snd b + 16 + stride * idx - 1) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y1| lia]. }
  split; [exact CB|]. split; [exact R4|]. split; [unfold P0; lia|]. split; [exact RC| apply RI1; unfold P0 in *; lia].
Qed.
End SLOT.

(* [comment removed for export] *)
Definition rmalloc_fp (st st' : mstate) (lo sp : Z) (a : Z) : Prop :=
  ralloc_fp (fun k => k <> RKGroup) st' lo sp a \/ new_reg_addr st st' a \/ free_slot_addr st a \/ grp_hdr_addr st a
  \/ fresh_addr st a.

Lemma rmalloc_fp_mono st sta stb lo sp a :
  (forall rid r, (s_regions sta) !! rid = Some r ->
     exists r', (s_regions stb) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof using .
  intros HR [H|[H|H]]; [| right; left | right; right; exact H].
  - destruct H as [H|[H|[H|(rid & r & Hr & Hk & Ha)]]]; [left; left; exact H| left; right; left; exact H| left; right; right; left; exact H|].
    destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
    left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [congruence|].
    assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
    pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
  - destruct H as (rid & r & Hr & Hn & Ha). destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
    exists rid, r'. split; [exact Hr'|]. split; [exact Hn|].
    assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
    pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : RMFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.

Lemma rget_meta_rec_st2 : get_meta_rec st2 g = m_set_avail (m_avail mr - 2 ^ k) mr.
Proof. unfold st2. rewrite get_meta_rec_upd_same. reflexivity. Qed.

Lemma rfast_slot_ok : exists b r,
  slot_ok st2 g b r k n
  /\ (forall a, r_base r + snd b + 16 + get_stride mr * k - 4 <= a < r_base r + snd b + 16 + get_stride mr * k + get_stride mr - 4 ->
        free_slot_addr st a)
  /\ k < 32 /\ m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r.
Proof using ACT AV K0 LBK MF N0 NFIT st1.
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  destruct (FA sc g ACT) as (SC48 & GSC & MEMnn). change (get_meta_rec st g) with mr in GSC, MEMnn.
  destruct (m_mem mr) as [b|] eqn:Hmem; [|congruence]. clear MEMnn.
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). change (get_meta_rec st g) with mr in FG. cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
  unfold UNIT, IB in *.
  assert (TBk : Z.testbit (m_avail mr) k = true) by (apply lowbit_testbit; assumption).
  pose proof (AVAI k K0 TBk) as KAI.
  assert (K32 : k < 32) by lia.
  assert (P2k : 0 < 2 ^ k <= m_avail mr).
  { split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 (m_avail mr) AV) as (k' & _ & E' & LE'). unfold lowbit in LBK.
    rewrite LBK in E'. rewrite E'. exact LE'. }
  assert (GSC48 : m_sizeclass mr < 48) by lia. specialize (S31 GSC48).
  destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
  pose proof (mf_free_clear _ _ MF g b k Hmem K0 (or_introl TBk)) as FC. cbv zeta in FC. destruct FC as [NOGRP _].
  change (get_meta_rec (strip st) g) with mr in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
  unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
  pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(change (get_meta_rec st g) with mr; lia)) as K4.
  unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4.
  change (get_meta_rec st g) with mr in K4. unfold IB, UNIT in K4.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
  exists b, r. pose proof rget_meta_rec_st2 as E2.
  split; [|split; [|split; [exact K32| split; [reflexivity| exact Hr]]]].
  - pose proof (UND GSC48 k K0 TBk) as U. rewrite GSC in U. specialize (S20 GSC48).
    constructor; rewrite ?E2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
      try change (get_stride (m_set_avail (m_avail mr - 2 ^ k) mr)) with (get_stride mr);
      first [ exact Hmem | exact Hr | exact Hk | exact MSL | exact K4 | exact NOGRP | exact N0 | exact SMOD
            | (pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with mr; lia)) as SC;
               change (get_meta_rec (strip st) g) with mr in SC; unfold sstart_of in SC; rewrite Hmem in SC;
               cbn [default from_option id snd] in SC; unfold UNIT in SC; exact SC)
            | (intros off O0 OF;
               assert (get_stride mr * k + 16 * off < get_stride mr * (k + 1)) by lia;
               assert (get_stride mr * (k + 1) <= get_stride mr * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
               apply Z.div_lt_upper_bound; lia)
            | lia ].
  - intros a Ha. exists g, b, r, k. split; [exact Hmem|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact K0|]. split; [left; exact TBk|].
    unfold sstart_of. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT, IB. fold mr.
    assert (get_stride mr * k + get_stride mr <= get_stride mr * m_last_idx mr + get_stride mr) by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
    assert (0 <= get_stride mr * k) by (apply Z.mul_nonneg_nonneg; lia).
    lia.
Qed.
End FASTFACTS.



End CeilWrap.
(* [comment removed for export] *)
Notation RMFACTS := (@MFACTS_g ref_reserved).
End RMalloc_fp.

(* [comment removed for export] *)
Module RAllocSlot_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree RMalloc_fp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


(* [comment removed for export] *)
Definition RAS_STACK (sc : Z) : Z := 288 + 144 * Z.max 0 (27 - sc).

Lemma RAS_STACK_ge sc : 288 <= RAS_STACK sc.
Proof using . unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_le sc : 0 <= sc -> RAS_STACK sc <= 4176.
Proof using . unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_mono a b : a <= b -> RAS_STACK b <= RAS_STACK a.
Proof using . unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_nest sc j : sc < j -> j <= 26 -> RAS_STACK j + 144 <= RAS_STACK sc.
Proof using . unfold RAS_STACK. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
    /\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
    /\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
    /\ mrel st st1 /\ brk_link_ps st1 s'
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ as_inv st0 st st1 sc idx
    /\ 0 <= c_mmap_counter (ctx st1) < 2^32
    /\ (idx = -1
        \/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
              /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
                           < r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
                    rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
              (* [comment removed for export] *)
              /\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Definition ralloc_slot_stmt (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop)
                           (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop) : Prop :=
  forall (fuel : nat) (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  as_pre st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells psegs m (errno_addr tp) [C4 errv] -> mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post as_inv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom psegs)).



End CeilWrap.
End RAllocSlot_iface.

(* [comment removed for export] *)
From Stdlib Require FunctionalExtensionality.
Module RF_realloc_K.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.

Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Realloc.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A RMalloc_fp RF_enframe.
Import RF_realloc_C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma write_to_mem_same_fun : forall segs m a bs,
  bytes_at segs m a bs -> (forall i, (i < length bs)%nat -> m (wa (a + Z.of_nat i)) <> None) ->
  write_to_mem m (wa a) bs = m.
Proof.
  intros segs m a bs (A0 & An & B) PR. apply functional_extensionality. intros x.
  pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR.
  rewrite write_to_mem_spec by lia.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
  specialize (B (Z.to_nat (bv_unsigned x - a)) ltac:(lia)). specialize (PR (Z.to_nat (bv_unsigned x - a)) ltac:(lia)).
  replace (a + Z.of_nat (Z.to_nat (bv_unsigned x - a))) with (bv_unsigned x) in B, PR by lia. rewrite Nodes.wa_unsigned_id in B, PR.
  unfold mrd in B. destruct (m x) as [b|]; [| exfalso; apply PR; reflexivity]. symmetry. exact B.
Qed.

(* [comment removed for export] *)
Lemma rss_mem_outside : forall m P E n k (x : word),
  0 <= n -> 4 <= P -> P + n <= E -> E + 1 <= 2^64 ->
  bv_unsigned x <> P - 3 -> ~ (P + n <= bv_unsigned x < E) ->
  rss_mem m P E n k x = m x.
Proof using .
  intros m P E n k x N0 P4 PE E64 X1 X2. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR.
  unfold rss_mem. set (r := E - P - n).
  assert (W1 : forall m0 a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> ~ (a <= bv_unsigned x < a + Z.of_nat (length bs)) -> write_to_mem m0 (wa a) bs x = m0 x).
  { intros m0 a bs Ha Hb NX. rewrite write_to_mem_spec by lia.
    destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity. exfalso. apply NX. lia. }
  destruct (Z.leb_spec 5 r); destruct (Z.eqb_spec r 0); try (exfalso; lia).
  - rewrite W1 by (cbn; lia). rewrite W1 by (rewrite ?length_le4; cbn; lia). rewrite W1 by (cbn; lia). apply W1; cbn; lia.
  - rewrite W1 by (cbn; lia). reflexivity.
  - rewrite W1 by (cbn; lia). apply W1; cbn; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wr32_wr8_comm' p q v w st : fst p = fst q -> snd q + 1 = snd p ->
  wr8 q w (wr32 p v st) = wr32 p v (wr8 q w st).
Proof using .
  intros Hf H1. unfold wr32.
  rewrite (wr8_comm q (aadd p 3)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 2)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

Section SETSIZE.
Variables (stx : mstate) (mx : mem) (pp e : aptr) (r : region) (n idx kb : Z).
Let P := r_base r + snd pp.
Let E := r_base r + snd e.
Hypothesis MR : rmrep stx mx.
Hypothesis TK : ticks_ok stx.
Hypothesis Hr : (s_regions stx) !! (fst pp) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis Fe : fst e = fst pp.
Hypothesis P4 : 4 <= snd pp.
Hypothesis N0 : 0 <= n.
Hypothesis PNE : snd pp + n <= snd e.
Hypothesis EHI : snd e + 1 <= round_up_pg (r_len r).
Hypothesis RS : snd e - snd pp - n < 2^32.
Hypothesis IDX : 0 <= idx < 32.
Hypothesis KB : 0 <= kb < 256 /\ Z.land kb 31 = idx.
(* [comment removed for export] *)
Hypothesis NOGRP : forall b gh, (s_groups stx) !! b = Some gh -> fst b = fst pp ->
  snd b + 9 <= snd pp - 3 \/ snd e + 1 <= snd b.

Lemma rmrep_set_size_i :
  rmrep (set_size_i pp e n idx stx) (rss_mem mx P E n kb) /\ ticks_ok (set_size_i pp e n idx stx).
Proof.
  destruct KB as [KB0 KB31].
  unfold set_size_i, rss_mem. subst P E.
  replace (r_base r + snd e - (r_base r + snd pp) - n) with (snd e - snd pp - n) by lia.
  set (rsv := snd e - snd pp - n). assert (RSV : 0 <= rsv < 2^32) by (subst rsv; lia).
  (* [comment removed for export] *)
  set (stF := if negb (rsv =? 0) then _ else _). set (mF := if rsv =? 0 then _ else _).
  assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions stx /\ s_groups stF = s_groups stx).
  { subst stF mF. destruct (Z.eqb_spec rsv 0) as [Z0|NZ]; cbn [negb].
    - auto.
    - pose proof (rmrep_wr8 stx mx (aadd e (- rsv)) 0 r MR TK ltac:(cbn; rewrite Fe; exact Hr) Hk ltac:(cbn; lia)
                   ltac:(intros b gh Hb Hfb; cbn in Hfb |- *; rewrite Fe in Hfb; destruct (NOGRP b gh Hb Hfb); lia) ltac:(lia)) as M1.
      cbn [aadd snd] in M1. replace (r_base r + (snd e + - rsv)) with (r_base r + snd e - rsv) in M1 by lia.
      split; [exact M1|]. split; [apply ticks_ok_wr8; exact TK|]. split; reflexivity. }
  clearbody stF mF. destruct PF as (MF & TF & ERF & EGF).
  (* [comment removed for export] *)
  set (stG := if 5 <=? rsv then _ else _). set (mG := if 5 <=? rsv then _ else _).
  assert (PG : rmrep (fst stG) (fst mG) /\ ticks_ok (fst stG) /\ snd stG = snd mG /\ 0 <= snd mG <= 5
               /\ s_regions (fst stG) = s_regions stx /\ s_groups (fst stG) = s_groups stx).
  { subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd].
    - (* [comment removed for export] *)
      rewrite (wr32_wr8_comm' (aadd e (-4)) (aadd e (-5))) by (cbn; lia || reflexivity).
      pose proof (rmrep_wr8 stF mF (aadd e (-5)) 0 r MF TF ltac:(cbn; rewrite ERF, Fe; exact Hr) Hk ltac:(cbn; lia)
                   ltac:(intros b gh Hb Hfb; cbn in Hfb |- *; rewrite EGF in Hb; rewrite Fe in Hfb; destruct (NOGRP b gh Hb Hfb); lia) ltac:(lia)) as M1.
      pose proof (ticks_ok_wr8 stF (aadd e (-5)) 0 TF) as T1.
      pose proof (rmrep_wr32 (wr8 (aadd e (-5)) 0 stF) _ (aadd e (-4)) rsv r M1 T1 ltac:(cbn; rewrite ERF, Fe; exact Hr) Hk ltac:(cbn; lia) ltac:(cbn; lia)
                   ltac:(intros b gh Hb Hfb; cbn in Hfb, Hb |- *; rewrite EGF in Hb; rewrite Fe in Hfb; destruct (NOGRP b gh Hb Hfb); lia) ltac:(lia)) as [M2 T2].
      cbn [aadd snd] in M2. replace (r_base r + (snd e + -5)) with (r_base r + snd e - 5) in M2 by lia.
      replace (r_base r + (snd e + -4)) with (r_base r + snd e - 4) in M2 by lia.
      split; [exact M2|]. split; [exact T2|]. split; [reflexivity|]. split; [lia|]. split; assumption.
    - split; [exact MF|]. split; [exact TF|]. split; [reflexivity|]. split; [lia|]. split; assumption. }
  clearbody stG mG. destruct stG as [stg r1]. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
  destruct PG as (MG & TG & -> & R2 & ERG & EGG).
  assert (KV : 0 <= idx + Z.shiftl r2 5 < 256) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^5) with 32; lia).
  pose proof (rmrep_wr8 stg mg (aadd pp (-3)) (idx + Z.shiftl r2 5) r MG TG ltac:(cbn; rewrite ERG; exact Hr) Hk ltac:(cbn; lia)
               ltac:(intros b gh Hb Hfb; cbn in Hfb |- *; rewrite EGG in Hb; destruct (NOGRP b gh Hb Hfb); lia) KV) as M3.
  cbn [aadd snd] in M3. replace (r_base r + (snd pp + -3)) with (r_base r + snd pp - 3) in M3 by lia.
  rewrite <- KB31 in M3 at 2. rewrite KB31 in M3 at 1.
  split; [| apply ticks_ok_wr8; exact TG].
  replace (Z.land kb 31 + Z.shiftl r2 5) with (idx + Z.shiftl r2 5) by (rewrite KB31; reflexivity). exact M3.
Qed.
End SETSIZE.


End CeilWrap.
End RF_realloc_K.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Export PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Export MallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RMallocKit_B.
Import RMallocKit_B2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_F.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A.
Import RMalloc_fp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

Lemma rpw_extP p : optr_in P p -> pw st' p = pw st p.
Proof using Hconc. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.

Lemma rget_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.

Lemma rmeta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
  unfold meta_cells. rewrite !rpw_extP by assumption. reflexivity.
Qed.

Lemma rmrep_ctx_extP m : s_areas st' = s_areas st -> rmrep_ctx st m -> rmrep_ctx st' m.
Proof using HP Hconc Hctx.
  intros Har H. destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
  assert (E1 : rctx_head_cells st' = rctx_head_cells st).
  { unfold rctx_head_cells. rewrite (rsec_ext st st' ltac:(rewrite Hctx; reflexivity) Har). rewrite Hctx. rewrite !rpw_extP by assumption. reflexivity. }
  assert (E2 : actives st' = actives st).
  { unfold actives. apply map_ext. intros a. unfold active. rewrite Hctx. apply rpw_extP. apply (H6 (Z.of_nat a)). }
  assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hctx. reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hctx. reflexivity. }
  assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hctx. reflexivity. }
  assert (E6 : ctx_tail_cells st' = ctx_tail_cells st).
  { unfold ctx_tail_cells, brk_word. rewrite Hctx. destruct (c_brk (ctx st)) as [| |rid off]; try reflexivity.
    rewrite (Hconc (rid, off)) by exact H7. reflexivity. }
  unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.

Lemma rarea_rep_extP m a ar : (s_areas st) !! a = Some ar -> rarea_rep st m a ar -> rarea_rep st' m a ar.
Proof using HP Hconc Hmetas.
  intros Ha (A1 & A2 & A3). destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
  destruct (H9 a ar Ha) as [Pa Pn].
  unfold rarea_rep. rewrite (Hconc a Pa). rewrite (rpw_extP _ Pn). split; [exact A1|]. split; [|exact A3].
  intros k Hk. rewrite rget_meta_rec_extP, rmeta_cells_extP. apply A2. exact Hk.
Qed.

Lemma rgroup_rep_extP m b gh : (s_groups st) !! b = Some gh -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof using HP Hconc.
  intros Hb (w8 & R & Hw8). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
  destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (rpw_extP _ Pg). auto.
Qed.
End PEXT.

Lemma rbytes_at_agree m m' A bs : bytes_at psegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at psegs m' A bs.
Proof using .
  intros (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

Lemma rwr_at_agree m m' A n : wr_at psegs m A n -> agree_on m m' A n -> wr_at psegs m' A n.
Proof using .
  intros (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold wview. rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed.

Lemma rrw_cells_agree m m' A cs : rw_cells psegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells psegs m' A cs.
Proof using .
  intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

Lemma ru64arr_agree m m' A ws : u64arr psegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr psegs m' A ws.
Proof using .
  intros [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma ru8arr_agree m m' A bs : u8arr psegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr psegs m' A bs.
Proof using . intros [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

(* [comment removed for export] *)
Lemma rmrep_agree : forall st m m',
  rmrep st m ->
  agree_on m m' RMLOCK 4 -> agree_on m m' RLIBC 0x418 -> agree_on m m' RGOT_SSP 8 -> agree_on m m' RSSP_GUARD 8 ->
  (forall a ar, (s_areas st) !! a = Some ar -> agree_on m m' (conc st a) 4096) ->
  (forall b gh, (s_groups st) !! b = Some gh -> agree_on m m' (conc st b) 9) ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
  rmrep st m'.
Proof using .
  intros st m m' (WF & CX & GL & AR & GR & SH) AGL AGC AGS1 AGS2 AGA AGG AGR.
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    unfold RLIBC, RCTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  - destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply rrw_cells_agree; [exact G1|]. eapply agree_on_sub; [exact AGL| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G2|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G3|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G4|]. eapply agree_on_sub; [exact AGS1| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G5|]. eapply agree_on_sub; [exact AGS2| lia| cbn; lia].
  - intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). pose proof (AGA a ar Ha) as AG.
    split; [|split].
    + eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
    + intros k Hk. eapply rrw_cells_agree; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AG| lia| lia].
    + eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    eapply rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG. split.
    + eapply rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AG| lia| lia].
Qed.

Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).

Hypothesis MR : rmrep st m.
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= alloc_ceiling.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
(* [comment removed for export] *)
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

Lemma rnr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof using k len x. reflexivity. Qed.
Lemma rnr_lookup_new : (s_regions st') !! rid = Some r0.
Proof using k len st x. rewrite rnr_regions. apply lookup_insert_eq. Qed.
Lemma rnr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof using r0. intros. rewrite rnr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rnr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof using k len x.
  intros H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite rnr_lookup_new in H. inversion H. auto.
  - right. rewrite rnr_lookup_old in H by exact NE. auto.
Qed.
Lemma rnr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof using r0. intros. unfold conc, get_region. rewrite rnr_lookup_old by assumption. reflexivity. Qed.
Lemma rnr_conc_new off : conc st' (rid, off) = x + off.
Proof using r0 st. unfold conc, get_region. cbn [fst snd]. rewrite rnr_lookup_new. reflexivity. Qed.
Lemma rnr_shadow q : get_shadow st' q = get_shadow st q.
Proof using k len x. reflexivity. Qed.
Lemma rnr_lr_lo_new : x <= lr_lo r0.
Proof using ACEIL ZF rid. unfold lr_lo, r0. cbn. destruct k; lia. Qed.

(* [comment removed for export] *)
Lemma rnr_old_disjoint q r : (s_regions st) !! q = Some r ->
  x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof.
  intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

Lemma rnr_regions_wf : rregions_wf st'.
Proof using LEN MR PT RF X0 XA XC ZF r0.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (RFimg : ranges_free ref_reserved x L = true).
  { apply ranges_free_intro. intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
  split; [exact RS|]. split; [|split; [|split]].
  - intros q r Hq. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
    + unfold r0. cbn. fold L. repeat split; try lia. exact RFimg.
    + exact (WR q r H).
  - intros q1 r1 q2 r2 H1 H2 NE.
    destruct (rnr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rnr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q2 r2 H2'). pose proof rnr_lr_lo_new. lia.
    + cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q1 r1 H1'). pose proof rnr_lr_lo_new. lia.
    + exact (DJ q1 r1 q2 r2 H1' H2' NE).
  - intros a ar Ha. destruct (WA a ar Ha) as (r & Hr & REST).
    destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
    exists r. rewrite rnr_lookup_old by exact Pa. auto.
  - intros b gh Hb. destruct (WG b gh Hb) as (r & Hr & REST).
    destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
    exists r. rewrite rnr_lookup_old by exact Pb. auto.
Qed.

Lemma rmrep_new_region : rmrep st' m'.
Proof.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (RI : forall b n, In (b, n) ref_reserved -> x + L <= b \/ b + n <= x).
  { intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
  pose proof (RI _ _ ltac:(left; reflexivity)) as RI1. pose proof (RI _ _ ltac:(right; right; left; reflexivity)) as RI2.
  pose proof (RI _ _ ltac:(right; right; right; left; reflexivity)) as RI3.
  pose proof (round_up_pg_ge len) as LG. fold L in LG. unfold alloc_ceiling in XC.
  (* [comment removed for export] *)
  assert (MR1 : rmrep st m').
  { eapply rmrep_agree; [exact MR| | | | | | |].
    - intros a Ha. apply AG; unfold RMLOCK in *; lia.
    - intros a Ha. apply AG; unfold RLIBC in *; lia.
    - intros a Ha. apply AG; unfold RGOT_SSP in *; lia.
    - intros a Ha. apply AG; unfold RSSP_GUARD in *; lia.
    - intros a ar Ha a0 Ha0.
      destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
      pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rnr_old_disjoint _ _ Hra).
      unfold alloc_ceiling in RBC. apply AG; lia.
    - intros b gh Hb a0 Ha0.
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
      pose proof (lr_lo_group rb Kb). pose proof (rnr_old_disjoint _ _ Hrb). unfold alloc_ceiling in RBC. apply AG; lia.
    - intros q r Hq Hk a0 Ha0. destruct (WR q r Hq) as (B0 & _ & _ & BC & _). unfold alloc_ceiling in BC.
      pose proof (lr_lo_group r Hk). pose proof (rnr_old_disjoint _ _ Hq). apply AG; lia. }
  pose proof MR1 as (_ & CX1 & GL1 & AR1 & GR1 & SH1).
  assert (Hconc : forall q, (fun r => r <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rnr_conc; exact Hq).
  split; [exact rnr_regions_wf|]. split; [|split; [exact GL1|split; [|split]]].
  - eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl); [reflexivity| exact CX1].
  - intros a ar Ha. eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|]. exact (AR1 a ar Ha).
  - intros b gh Hb. eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|]. exact (GR1 b gh Hb).
  - intros q r Hq Hk. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
    + (* [comment removed for export] *)
      cbn [r_kind r0] in Hk. unfold rshadow_rep. cbn [r_base r_len r0]. fold L.
      split.
      * split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite (ZF Hk) by lia. discriminate.
      * intros o v Ho Hc. rewrite rnr_shadow in Hc. unfold get_shadow in Hc. fold rid in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc.
        rewrite cell_read_shadow0 in Hc. inversion Hc; subst v. split; [|lia].
        split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia]. cbn [nth_error].
        unfold mrd. rewrite Z.add_0_r. rewrite (ZF Hk) by lia. reflexivity.
    + eapply rshadow_rep_ext; [apply rnr_shadow|]. exact (SH1 q r H Hk).
Qed.

Lemma rticks_ok_new_region : ticks_ok st -> ticks_ok st'.
Proof. intros H. exact H. Qed.

Lemma rptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End NEWREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
  (RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x418 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8
   \/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
  m' (wa a) = m (wa a).

Lemma rdr_regions : s_regions st' = delete rid (s_regions st).
Proof using . reflexivity. Qed.
Lemma rdr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof using .
  intros H. rewrite rdr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
  - rewrite lookup_delete_eq in H. discriminate.
  - rewrite lookup_delete_ne in H by congruence. auto.
Qed.
Lemma rdr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof using . intros. rewrite rdr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rdr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof using . intros. unfold conc, get_region. rewrite rdr_lookup_old by assumption. reflexivity. Qed.
Lemma rdr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof using . intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.

Lemma rmrep_drop_region : rmrep st' m'.
Proof.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (Hconc : forall q, (fun q => q <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rdr_conc; exact Hq).
  destruct (WR rid r Hr) as (B0 & _ & RL0 & BC & RFr). unfold alloc_ceiling in BC.
  assert (OTHER : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
            r_base rq + round_up_pg (r_len rq) <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= lr_lo rq)
    by (intros q rq Hq NE; exact (DJ q rq rid r Hq Hr NE)).
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *)
    split; [exact RS|]. split; [|split; [|split]].
    + intros q rq Hq. destruct (rdr_lookup_inv q rq Hq) as [_ H]. exact (WR q rq H).
    + intros q1 r1 q2 r2 H1 H2 NE. destruct (rdr_lookup_inv _ _ H1) as [_ H1']. destruct (rdr_lookup_inv _ _ H2) as [_ H2']. exact (DJ _ _ _ _ H1' H2' NE).
    + intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & REST).
      destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
      exists ra. rewrite rdr_lookup_old by exact Pa. auto.
    + intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & REST).
      destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
      exists rb. rewrite rdr_lookup_old by exact Pb. auto.
  - (* [comment removed for export] *)
    eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl); [reflexivity|].
    destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
    assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x22000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x22000 \/ 0x55000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
    { destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [exact RFr| lia]]. }
    assert (AGC : agree_on m m' RLIBC 0x418).
    { intros a Ha. unfold RLIBC in Ha. apply AG; [lia| lia| right; left; unfold RLIBC; lia]. }
    unfold RLIBC, RCTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  - destruct GL as (G1 & G2 & G3 & G4 & G5). pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
    assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x22000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x22000 \/ 0x55000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
    { destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [exact RFr| lia]]. }
    unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply rrw_cells_agree; [exact G1|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|left; lia].
    + eapply rrw_cells_agree; [exact G2|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
    + eapply rrw_cells_agree; [exact G3|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
    + eapply rrw_cells_agree; [exact G4|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; left; lia].
    + eapply rrw_cells_agree; [exact G5|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; right; left; lia].
  - intros a ar Ha. cbn [s_areas drop_region set_shadow set_regions] in Ha.
    eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|].
    destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). unfold alloc_ceiling in RBC.
    assert (NE : fst a <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _); exact (proj1 (P9 a ar Ha))).
    pose proof (OTHER _ _ Hra NE). pose proof (lr_lo_ge r). pose proof (lr_lo_ge ra).
    assert (AGA : agree_on m m' (conc st a) 4096).
    { intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists (fst a), ra. split; [exact Hra|]. lia. }
    destruct (AR a ar Ha) as (A1 & A2 & A3). split; [|split].
    + eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
    + intros k0 Hk0. eapply rrw_cells_agree; [apply A2; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AGA| lia| lia].
    + eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
  - intros b gh Hb. cbn [s_groups drop_region set_shadow set_regions] in Hb.
    eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
    assert (NE : fst b <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10); exact (proj1 (P10 b gh Hb))).
    pose proof (OTHER _ _ Hrb NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rb Kb). unfold alloc_ceiling in RBC.
    destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    eapply rrw_cells_agree; [exact R|]. intros a0 Ha0. cbn in Ha0. apply AG; [lia| lia|].
    right; right; right; right. exists (fst b), rb. split; [exact Hrb|]. lia.
  - intros q rq Hq Hk. destruct (rdr_lookup_inv q rq Hq) as [NE H].
    eapply rshadow_rep_ext; [apply rdr_shadow; exact NE|].
    destruct (WR q rq H) as (Bq & _ & _ & BCq & _). unfold alloc_ceiling in BCq.
    pose proof (OTHER _ _ H NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rq Hk).
    assert (AGR : agree_on m m' (r_base rq) (round_up_pg (r_len rq))).
    { intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists q, rq. split; [exact H|]. lia. }
    destruct (SH q rq H Hk) as [HWr HB]. split.
    + eapply rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AGR| lia| lia].
Qed.

Lemma rticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
Proof.
  intros [T1 T2]. split.
  - intros q sh u hl ch Hq Hu Hin. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
    destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
    rewrite lookup_delete_ne in Hq by congruence. exact (T1 q sh u hl ch Hq Hu Hin).
  - intros q sh pg t Hq Hp. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
    destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
    rewrite lookup_delete_ne in Hq by congruence. exact (T2 q sh pg t Hq Hp).
Qed.
End DROPREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rmrep_put_group_new : forall st m b g ai r (w8 : byte),
  rmrep st m -> (s_groups st) !! b = None ->
  (s_regions st) !! (fst b) = Some r -> r_kind r = RKGroup -> 0 <= snd b -> snd b + 16 <= round_up_pg (r_len r) -> snd b mod 16 = 0 ->
  rw_cells psegs m (conc st b) [C8 (pw st (Some g)); C1 w8] -> Z.land (bv_unsigned w8) 31 = Z.land ai 31 ->
  rmrep (put_group b (Some g) ai st) m.
Proof.
  intros st m b g ai r w8 (WF & CX & GL & AR & GR & SH) Hb Hr Hk B0 B16 BA R Hw8.
  pose proof WF as (RS & WR & DJ & WA & WG).
  split; [|split; [exact CX|split; [exact GL|split; [exact AR|split; [|exact SH]]]]].
  - split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
    intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
    destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists r. auto.
    + rewrite lookup_insert_ne in Hb' by congruence. exact (WG b' gh Hb').
  - intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
    destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists w8. cbn [g_meta g_active_idx]. split; [exact R| exact Hw8].
    + rewrite lookup_insert_ne in Hb' by congruence. exact (GR b' gh Hb').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmrep_set_mmap_counter : forall st m v,
  rmrep st m -> 0 <= v < 2^32 ->
  rmrep (upd_ctx (set_mmap_counter v) st) (write_to_mem m (wa (RCTX + 12)) (le4 (wz v))).
Proof.
  intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le4 (wz v)) as L4.
  pose proof (munch_write [(RCTX + 12, RCTX + 16)] m m (RCTX + 12) (le4 (wz v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L4; unfold RCTX; lia) ltac:(rewrite L4; cbn [inside]; lia)) as MU.
  pose proof (wmono_write psegs m m (wa (RCTX + 12)) (le4 (wz v)) (wmono_refl psegs m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_mmap_counter v) st) m _ _ MR MU WM); try reflexivity.
  - intros lo hi [E|[]]; inversion E; subst. unfold RCTX. lia.
  - left.
    pose proof (rw_cells_write psegs m RCTX (rctx_head_cells st) 12 (C4 (wz (c_mmap_counter (ctx st)))) (C4 (wz v)) X1 eq_refl eq_refl I) as W.
    replace (RCTX + Z.of_nat 12) with (RCTX + 12) in W by reflexivity.
    unfold rctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_mmap_counter c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
      c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
    cbn [cell_upd csize Nat.eqb Nat.sub cbytes] in W. exact W.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold actives, active, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_active]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold usages, usage, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_usage]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold unmap_seqs, unmap_seq, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_unmap_seq]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold bouncess, bounces, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_bounces]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_seq c_brk]. reflexivity.
Qed.



End CeilWrap.
