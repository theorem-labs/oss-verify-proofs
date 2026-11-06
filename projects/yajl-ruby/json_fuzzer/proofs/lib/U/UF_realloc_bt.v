(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad RawAlloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UF_enframe UF_realloc_hdr UF_realloc_ip.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition rbt_mem (m : mem) (G NB mw' P E n k : Z) : mem :=
  rset_size_mem (write_to_mem (write_to_mem (write_to_mem m (wa (G + 16)) (le8 (Z_to_bv 64 NB))) (wa (G + 32)) (le8 (wz mw')))
                              (wa E) [b8 0]) P E n k.

Lemma lor_low_pg x nd : 0 <= x -> 0 <= nd -> nd mod 4096 = 0 -> Z.lor (Z.land x 4095) nd = Z.land x 4095 + nd.
Proof.
  intros Hx Hn Hm.
  assert (D : Z.land (Z.land x 4095) nd = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 12).
    - replace nd with ((nd / 4096) * 2 ^ 12) by (change (2^12) with 4096; Z.div_mod_to_equations; lia).
      rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - rewrite Z.land_spec. change 4095 with (Z.ones 12). rewrite Z.testbit_ones_nonneg by lia.
      replace (i <? 12) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- (Z.add_nocarry_lxor _ _ D). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rss_fin_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (rax s0x s1x s2x s3x s4x s5x s6x : word) F fc (m4 m : mem) (P E n k r' lo : Z),
  bv_unsigned a0 = P -> 0 <= r' <= 5 -> 0 <= k < 256 -> 16 <= P -> P <= E -> E + 5 <= 2^64 ->
  mem_inv usegs m4 ->
  rw_cells usegs m4 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m4 lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 64 -> E + 4 <= lo ->
  wr_at usegs m4 (P - 3) (E - P + 3) -> bytes_at usegs m4 (P - 3) [b8 k] ->
  write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)] = rset_size_mem m P E n k ->
  evt usegs (rss_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc lo m P E n k)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0x s1x a0 (Z_to_bv 64 r') a2 a3 a4 a5 a6 a7
             s2x s3x s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19ee0) fc None m4 (seg_rom usegs)).
Proof.
  intros until lo. intros HP R' HK P16 PE E5 MI4 FR4 ST4 SLO ELO WR4 BK4 EQ.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (land31_small k ltac:(lia)) as K31.
  (* [comment removed for export] *)
  read_k. replace (P + -3) with (bv_unsigned a0 + -3) in RK by lia. step. clear RK. rewrite ?zxb_b8 by lia.
  step. rewrite ?(wz_unsigned k) by lia.
  step. rewrite (unsigned_lit r'), Z.shiftl_mul_pow2 by lia.
  step. rewrite (unsigned_lit (r' * 2 ^ 5)), (unsigned_lit (Z.land k 31)) by lia.
  rewrite (lor_shl5 r' (Z.land k 31)) by lia.
  replace (Z.land (Z.land k 31) 31) with (Z.land k 31) by (rewrite <- Z.land_assoc; reflexivity).
  sok 0 1%nat (P + -3). replace (P + -3) with (bv_unsigned a0 + -3) in SO by lia.
  step. change (Z_to_bv 64 (Z.land k 31 + Z.shiftl r' 5)) with (wz (Z.land k 31 + Z.shiftl r' 5)).
  rewrite (le1_wz (Z.land k 31 + Z.shiftl r' 5)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (bv_unsigned a0 + -3) with (P - 3) by lia. sdk.
  (* [comment removed for export] *)
  do 10 step.
  release_frame FR4 ST4 (bv_unsigned sp).
  apply evt_done. unfold rss_post. do 14 eexists.
  lazymatch goal with E1 : ?mx = write_to_mem _ _ _ |- _ => rewrite EQ in E1; subst mx end.
  split; [reflexivity|]. split; [assumption | exact ST4].
Qed.

(* [comment removed for export] *)
Lemma rrealloc_bt_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (rax gw s2x s5x s6x : word) (x1 x2 x3 y1 y2 : word) F fc (m : mem) (G NB ND base mw n k lo : Z),
  let P := NB + 16 + base in
  let E := NB + ND - 4 in
  bv_unsigned gw = G -> mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned sp + -64) (rre_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
  stk usegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 64 -> alloc_ceiling <= lo ->
  rw_cells usegs m G [C8 x1; C8 x2; C8 x3; C4 y1; C4 y2; C8 (Z_to_bv 64 mw)] ->
  wr_at usegs m (P - 3) (E - P + 4) -> bytes_at usegs m (P - 3) [b8 k] ->
  0 <= mw < 2^64 -> 0 <= k < 256 -> 0 <= base -> 0 <= n -> 0 < NB -> 0 < ND -> ND mod 4096 = 0 ->
  P + n <= E -> E - P - n < 4096 -> NB + ND <= alloc_ceiling -> 0 < G -> G + 40 <= alloc_ceiling ->
  (G + 40 <= NB \/ NB + ND <= G) ->
  evt usegs (rss_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 P) F fc lo
               (write_to_mem (write_to_mem (write_to_mem m (wa (G + 16)) (le8 (Z_to_bv 64 NB))) (wa (G + 32)) (le8 (wz (Z.land mw 4095 + ND))))
                             (wa E) [b8 0]) P E n k)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 ND) gw a0 (Z_to_bv 64 n) (Z_to_bv 64 NB) a3 a4 a5 a6 a7
               s2x (Z_to_bv 64 base) (Z_to_bv 64 4095) s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19dd4) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros P E HG MI FR ST SLO CLO CH WR BK MW HK B0 N0 NB0 ND0 NDA PNE EP NC G0 GC GNB.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold alloc_ceiling in *.
  set (r := E - P - n).
  assert (HR : 0 <= r < 4096) by (lia).
  unfold rre_frame in FR.
  (* [comment removed for export] *)
  rewrite <- HG in CH.
  step.
  (* [comment removed for export] *)
  step. step. step.
  (* [comment removed for export] *)
  step. step. step. step. step.
  assert (LND : 0 <= Z.land mw 4095 < 4096).
  { split; [apply Z.land_nonneg; lia|]. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound mw 4096). lia. }
  rewrite (unsigned_lit mw), (unsigned_lit ND) by lia.
  rewrite (unsigned_lit (Z.land mw 4095)) by lia. rewrite (lor_low_pg mw ND) by lia.
  rewrite (unsigned_lit (NB + ND + -4)), (unsigned_lit (n + (NB + base + 16))) by lia.
  rewrite (swrap32_small (NB + ND + -4 - (n + (NB + base + 16)))) by lia.
  replace (NB + ND + -4 - (n + (NB + base + 16))) with r by (lia).
  (* [comment removed for export] *)
  pose proof (rw_cells_wr_at usegs m _ _ 40 CH ltac:(cbn; lia)) as WG. clear CH.
  pose proof (wr_at_store_ok usegs m _ _ 16 8%nat WG ltac:(lia) ltac:(cbn; lia)) as SO1.
  change (wa (bv_unsigned gw + 16)) with (Z_to_bv 64 (bv_unsigned gw + 16)) in SO1.
  step. sdk.
  lazymatch goal with W : wr_at usegs ?mX (bv_unsigned gw) 40 |- _ =>
    pose proof (wr_at_store_ok usegs mX _ _ 32 8%nat W ltac:(lia) ltac:(cbn; lia)) as SO2 end.
  change (wa (bv_unsigned gw + 32)) with (Z_to_bv 64 (bv_unsigned gw + 32)) in SO2.
  step. change (Z_to_bv 64 (Z.land mw 4095 + ND)) with (wz (Z.land mw 4095 + ND)). sdk.
  (* [comment removed for export] *)
  sok (E - P + 3) 1%nat (NB + ND + -4).
  step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
  (* [comment removed for export] *)
  assert (FIN : forall (a2v a4v : word) (m4 mm : mem) (r' : Z),
    0 <= r' <= 5 -> mem_inv usegs m4 ->
    rw_cells usegs m4 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m4 lo (bv_unsigned sp + -64) ->
    wr_at usegs m4 (P - 3) (E - P + 3) -> bytes_at usegs m4 (P - 3) [b8 k] ->
    write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)] = rset_size_mem mm P E n k ->
    evt usegs (rss_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 P) F fc lo mm P E n k)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 ND) gw (Z_to_bv 64 P) (Z_to_bv 64 r') a2v
               (Z_to_bv 64 (NB + ND)) a4v (Z_to_bv 64 (Z.land mw 4095 + ND)) (Z_to_bv 64 r) a7
               s2x (Z_to_bv 64 base) (Z_to_bv 64 4095) s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19ee0) fc None m4 (seg_rom usegs))).
  { intros a2v a4v m4 mm r' R' MI4 FR4 ST4 WR4 BK4 EQ. unfold mkR.
    eapply rss_fin_walk; [| exact R'| exact HK| | | | exact MI4| exact FR4| exact ST4| | | exact WR4| exact BK4| exact EQ].
    all: try lia. all: apply unsigned_lit; lia. }
  (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  - (* [comment removed for export] *)
    step. step.
    replace (Z_to_bv 64 (NB + base + 16) : word) with (Z_to_bv 64 P : word) by (f_equal; lia).
    lazymatch goal with W : wr_at usegs ?mq (P - 3) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      eapply (FIN _ _ mX _ 0); [lia| assumption| assumption| assumption| eapply wr_at_sub; [exact W| lia| lia]| assumption|] end.
    unfold rset_size_mem. fold r. rewrite KR. cbv beta iota zeta.
    repeat match goal with E1 : ?mx = write_to_mem _ _ _ |- _ => rewrite E1; clear E1 end.
    rewrite HG. repeat (f_equal; try (unfold wa; f_equal; lia)).
  - (* [comment removed for export] *)
    step. rewrite (unsigned_lit (NB + ND + -4)), (unsigned_lit (n + (NB + base + 16))) by lia.
    rewrite (swrap32_small (NB + ND + -4 - (n + (NB + base + 16)))) by lia.
    replace (NB + ND + -4 - (n + (NB + base + 16))) with r by (lia).
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (NB + ND + -4 + (0 - r)) with (E - r + 0) by (lia).
    step.
    sok (n + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    + (* [comment removed for export] *)
      step.
      replace (Z_to_bv 64 (NB + base + 16) : word) with (Z_to_bv 64 P : word) by (f_equal; lia).
      lazymatch goal with W : wr_at usegs ?mq (P - 3) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
        eapply (FIN _ _ mX _ r); [lia| assumption| assumption| assumption| eapply wr_at_sub; [exact W| lia| lia]| assumption|] end.
      unfold rset_size_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      repeat match goal with E1 : ?mx = write_to_mem _ _ _ |- _ => rewrite E1; clear E1 end.
      rewrite HG. repeat (f_equal; try (unfold wa; f_equal; lia)).
    + (* [comment removed for export] *)
      sok (E - P - 2) 1%nat (NB + ND + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - P - 1) 4%nat (NB + ND + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      replace (Z_to_bv 64 (NB + base + 16) : word) with (Z_to_bv 64 P : word) by (f_equal; lia).
      lazymatch goal with W : wr_at usegs ?mq (P - 3) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
        eapply (FIN _ _ mX _ 5); [lia| assumption| assumption| assumption| eapply wr_at_sub; [exact W| lia| lia]| assumption|] end.
      unfold rset_size_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      repeat match goal with E1 : ?mx = write_to_mem _ _ _ |- _ => rewrite E1; clear E1 end.
      rewrite HG. repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.
End RC__1.
