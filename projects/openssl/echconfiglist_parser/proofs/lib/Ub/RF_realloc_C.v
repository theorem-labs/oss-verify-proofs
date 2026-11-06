(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocKit_B3.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import RMallocRep RMallocTree RMallocKit_B RF_get_meta RF_enframe F_memcpy RF_realloc_A RF_realloc_B.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

(* [comment removed for export] *)
Definition rre_ss_mem (m : word -> option byte) (P E n b3 : Z) : word -> option byte :=
  let r := E - P - n in
  let m1 := if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0] in
  let '(m2, r') := if 5 <=? r then (write_to_mem (write_to_mem m1 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m1, r) in
  write_to_mem m2 (wa (P - 3)) [b8 (Z.land b3 31 + Z.shiftl r' 5)].

Definition rre_inplace_post (sp gp tp a0 s7 s8 s9 s10 s11 rav s0v s1v s2v s3v s4v s5v s6v : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (P E n b3 : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None (rre_ss_mem m P E n b3) (seg_rom usegs)
    /\ mem_inv usegs (rre_ss_mem m P E n b3).

Lemma rre_inplace_walk : forall (sp gp tp t1 t2 s0 a0 a2 a4 a5 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 gw rav s0v s1v s2v s3v s4v s5v s6v : word) F fc (m : mem)
    (lo P n sc E rsv b3 : Z),
  bv_unsigned a0 = P -> 16 <= P -> 0 <= n -> P + n <= E -> E - P < 2^20 -> E + 4 <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp + 8 <= 2^64 -> 0 <= b3 < 256 ->
  mem_inv usegs m -> stk usegs m lo (bv_unsigned sp + -64) ->
  rw_cells usegs m (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  wr_at usegs m (P - 3) (E - P + 3) -> bytes_at usegs m (P - 3) [b8 b3] ->
  evt usegs (rre_inplace_post sp gp tp a0 s7 s8 s9 s10 s11 rav s0v s1v s2v s3v s4v s5v s6v F fc m P E n b3)
    (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) t1 t2 s0 gw a0 (Z_to_bv 64 n) a2 (Z_to_bv 64 sc) a4 a5
              (Z_to_bv 64 (E + 4)) a7 (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 131051) t4 t5 t6)
        F (Z_to_bv 64 0x2b8098) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until b3. intros HP P16 N0 PN EP ELO LO SPH B3 MI ST FR W BK3.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (r := E - P - n).
  assert (K31 : 0 <= Z.land b3 31 < 32) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound b3 (2^5)); lia).
  (* [comment removed for export] *)
  step. rewrite ?HP. step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
  replace (E - (n + P)) with r by lia.
  (* [comment removed for export] *)
  assert (TAIL : forall (a2v t0v : word) (r' : Z) (mX : mem),
    r' = (if 5 <=? r then 5 else r) ->
    mX = (let m1 := if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0] in
          if 5 <=? r then write_to_mem (write_to_mem m1 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)) else m1) ->
    mem_inv usegs mX -> stk usegs mX lo (bv_unsigned sp + -64) ->
    rw_cells usegs mX (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
    wr_at usegs mX (P - 3) (E - P + 3) -> bytes_at usegs mX (P - 3) [b8 b3] ->
    evt usegs (rre_inplace_post sp gp tp a0 s7 s8 s9 s10 s11 rav s0v s1v s2v s3v s4v s5v s6v F fc m P E n b3)
      (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0v t1 t2 s0 gw a0 (Z_to_bv 64 r') a2v (Z_to_bv 64 sc) a4 a5
                (Z_to_bv 64 (E + 4)) a7 (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 131051) t4 t5 t6)
          F (Z_to_bv 64 0x2b80d4) fc None mX (seg_rom usegs))).
  { intros a2v t0v r' mX Hr' HmX MIX STX FRX WX BKX.
    assert (R' : 0 <= r' <= 5) by (subst r'; destruct (Z.leb_spec 5 r); lia).
    pose proof (bytes_at_read usegs mX (P - 3) [b8 b3] 0 1 BKX ltac:(lia) ltac:(cbn; lia)) as RK.
    cbv [take drop Z.to_nat] in RK. replace (P - 3 + 0) with (P + -3) in RK by lia. change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK.
    step. clear RK. rewrite ?zxb_b8 by lia.
    step. rewrite ?(wz_unsigned b3) by lia.
    step. rewrite ?(unsigned_lit r'), Z.shiftl_mul_pow2 by lia.
    step. rewrite ?(unsigned_lit (r' * 2 ^ 5)), ?(unsigned_lit (Z.land b3 31)), ?(unsigned_lit b3) by lia.
    rewrite (lor_shl5 r' (Z.land b3 31)) by lia. rewrite <- Z.land_assoc. change (Z.land 31 31) with 31.
    pose proof (wr_at_store_ok usegs mX _ _ 0 1%nat WX ltac:(lia) ltac:(lia)) as SO.
    replace (P - 3 + 0) with (P + -3) in SO by lia. change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in SO.
    step. rewrite (le1_wz (Z.land b3 31 + Z.shiftl r' 5)) by (rewrite Z.shiftl_mul_pow2 by lia; lia). sdk.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step. step.
    apply evt_done. unfold rre_inplace_post.
    lazymatch goal with |- exists t0, _ => idtac end.
    assert (EM : rre_ss_mem m P E n b3 = m0).
    { unfold rre_ss_mem. fold r. subst m0 mX r'. destruct (5 <=? r); reflexivity. }
    rewrite EM. do 14 eexists. split; [reflexivity| assumption]. }
  (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  - (* [comment removed for export] *)
    step. step. eapply (TAIL _ _ 0 m); try eassumption; rewrite KR; reflexivity.
  - (* [comment removed for export] *)
    step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    pose proof (wr_at_store_ok usegs m _ _ (n + 3) 1%nat W ltac:(lia) ltac:(lia)) as SO1.
    replace (P - 3 + (n + 3)) with (E - r + 0) in SO1 by lia. change (wa (E - r + 0)) with (Z_to_bv 64 (E - r + 0)) in SO1.
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small, ?signed_of_Z in K5 by lia.
    + (* [comment removed for export] *)
      step. eapply (TAIL _ _ r); try eassumption.
      * replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      * replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia).
        subst. repeat (f_equal; try (unfold wa; f_equal; lia)).
    + (* [comment removed for export] *)
      lazymatch goal with W' : wr_at usegs ?mc (P - 3) _ |- _ =>
        pose proof (wr_at_store_ok usegs mc _ _ (E - P - 2) 1%nat W' ltac:(lia) ltac:(lia)) as SO2;
        replace (P - 3 + (E - P - 2)) with (E + 4 + -9) in SO2 by lia; change (wa (E + 4 + -9)) with (Z_to_bv 64 (E + 4 + -9)) in SO2 end.
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      lazymatch goal with W' : wr_at usegs ?mc (P - 3) _ |- _ =>
        pose proof (wr_at_store_ok usegs mc _ _ (E - P - 1) 4%nat W' ltac:(lia) ltac:(lia)) as SO3;
        replace (P - 3 + (E - P - 1)) with (E + 4 + -8) in SO3 by lia; change (wa (E + 4 + -8)) with (Z_to_bv 64 (E + 4 + -8)) in SO3 end.
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step. eapply (TAIL _ _ 5); try eassumption.
      * replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      * replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia).
        subst. repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rre_mv1_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (n : Z),
  a1 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
  evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x2b8068) sp gp tp t0 t1 t2 (Z_to_bv 64 n) a0 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2b8058) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until n. intros HA N. subst a1.
  step. step. step. step. apply evt_done. unfold rmalloc_entry. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rre_mv2_walk : forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (n P A' old ER : Z),
  a0 = Z_to_bv 64 A' -> 0 < A' < 2^64 -> bv_unsigned s1 = P -> s2 = Z_to_bv 64 ER -> ER - P = old -> 0 <= old -> P <= ER < 2^64 -> 0 <= n < 2^64 ->
  evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x2b8088) sp gp tp t0 t1 t2 (Z_to_bv 64 A') s1 (Z_to_bv 64 A') s1 (Z_to_bv 64 (Z.min n old)) a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 memcpy_entry) fc None m (seg_rom usegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 n) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2b8068) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until ER. intros HA A0 HP HS2 HO O0 PE N. subst a0 s2.
  pose proof (bv_unsigned_in_range _ s1) as PR. change (bv_modulus 64) with (2^64) in PR. rewrite HP in PR.
  step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia. { exfalso. lia. }
  step. rewrite ?HP, ?unsigned_lit by lia. replace (ER - P) with old by lia. replace (ER + - P) with old by lia.
  assert (LO' : Z.land old 18446744073709551615 = old) by (rewrite <- unsigned_lit_land; apply unsigned_lit; lia).
  step. step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit, ?LO' in K1 by lia.
  - step. step. step. apply evt_done. unfold memcpy_entry. rewrite Z.min_l by lia. reflexivity.
  - step. step. step. step. apply evt_done. unfold memcpy_entry. rewrite Z.min_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rre_mv3_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x2b8090) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 rfree_entry) fc None m (seg_rom usegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2b8088) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros. step. step. apply evt_done. unfold rfree_entry. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rre_mv4_post (sp gp tp s0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v s0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m (seg_rom usegs).

Lemma rre_mv4_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v : word) F fc (m : mem) (lo : Z),
  lo <= bv_unsigned sp - 64 -> bv_unsigned sp + 8 <= 2^64 ->
  mem_inv usegs m -> stk usegs m lo (bv_unsigned sp + -64) ->
  rw_cells usegs m (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  evt usegs (rre_mv4_post sp gp tp s0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v F fc m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2b8090) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until lo. intros LO SPH MI ST FR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. step. step. step. step. step. step. step. step. step. step. step.
  apply evt_done. unfold rre_mv4_post. reflexivity.
Qed.
End HCW.
