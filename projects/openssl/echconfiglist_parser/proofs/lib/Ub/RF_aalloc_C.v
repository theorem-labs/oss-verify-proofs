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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import RMallocRep RMallocTree RMallocKit_B RF_get_meta RF_enframe RF_realloc_C.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require TacX.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

(* [comment removed for export] *)
Definition raa_tail_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v : word) (F : bvmap 5 word) (fc : bv 32)
    (m' : mem) (A : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m'.

(* [comment removed for export] *)
Lemma raa_ss_walk : forall (ra0 sp gp tp t0 t1 t2 s0 a0 a1 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rav s0v s1v : word) F fc (m : mem) (junk : list byte)
    (lo P n E b3 : Z),
  bv_unsigned a0 = P -> 16 <= P -> 0 <= n -> P + n <= E -> E - P < 2^20 -> E + 4 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp + 8 <= 2^64 -> 0 <= b3 < 256 ->
  mem_inv usegs m -> stk usegs m lo (bv_unsigned sp + -32) ->
  rw_cells usegs m (bv_unsigned sp + -32) [CB 8 junk; C8 s1v; C8 s0v; C8 rav] ->
  wr_at usegs m (P - 3) (E - P + 3) -> bytes_at usegs m (P - 3) [b8 b3] ->
  evt usegs (raa_tail_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v F fc (rre_ss_mem m P E n b3) P)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 (Z_to_bv 64 n) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 E) a5 a6 (Z_to_bv 64 0)
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2b7bcc) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until b3. intros HP P16 N0 PN EP ELO LO SPH B3 MI ST FR W BK3.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (r := E - P - n).
  assert (K31 : 0 <= Z.land b3 31 < 32) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound b3 (2^5)); lia).
  assert (AZ : a0 = Z_to_bv 64 P) by (rewrite <- HP; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  step. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbn [negb]. cbv iota.
  step. rewrite ?HP. step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
  replace (E - (n + P)) with r by lia.
  (* [comment removed for export] *)
  assert (TAIL : forall (a2v a4v : word) (r' : Z) (mX : mem),
    r' = (if 5 <=? r then 5 else r) ->
    mX = (let m1 := if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0] in
          if 5 <=? r then write_to_mem (write_to_mem m1 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)) else m1) ->
    mem_inv usegs mX -> stk usegs mX lo (bv_unsigned sp + -32) ->
    rw_cells usegs mX (bv_unsigned sp + -32) [CB 8 junk; C8 s1v; C8 s0v; C8 rav] ->
    wr_at usegs mX (P - 3) (E - P + 3) -> bytes_at usegs mX (P - 3) [b8 b3] ->
    evt usegs (raa_tail_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v F fc (rre_ss_mem m P E n b3) P)
      (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 r') a2v (Z_to_bv 64 (E + 4)) a4v a5 a6 (Z_to_bv 64 0)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b7cb4) fc None mX (seg_rom usegs))).
  { intros a2v a4v r' mX Hr' HmX MIX STX FRX WX BKX.
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
    step. step. step. step. step. step.
    apply evt_done. unfold raa_tail_post.
    lazymatch goal with |- exists t0, _ => idtac end.
    assert (EM : rre_ss_mem m P E n b3 = m0).
    { unfold rre_ss_mem. fold r. subst m0 mX r'. destruct (5 <=? r); reflexivity. }
    rewrite EM, AZ. do 14 eexists. split; [reflexivity| assumption]. }
  (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  - (* [comment removed for export] *)
    rewrite KR. eapply (TAIL _ _ 0 m); try eassumption; rewrite KR; reflexivity.
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
Definition raa_mem (m : word -> option byte) (P' E n S idx q : Z) : word -> option byte :=
  let m1 := write_to_mem (write_to_mem (write_to_mem m (wa (P' - 4)) [b8 0]) (wa (P' - 3)) [b8 idx]) (wa (P' - 2)) (le2 (wz q)) in
  let r := E - P' - n in
  let m2 := if r =? 0 then m1 else write_to_mem m1 (wa (E - r)) [b8 0] in
  let m3 := if 5 <=? r then write_to_mem (write_to_mem m2 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)) else m2 in
  let m4 := write_to_mem m3 (wa (P' - 3)) [b8 (idx + Z.shiftl (Z.min r 5) 5)] in
  write_to_mem (write_to_mem m4 (wa (S - 3)) [b8 224]) (wa (S - 2)) (le2 (wz ((P' - S) / 16))).

(* [comment removed for export] *)
Lemma raa_aa_walk : forall (ra0 sp gp tp t0 t1 t2 s0 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rav s0v s1v : word) F fc (m : mem) (junk : list byte)
    (lo P P' n E S B idx stride adj : Z),
  bv_unsigned a0 = P -> 0 < adj -> P' = P + adj -> S <= P -> 16 <= S -> 1 <= n -> P' + n <= E -> E - S < 2^20 -> S = B + 16 + stride * idx ->
  0 <= P' - B - 16 < 2^20 -> (P' - B - 16) mod 16 = 0 -> (P' - S) mod 16 = 0 -> 0 <= B -> 0 <= stride < 2^20 -> 0 <= idx < 32 ->
  E + 4 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp + 8 <= 2^64 ->
  mem_inv usegs m -> stk usegs m lo (bv_unsigned sp + -32) ->
  rw_cells usegs m (bv_unsigned sp + -32) [CB 8 junk; C8 s1v; C8 s0v; C8 rav] ->
  wr_at usegs m (S - 3) (E - S + 3) ->
  evt usegs (raa_tail_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v F fc (raa_mem m P' E n S idx ((P' - B - 16) / 16)) P')
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 idx) (Z_to_bv 64 n) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 E)
              (Z_to_bv 64 (B + 16)) (Z_to_bv 64 stride) (Z_to_bv 64 adj) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2b7bcc) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until adj. intros HP ADJ HP' SP S16 N1 PN ES HS QR QM DM B0 STR IDX ELO LO SPH MI ST FR W.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (r := E - P' - n). set (q := (P' - B - 16) / 16).
  assert (QQ : 0 <= q < 2 ^ 16) by (subst q; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia. { exfalso. lia. }
  (* [comment removed for export] *)
  assert (SI : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  step. rewrite (unsigned_lit stride), (unsigned_lit idx) by lia.
  step. rewrite ?HP. replace (P + adj) with P' by lia. step. rewrite (unsigned_lit (B + 16)) by lia. replace (P' + - (B + 16)) with (P' - B - 16) by lia.
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit (P' - B - 16)), Z.shiftr_div_pow2, (Z.div_small _ (2 ^ 20)) by lia.
  step. rewrite ?(unsigned_lit 0), ?Z.shiftl_0_l by lia.
  step. rewrite ?(unsigned_lit (P' - B - 16)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. fold q.
  step. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (B + 16)), ?(unsigned_lit (stride * idx)) by lia. rewrite <- HS.
  step. step. rewrite (unsigned_lit E), (unsigned_lit (n + P')) by lia. rewrite (swrap32_small (E - (n + P'))) by lia.
  replace (E - (n + P')) with r by lia.
  assert (PS16 : S + 16 <= P') by (Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  sok (P' - S - 1) 1%nat (P' + -4). step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
  sok (P' - S) 1%nat (P' + -3). step. rewrite (le1_wz idx) by lia. sdk.
  lazymatch goal with E2 : ?mc = write_to_mem ?mp (wa ?a) [b8 idx] |- _ =>
    pose proof (bytes_at_write_same usegs mp a [b8 idx] ltac:(lia) ltac:(cbn; lia)) as BK; rewrite <- E2 in BK;
    replace a with (P' - 3) in BK by lia end.
  sok (P' - S + 1) 2%nat (P' + -2). step. change (le2 (Z_to_bv 64 q)) with (le2 (wz q)). sdk.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => set (mH := mc) in * end.
  (* [comment removed for export] *)
  assert (TAIL : forall (a2v a4v : word) (r' : Z) (mX : mem),
    r' = (if 5 <=? r then 5 else r) ->
    mX = (let mA := if r =? 0 then mH else write_to_mem mH (wa (E - r)) [b8 0] in
          if 5 <=? r then write_to_mem (write_to_mem mA (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)) else mA) ->
    mem_inv usegs mX -> stk usegs mX lo (bv_unsigned sp + -32) ->
    rw_cells usegs mX (bv_unsigned sp + -32) [CB 8 junk; C8 s1v; C8 s0v; C8 rav] ->
    wr_at usegs mX (S - 3) (E - S + 3) -> bytes_at usegs mX (P' - 3) [b8 idx] ->
    evt usegs (raa_tail_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v F fc (raa_mem m P' E n S idx q) P')
      (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp (Z_to_bv 64 0) t1 t2 s0 (Z_to_bv 64 n) (Z_to_bv 64 P') (Z_to_bv 64 r') a2v (Z_to_bv 64 (E + 4)) a4v
                (Z_to_bv 64 S) (Z_to_bv 64 r) (Z_to_bv 64 q) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b7c74) fc None mX (seg_rom usegs))).
  { intros a2v a4v r' mX Hr' HmX MIX STX FRX WX BKX.
    assert (R' : 0 <= r' <= 5) by (subst r'; destruct (Z.leb_spec 5 r); lia).
    pose proof (bytes_at_read usegs mX (P' - 3) [b8 idx] 0 1 BKX ltac:(lia) ltac:(cbn; lia)) as RK.
    cbv [take drop Z.to_nat] in RK. replace (P' - 3 + 0) with (P' + -3) in RK by lia. change (wa (P' + -3)) with (Z_to_bv 64 (P' + -3)) in RK.
    (* [comment removed for export] *)
    step. clear RK. rewrite ?zxb_b8 by lia.
    step. rewrite ?(unsigned_lit r'), Z.shiftl_mul_pow2 by lia.
    step. rewrite ?(wz_unsigned idx) by lia.
    assert (I31 : Z.land idx 31 = idx) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
    rewrite ?I31. step. rewrite ?(unsigned_lit (r' * 2 ^ 5)), ?I31, ?(unsigned_lit idx) by lia.
    rewrite (lor_shl5 r' idx) by lia. rewrite I31.
    step. rewrite (unsigned_lit P'), (unsigned_lit S), (swrap32_small (P' - S)) by lia.
    (* [comment removed for export] *)
    pose proof (wr_at_store_ok usegs mX _ _ (P' - S) 1%nat WX ltac:(lia) ltac:(lia)) as SO4.
    replace (S - 3 + (P' - S)) with (P' + -3) in SO4 by lia. change (wa (P' + -3)) with (Z_to_bv 64 (P' + -3)) in SO4.
    step. rewrite (le1_wz (idx + Z.shiftl r' 5)) by (rewrite Z.shiftl_mul_pow2 by lia; lia). sdk.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit (P' - S)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
    (* [comment removed for export] *)
    lazymatch goal with W' : wr_at usegs ?mc (S - 3) _ |- _ =>
      pose proof (wr_at_store_ok usegs mc _ _ 0 1%nat W' ltac:(lia) ltac:(lia)) as SO5;
      replace (S - 3 + 0) with (S + -3) in SO5 by lia; change (wa (S + -3)) with (Z_to_bv 64 (S + -3)) in SO5 end.
    step. rewrite (TacX.le1_mod (-32)). change ((-32) mod 256) with 224. sdk.
    (* [comment removed for export] *)
    lazymatch goal with W' : wr_at usegs ?mc (S - 3) _ |- _ =>
      pose proof (wr_at_store_ok usegs mc _ _ 1 2%nat W' ltac:(lia) ltac:(lia)) as SO6;
      replace (S - 3 + 1) with (S + -2) in SO6 by lia; change (wa (S + -2)) with (Z_to_bv 64 (S + -2)) in SO6 end.
    step. change (le2 (Z_to_bv 64 ((P' - S) / 16))) with (le2 (wz ((P' - S) / 16))). sdk.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => assert (EM : raa_mem m P' E n S idx q = mf) end.
    { unfold raa_mem. fold r. subst r' mX mH. repeat match goal with H : ?mv = write_to_mem _ _ _ |- _ => subst mv end.
      destruct (Z.leb_spec 5 r); [rewrite Z.min_r by lia| rewrite Z.min_l by lia]; reflexivity. }
    apply evt_done. unfold raa_tail_post. rewrite EM. do 14 eexists. split; [reflexivity| assumption]. }
  (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  - (* [comment removed for export] *)
    step. step. eapply (TAIL _ _ 0 mH); try eassumption; rewrite KR; reflexivity.
  - (* [comment removed for export] *)
    step. rewrite (unsigned_lit E), (unsigned_lit (n + P')) by lia. rewrite (swrap32_small (E - (n + P'))) by lia.
    replace (E - (n + P')) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    pose proof (wr_at_store_ok usegs mH _ _ (P' - S + n + 3) 1%nat W ltac:(lia) ltac:(lia)) as SO1.
    replace (S - 3 + (P' - S + n + 3)) with (E - r + 0) in SO1 by lia. change (wa (E - r + 0)) with (Z_to_bv 64 (E - r + 0)) in SO1.
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small, ?signed_of_Z in K5 by lia.
    + (* [comment removed for export] *)
      step. eapply (TAIL _ _ r); try eassumption.
      * replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      * replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia).
        subst. repeat (f_equal; try (unfold wa; f_equal; lia)).
    + (* [comment removed for export] *)
      lazymatch goal with W' : wr_at usegs ?mc (S - 3) _ |- _ =>
        pose proof (wr_at_store_ok usegs mc _ _ (E - S - 2) 1%nat W' ltac:(lia) ltac:(lia)) as SO2;
        replace (S - 3 + (E - S - 2)) with (E + 4 + -9) in SO2 by lia; change (wa (E + 4 + -9)) with (Z_to_bv 64 (E + 4 + -9)) in SO2 end.
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      lazymatch goal with W' : wr_at usegs ?mc (S - 3) _ |- _ =>
        pose proof (wr_at_store_ok usegs mc _ _ (E - S - 1) 4%nat W' ltac:(lia) ltac:(lia)) as SO3;
        replace (S - 3 + (E - S - 1)) with (E + 4 + -8) in SO3 by lia; change (wa (E + 4 + -8)) with (Z_to_bv 64 (E + 4 + -8)) in SO3 end.
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step. eapply (TAIL _ _ 5); try eassumption.
      * replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      * replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia).
        subst. repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.
End HCW.

(* [comment removed for export] *)
Definition aadj (P al : Z) : Z := (- P) mod al.

Lemma aadj_facts P al k : al = 2 ^ k -> 4 <= k <= 6 -> P mod 16 = 0 ->
  0 <= aadj P al < al /\ aadj P al mod 16 = 0 /\ (P + aadj P al) mod al = 0 /\ 16 <= al <= 64 /\ al mod 16 = 0.
Proof.
  intros Hal Hk P16. unfold aadj.
  assert (ALR : 16 <= al <= 64).
  { rewrite Hal. split; [change 16 with (2^4); apply Z.pow_le_mono_r; lia| change 64 with (2^6); apply Z.pow_le_mono_r; lia]. }
  assert (D16 : (16 | al)). { exists (2 ^ (k - 4)). rewrite Hal. change 16 with (2^4). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  split; [apply Z.mod_pos_bound; lia|]. split.
  - rewrite (Z.mod_mod_divide _ _ _ D16). replace (- P) with ((- (P / 16)) * 16) by (Z.div_mod_to_equations; lia). apply Z_mod_mult.
  - split; [rewrite Z.add_mod_idemp_r by lia; replace (P + - P) with 0 by lia; reflexivity|]. split; [exact ALR|].
    destruct D16 as [q Hq]. rewrite Hq. apply Z_mod_mult.
Qed.
