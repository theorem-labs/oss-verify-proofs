(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Common Require Import SFModel StrFun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Bytes.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Malloc Require Import F_malloc_free F_malloc_fast MallocBlocks MallocHINV Malloc_iface Malloc_ifaceP MallocSU.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require Import STree Malloc MallocCtrl Monad MI_Inv MI_Geom MI_Read MI_Pres2 MI_WFree MI_Arith.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Malloc Require MallocFacts_inv MallocFacts_inv3 MallocFacts_B.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import RMallocRep RMallocTree RF_get_meta RMalloc_iface RMalloc_ifaceP F_memset.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Malloc Require MallocFresh.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Definition RCALLOC_SYM : Z := 0x23844.
Definition RCALLOC_STACK : Z := 8192 + 64.
Definition rallzerop_entry : Z := 0x251b0.


Definition allzerop_res (last_idx sc maplen : Z) : bool :=
  (48 <=? sc) || (negb (maplen =? 0) && (last_idx =? 0) && (maplen * 4096 - 16 <? 16 * size_class sc)).

Definition rallzerop_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 : word) (res : bool)
   (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 a6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom psegs)
    /\ bv_unsigned a0 = Z.b2z res.

Lemma testbit_3072 n : 0 <= n -> Z.testbit 3072 n = ((n =? 10) || (n =? 11))%bool.
Proof.
  intros Hn. change 3072 with (3 * 2 ^ 10).
  destruct (Z.lt_ge_cases n 10) as [LT|GE].
  - rewrite Z.mul_pow2_bits_low by lia. replace (n =? 10) with false by (symmetry; apply Z.eqb_neq; lia). replace (n =? 11) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - rewrite Z.mul_pow2_bits by lia.
    destruct (Z.eq_dec n 10) as [->|N10]; [reflexivity|]. destruct (Z.eq_dec n 11) as [->|N11]; [reflexivity|].
    replace (n =? 10) with false by (symmetry; apply Z.eqb_neq; lia). replace (n =? 11) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [orb]. apply Z.bits_above_log2; cbn; lia.
Qed.

Lemma land3072_iff x sc : 0 <= x -> 0 <= sc < 64 -> (x / 64) mod 64 = sc -> (Z.land x 3072 = 3072 <-> 48 <= sc).
Proof.
  intros Hx Hsc E.
  assert (Q : exists k, 0 <= k /\ x / 64 = 64 * k + sc) by (exists (x / 64 / 64); Z.div_mod_to_equations; nia).
  destruct Q as (k & Hk & Eq).
  assert (B10 : Z.testbit x 10 = Z.odd (sc / 16)).
  { rewrite Z.testbit_odd, Z.shiftr_div_pow2 by lia. change (2^10) with 1024.
    replace (x / 1024) with (sc / 16 + 2 * (2 * k)) by (Z.div_mod_to_equations; nia). apply Z.odd_add_mul_2. }
  assert (B11 : Z.testbit x 11 = Z.odd (sc / 32)).
  { rewrite Z.testbit_odd, Z.shiftr_div_pow2 by lia. change (2^11) with 2048.
    replace (x / 2048) with (sc / 32 + 2 * k) by (Z.div_mod_to_equations; nia). apply Z.odd_add_mul_2. }
  assert (O16 : Z.odd (sc / 16) = true <-> (sc / 16 = 1 \/ sc / 16 = 3)).
  { rewrite Zodd_mod. split; [intros O; apply Z.eqb_eq in O| intros O; apply Z.eqb_eq]; Z.div_mod_to_equations; nia. }
  assert (O32 : Z.odd (sc / 32) = true <-> sc / 32 = 1).
  { rewrite Zodd_mod. split; [intros O; apply Z.eqb_eq in O| intros O; apply Z.eqb_eq]; Z.div_mod_to_equations; nia. }
  split.
  - intros L. pose proof (f_equal (fun z => Z.testbit z 10) L) as T10. pose proof (f_equal (fun z => Z.testbit z 11) L) as T11. cbn beta in T10, T11.
    rewrite Z.land_spec, testbit_3072, B10 in T10 by lia. rewrite Z.land_spec, testbit_3072, B11 in T11 by lia. cbn [Z.eqb Pos.eqb orb] in T10, T11.
    rewrite andb_true_r in T10, T11. apply O16 in T10. apply O32 in T11. Z.div_mod_to_equations; nia.
  - intros GE. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, testbit_3072 by lia.
    destruct (Z.eqb_spec n 10) as [->|N10]; [rewrite B10; cbn [Z.eqb Pos.eqb orb]; rewrite andb_true_r; apply O16; Z.div_mod_to_equations; nia|].
    destruct (Z.eqb_spec n 11) as [->|N11]; [rewrite B11; cbn [Z.eqb Pos.eqb orb]; rewrite andb_true_r; apply O32; Z.div_mod_to_equations; nia|].
    cbn [orb]. apply andb_false_r.
Qed.

Lemma rallzerop_fin : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
   (mword last_idx sc maplen : Z),
  0 <= mword < 2^64 -> 0 <= maplen < 2^40 -> 0 <= last_idx < 32 -> 0 <= sc < 64 ->
  (Z.land mword 3072 = 3072 <-> 48 <= sc) -> mword - mword mod 4096 = maplen * 4096 ->
  (sc < 48 -> ov_read_bytes psegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  evt psegs (rallzerop_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 (allzerop_res last_idx sc maplen) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz mword) a1 (Z_to_bv 64 last_idx) (Z_to_bv 64 maplen) (Z_to_bv 64 sc) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x252bc) fc None m (seg_rom psegs)).
Proof.
  intros until maplen. intros MW ML LI SC MW5 MW6 RS.
  assert (RS' : sc < 48 -> ov_read_bytes psegs m (Z_to_bv 64 (77738 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
  { intros Hlt. replace (Z_to_bv 64 (77738 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact (RS Hlt). }
  clear RS.
  st1. st1. st1. st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
  -
    assert (SC48 : sc < 48) by (destruct (Z.lt_ge_cases sc 48) as [H|H]; [exact H| exfalso; apply K; apply (proj2 MW5); exact H]).
    specialize (RS' SC48). pose proof (size_class_range sc ltac:(lia)) as SZ.
    st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    +
      st1. st1. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. st1. st1.
      unfold rallzerop_post. finish.
      unfold allzerop_res. rewrite K2. replace (48 <=? sc) with false by (symmetry; apply Z.leb_gt; lia). cbn [Z.eqb negb andb orb Z.b2z].
      rewrite v_sltu_b2z, Z.ltb_irrefl. reflexivity.
    +
      st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
      *
        st1. st1. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. st1. st1.
        unfold rallzerop_post. finish. unfold allzerop_res.
        replace (48 <=? sc) with false by (symmetry; apply Z.leb_gt; lia). replace (last_idx =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite andb_false_r. cbn [Z.eqb negb andb orb Z.b2z]. rewrite v_sltu_b2z, Z.ltb_irrefl. reflexivity.
      *
        st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. st1. st1.
        st1. st1. rewrite land_pgmask by lia. rewrite MW6. st1. st1. st1. st1.
        unfold rallzerop_post. finish. unfold allzerop_res.
        replace (48 <=? sc) with false by (symmetry; apply Z.leb_gt; lia). replace (last_idx =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb orb].
        rewrite v_sltu_b2z. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
        rewrite (unsigned_lit (maplen * 4096 + -16)) by lia. rewrite (unsigned_lit (size_class sc * 16)) by lia.
        replace (maplen * 4096 + -16 <? size_class sc * 16) with (maplen * 4096 - 16 <? 16 * size_class sc)
          by (destruct (Z.ltb_spec (maplen * 4096 - 16) (16 * size_class sc)), (Z.ltb_spec (maplen * 4096 + -16) (size_class sc * 16)); lia || reflexivity).
        destruct (maplen * 4096 - 16 <? 16 * size_class sc); reflexivity.
  -
    st1. st1. unfold rallzerop_post. finish. unfold allzerop_res.
    replace (48 <=? sc) with true by (symmetry; apply Z.leb_le; apply (proj1 MW5); exact K). reflexivity.
Qed.

Lemma rallzerop_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
   (off16 mword last_idx sc maplen : Z),
  0 <= off16 < 65536 -> 0 <= mword < 2^64 -> 0 <= maplen < 2^40 -> 0 <= last_idx < 32 -> 0 <= sc < 64 ->
  Z.shiftr mword 12 = maplen -> Z.land mword 31 = last_idx -> (Z.land mword 3072 = 3072 <-> 48 <= sc) ->
  mword - mword mod 4096 = maplen * 4096 ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (sc < 48 -> ov_read_bytes psegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  evt psegs (rallzerop_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 (allzerop_res last_idx sc maplen) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz mword) (wz off16) (Z_to_bv 64 last_idx) a3 (Z_to_bv 64 sc) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x252a4) fc None m (seg_rom psegs)).
Proof.
  intros until maplen. intros O16 MW ML LI SC MW3 MW1 MW5 MW6 Hml RS.
  st1. rewrite MW3. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - eapply rallzerop_fin; eauto.
  -
    st1. st1. st1. if_cases K2; zify_cond K2.
    + eapply rallzerop_fin; eauto.
    + exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
      rewrite Z.land_ones, wz_unsigned in K2 by lia. rewrite Z.mod_small in K2 by lia. lia.
Qed.

Lemma rallzerop_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret: Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  ov_read_bytes psegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes psegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes psegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes psegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells psegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes psegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes psegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes psegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63) ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  evt psegs (rallzerop_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 (allzerop_res last_idx sc maplen) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rallzerop_entry) fc None m (seg_rom psegs)).
Proof.
  intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  unfold rallzerop_entry.
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  assert (RG' : ov_read_bytes psegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }
  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
  assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }
  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
  st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (MW3 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (MW6 : mword - mword mod 4096 = maplen * 4096).
  { subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. lia. }
  assert (MW5 : Z.land mword 3072 = 3072 <-> 48 <= sc).
  { apply land3072_iff; [lia| lia|]. subst mword.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable) + (sc + 64 * maplen) * 64) by lia.
    rewrite Z.div_add, Z.div_small by lia. rewrite Z.add_0_l, Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW2. st1. st1. if_cases K8; zify_cond K8.
  - specialize (Hsc63 ltac:(rewrite ?unsigned_lit in K8 by lia; lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?unsigned_lit in K9 by lia. lia. }
    eapply rallzerop_tail; eauto.
  - specialize (RS ltac:(rewrite ?unsigned_lit in K8 by lia; lia)) as RS0. specialize (Hsc ltac:(rewrite ?unsigned_lit in K8 by lia; lia)).
    st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. st1.
    assert (RS' : ov_read_bytes psegs m (Z_to_bv 64 (77738 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (77738 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS0. }
    pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. eapply rallzerop_tail; eauto.
Qed.


Lemma rallzerop_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    st (p : aptr) r g gh ar (b3 lo hi : Z),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo + 256 * hi in
  let idx := Z.land b3 31 in
  let base := aadd p (- (UNIT * off16) - UNIT) in
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv psegs m ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
  16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
  cell_read sh (po - 2) = Known lo -> cell_read sh (po - 1) = Known hi ->
  (s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
  m_mem mr = Some base ->
  (s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
  c_init_done (ctx st) = 1 ->
  0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
  (m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
  (48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
  (m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
  evt psegs (rallzerop_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7
               (allzerop_res (m_last_idx mr) (m_sizeclass mr) (m_maplen mr)) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rallzerop_entry) fc None m (seg_rom psegs)).
Proof.
  intros until hi. intros sh po off16 idx base mr MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk HID
         AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml. pose proof sec_range as SECR.
  pose proof MR as (WF & CX & GL & AR & GR & SH).
  destruct WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). atop_facts.
  destruct (rmrep_shadow_read st m (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
  destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
  destruct (rmrep_shadow_read2 st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1)) as (R2 & LO & HI).
  rewrite <- le2_lohi in R2 by lia.
  destruct (rmrep_group_read st m base gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.
  pose proof (rmrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  pose proof (rmrep_area_check_read st m (area_of g) ar MR Har) as RA.
  pose proof (rmrep_ctx_secret_read st m MR) as RC. unfold rsecw in RC. rewrite HID, Z.mul_1_r in RC.
  destruct (WG base gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
  assert (HB : conc st base = (r_base r + po) - 16 * off16 - 16).
  { unfold base. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
  destruct MS as (a & ara & k & Ha & Hkk & Eg).
  destruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
  assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  destruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). atop_facts.
  assert (Hm : (r_base rg + snd a + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
  { unfold AREA_HDR, META_SIZE, NSLOTS in *.
    replace (r_base rg + snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (HA : conc st (area_of g) = conc st g - conc st g mod 4096).
  { rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a) _ rg Hrg).
    replace ((snd a + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [lia|].
    unfold AREA_HDR, META_SIZE, NSLOTS in *.
    replace (snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096) * 4096) by (Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
  eapply (rallzerop_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
            (r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
            (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) SECRET
            (pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try lia.
  - replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
  - replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
  - replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
  - intros Hlt. apply rsize_classes_read; [exact MI | lia].
Qed.


Lemma allzerop_res_single_use mr : 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr ->
  allzerop_res (m_last_idx mr) (m_sizeclass mr) (m_maplen mr) = true <-> single_use mr.
Proof.
  intros SC ML. unfold allzerop_res, single_use, get_stride, UNIT.
  rewrite orb_true_iff, !andb_true_iff, negb_true_iff, Z.leb_le, Z.eqb_neq, Z.eqb_eq, Z.ltb_lt.
  destruct (Z.eqb_spec (m_last_idx mr) 0) as [E|NE]; destruct (Z.eqb_spec (m_maplen mr) 0) as [E2|NE2]; cbn [andb negb]; split; intros H; try lia.
  all: destruct H as [H|H]; try lia.
Qed.


Definition RMALLOC_REPLACED : Z := 0x5de20.

Lemma rw_CB_image_any : forall (bs0 : list byte) A (m : word -> option byte),
  rw_bytes_b psegs A bs0 = true -> 0 <= A -> A + Z.of_nat (length bs0) <= 2^64 ->
  exists bs, rw_cells psegs m A [CB (length bs0) bs].
Proof.
  induction bs0 as [|b0 bs0 IH]; intros A m Hb HA Hl.
  - exists []. split; [split|].
    + cbn. split; [reflexivity| exact I].
    + cbn [cells_bytes cbytes]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    + cbn [cells_size csize length Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [rw_bytes_b] in Hb.
    destruct (seg_rom psegs (wa A)) as [b'|] eqn:Er; [|discriminate].
    destruct (wview psegs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
    apply andb_prop in Hb. destruct Hb as [_ Hb]. cbn [length] in Hl.
    destruct (IH (A + 1)%Z m Hb ltac:(lia) ltac:(lia)) as (bs & [[Hwf (B0 & B1 & HB)] (W0 & W1 & HW)]).
    cbn in Hwf. destruct Hwf as [L _]. cbn [cells_bytes cbytes] in HB, B1. rewrite app_nil_r in HB, B1.
    cbn [cells_size csize] in HW, W1. rewrite Nat.add_0_r in HW, W1.
    set (b := match m (wa A) with Some b => b | None => b' end).
    exists (b :: bs). split; [split|].
    + cbn. split; [cbn; rewrite L; reflexivity| exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [cbn [length]; lia|].
      intros [|i] Hi; cbn [nth_error].
      * rewrite Z.add_0_r. unfold mrd, b. destruct (m (wa A)); [reflexivity| exact Er].
      * replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply HB. cbn in Hi. lia.
    + cbn [cells_size csize]. rewrite Nat.add_0_r. cbn [length]. split; [lia|]. split; [lia|].
      intros i Hi. destruct (Z.eq_dec i 0) as [->|NE].
      * rewrite Z.add_0_r. unfold wview in *. destruct (m (wa A)); [discriminate| exact (fun C => ltac:(rewrite C in Ew; discriminate))].
      * replace (A + i) with (A + 1 + (i - 1)) by lia. apply HW. lia.
Qed.

Lemma rreplaced_chunk : forall m, exists bs, rw_cells psegs m RMALLOC_REPLACED [CB 4 bs].
Proof.
  intros m. destruct (rw_CB_image_any (repeat (Z_to_bv 8 0) 4) RMALLOC_REPLACED m ltac:(vm_compute; reflexivity) ltac:(unfold RMALLOC_REPLACED; lia) ltac:(unfold RMALLOC_REPLACED; cbn [repeat length Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as [bs H].
  exists bs. exact H.
Qed.

Definition rcalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
       | Some p => exists A,
           a0 = Z_to_bv 64 A /\ rblock_range A n
           /\ RHEAP s' ((p, A, n) :: LB) m'
           /\ rw_cells psegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
           /\ (raddr_exposed s n -> A = ptr_addr s' p)
       end.

Definition rcalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 1 -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM psegs (raw_malloc n) s
        (rcalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RCALLOC_SYM) fc None m (seg_rom psegs)).

Lemma impl_post_evt {R : Type} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms :
  impl psegs (at_node psegs) t Q ms -> (forall r ms', Q r ms' -> evt psegs (Q' r) ms') -> impl psegs (at_node psegs) t Q' ms.
Proof.
  revert ms. induction t as [r|n k IH]; intros ms H K; cbn in *.
  - eapply evt_cut; [exact H| exact (K r)].
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [exact (Hk rsp)| exact K].
Qed.
Lemma implM_post_evt {A} (c : @Monad.M PState A) s (Q Q' : A -> PState -> machine_state -> Prop) ms :
  implM psegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt psegs (Q' a s') ms') -> implM psegs c s Q' ms.
Proof.
  intros H K. unfold implM in *. eapply impl_post_evt; [exact H|]. intros [|[a s']] ms' HQ; cbn in *; [apply evt_done; exact HQ| exact (K a s' ms' HQ)].
Qed.


Section TOP.
Hypothesis MALLOCZ : rmalloc_stmt_zz.

Definition calloc_zero_post (ra0 sv0 sv1 sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 : word) F fc (m : mem) (A len lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra0 (bv_add sp (Z_to_bv 64 32)) gp tp t0' t1' t2' sv0 sv1 s0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra0) fc None m' (seg_rom psegs)
      /\ munch [(A, A + len)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ rw_cells psegs m' A [CB (Z.to_nat len) (repeat (Z_to_bv 8 0) (Z.to_nat len))]
      /\ stk psegs m' lo (bv_unsigned sp + 32).

Lemma calloc_tail_memset : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 sv0 sv1 : word) F fc (m : mem) (A len : Z) (junk jf : list byte) (lo : Z),
  bv_unsigned s0 = A -> bv_unsigned s1 = len -> 0 <= len ->
  rw_cells psegs m A [CB (Z.to_nat len) junk] -> mem_inv psegs m ->
  rw_cells psegs m (bv_unsigned sp) [CB 8 jf; C8 sv1; C8 sv0; C8 ra0] ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2^64 -> A + len <= lo ->
  evt psegs (calloc_zero_post ra0 sv0 sv1 sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 F fc m A len lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23934) fc None m (seg_rom psegs)).
Proof.
  intros until lo. intros HA HL L0 BLK MI FR ST LOS SPH ALO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  st1. st1. st1. st1. st1. st1. st1. release_frame FR ST (bv_unsigned sp + 32). st1.
  eapply evt_mono.
  { eapply (memset_spec _ _ gp tp); [| exact MI]. rewrite HA, HL. exact BLK. }
  cbv beta. intros ms' PO. unfold memset_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ZB).
  rewrite HA, HL in MU, ZB. rewrite (unsigned_lit 0), Z.mod_0_l in ZB by lia.
  unfold calloc_zero_post. do 14 eexists. exists m'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ZB|].
  eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. cbn. lia.
Qed.

Lemma rheap_pres_of_munch LB SP W m m' :
  munch W m m' -> wmono psegs m m' -> (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a) -> rheap_pres LB SP m m'.
Proof.
  intros MU WM OUT a Ha Hc. split; [apply MU; rewrite wa_unsigned by lia; exact (OUT a Ha Hc)| apply WM].
Qed.


Lemma le8_of_bytes8 (bs : list byte) : length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (Bytes.le_val_range _ (Bytes.bytes_ok_map bs)) as HR. rewrite length_map, HL, <- Bytes.bytes_le_to_Z_le_val in HR.
  change (256 ^ Z.of_nat 8) with (2^64) in HR. rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma rw_cells_rebytes m A0 cs cs' : rw_cells psegs m A0 cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells psegs m A0 cs'.
Proof. intros [[W B] WR] WF EB ES. split; [split; [exact WF| rewrite EB; exact B]| rewrite ES; exact WR]. Qed.

Lemma repeat_app_same {X} (x : X) a b : repeat x a ++ repeat x b = repeat x (a + b).
Proof. rewrite repeat_app. reflexivity. Qed.

Section MAL0.
Variables (A E : Z).
Hypothesis A16 : A mod 16 = 0.
Hypothesis AE : A + 16 <= E.
Hypothesis E64 : E <= 2^64.
Hypothesis A0 : 0 <= A.

Definition zblk (m : mem) (q : Z) : Prop :=
  exists jq, rw_cells psegs m A [CB (Z.to_nat (q - A)) jq; CB (Z.to_nat (E - q)) (repeat (Z_to_bv 8 0) (Z.to_nat (E - q)))].

Lemma zblk_all m : zblk m A -> rw_cells psegs m A [CB (Z.to_nat (E - A)) (repeat (Z_to_bv 8 0) (Z.to_nat (E - A)))].
Proof.
  intros [jq R]. pose proof R as [[[L _] _] _]. cbn in L. rewrite Z.sub_diag in L. destruct jq; [| discriminate].
  eapply rw_cells_rebytes; [exact R| cbn; split; [apply repeat_length| exact I]| reflexivity| cbn; lia].
Qed.

Lemma zblk_intro m junk : rw_cells psegs m A [CB (Z.to_nat (E - A)) junk] -> zblk m E.
Proof.
  intros R. exists junk. pose proof R as [[[L _] _] _].
  eapply rw_cells_rebytes; [exact R| cbn; rewrite Z.sub_diag; repeat split; auto| cbn; rewrite Z.sub_diag; cbn; rewrite !app_nil_r; reflexivity| cbn; lia].
Qed.

Lemma zblk_read16 m q : zblk m q -> A + 16 <= q -> q <= E ->
  exists w1 w2, ov_read_bytes psegs m (wa (q - 16)) 8 = Some (le8 w1) /\ ov_read_bytes psegs m (wa (q - 8)) 8 = Some (le8 w2)
    /\ (w1 = Z_to_bv 64 0 -> w2 = Z_to_bv 64 0 -> zblk m (q - 16)).
Proof.
  intros [jq R] LO HI. pose proof R as [[WF B] W]. cbn in WF. destruct WF as (L & _ & _).
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  set (k := Z.to_nat (q - A)) in *.
  assert (K16 : (16 <= k)%nat) by (subst k; lia).
  set (b1 := firstn 8 (skipn (k - 16) jq)). set (b2 := firstn 8 (skipn (k - 8) jq)).
  assert (L1 : length b1 = 8%nat) by (unfold b1; rewrite length_firstn, length_skipn; lia).
  assert (L2 : length b2 = 8%nat) by (unfold b2; rewrite length_firstn, length_skipn; lia).
  exists (le_bytes_to_word b1), (le_bytes_to_word b2). rewrite !le8_of_bytes8 by assumption.
  assert (LA : length (jq ++ repeat (Z_to_bv 8 0) (Z.to_nat (E - q))) = (k + Z.to_nat (E - q))%nat) by (rewrite length_app, repeat_length; lia).
  assert (TK : forall j, (j + 8 <= k)%nat -> take 8 (drop j (jq ++ repeat (Z_to_bv 8 0) (Z.to_nat (E - q)))) = take 8 (drop j jq)).
  { intros j Hj. rewrite drop_app_le by lia. rewrite take_app_le by (rewrite length_drop; lia). reflexivity. }
  split. { replace (q - 16) with (A + Z.of_nat (k - 16)) by lia. unfold b1.
           rewrite (bytes_at_ov_read psegs m A (jq ++ repeat (Z_to_bv 8 0) (Z.to_nat (E - q))) (k - 16) 8 B) by (rewrite LA; lia). rewrite TK by lia. reflexivity. }
  split. { replace (q - 8) with (A + Z.of_nat (k - 8)) by lia. unfold b2.
           rewrite (bytes_at_ov_read psegs m A (jq ++ repeat (Z_to_bv 8 0) (Z.to_nat (E - q))) (k - 8) 8 B) by (rewrite LA; lia). rewrite TK by lia. reflexivity. }
  intros H H0. exists (firstn (k - 16) jq).
  assert (Ejq : jq = firstn (k - 16) jq ++ (b1 ++ b2)).
  { unfold b1, b2. rewrite <- (firstn_skipn (k - 16) jq) at 1. f_equal.
    rewrite <- (firstn_skipn 8 (skipn (k - 16) jq)) at 1. f_equal. rewrite skipn_skipn. replace (8 + (k - 16))%nat with (k - 8)%nat by lia.
    symmetry. apply firstn_all2. rewrite skipn_length. lia. }
  assert (Z1 : b1 = repeat (Z_to_bv 8 0) 8) by (rewrite <- (le8_of_bytes8 b1 L1), H; reflexivity).
  assert (Z2 : b2 = repeat (Z_to_bv 8 0) 8) by (rewrite <- (le8_of_bytes8 b2 L2), H0; reflexivity).
  eapply rw_cells_rebytes; [exact R| | |].
  - cbn. split; [rewrite length_firstn; lia|]. split; [apply repeat_length| exact I].
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r.
    enough (EJ : jq ++ repeat (Z_to_bv 8 0) (Z.to_nat (E - q)) = take (k - 16) jq ++ repeat (Z_to_bv 8 0) (Z.to_nat (E - (q - 16)))) by (rewrite EJ; reflexivity).
    rewrite Ejq at 1. rewrite Z1, Z2, !repeat_app_same, <- app_assoc, repeat_app_same. f_equal. f_equal. lia.
  - cbn. lia.
Qed.

Lemma zblk_split m q X c : zblk m q -> A <= X -> 0 <= c -> X + c <= q -> q <= E ->
  exists j1 j2 j3, rw_cells psegs m A [CB (Z.to_nat (X - A)) j1] /\ rw_cells psegs m X [CB (Z.to_nat c) j2]
    /\ rw_cells psegs m (X + c) [CB (Z.to_nat (q - (X + c))) j3; CB (Z.to_nat (E - q)) (repeat (Z_to_bv 8 0) (Z.to_nat (E - q)))].
Proof.
  intros [jq R] H1 H2 H3 H4. pose proof R as [[WF B] W]. cbn in WF. destruct WF as (L & _ & _).
  set (a := Z.to_nat (X - A)). set (cc := Z.to_nat c).
  exists (firstn a jq), (firstn cc (skipn a jq)), (skipn (a + cc) jq).
  assert (R3 : rw_cells psegs m A ([CB a (firstn a jq)] ++ [CB cc (firstn cc (skipn a jq))] ++ [CB (Z.to_nat (q - (X + c))) (skipn (a + cc) jq); CB (Z.to_nat (E - q)) (repeat (Z_to_bv 8 0) (Z.to_nat (E - q)))])).
  { eapply rw_cells_rebytes; [exact R| | |].
    - cbn. rewrite !firstn_length, !skipn_length, repeat_length. repeat split; lia.
    - cbn [cells_bytes cbytes app]. rewrite !app_nil_r.
      assert (EJ : firstn a jq ++ (firstn cc (skipn a jq) ++ skipn (a + cc) jq) = jq).
      { replace (skipn (a + cc) jq) with (skipn cc (skipn a jq)) by (rewrite skipn_skipn; f_equal; lia). rewrite (firstn_skipn cc). apply firstn_skipn. }
      rewrite <- EJ at 4. rewrite <- !app_assoc. reflexivity.
    - cbn. lia. }
  apply Malloc_ifaceP.rw_cells_app in R3 as [R1 R23]. apply Malloc_ifaceP.rw_cells_app in R23 as [R2 R3'].
  cbn [cells_size csize] in R2, R3'.
  replace (A + Z.of_nat (a + 0)) with X in R2, R3' by lia. replace (X + Z.of_nat (cc + 0)) with (X + c) in R3' by lia.
  split; [exact R1|]. split; [exact R2| exact R3'].
Qed.

Lemma zblk_join m X c j1 : A <= X -> 0 <= c -> X + c <= E ->
  rw_cells psegs m A [CB (Z.to_nat (X - A)) j1] ->
  rw_cells psegs m X [CB (Z.to_nat c) (repeat (Z_to_bv 8 0) (Z.to_nat c))] ->
  rw_cells psegs m (X + c) [CB (Z.to_nat (E - (X + c))) (repeat (Z_to_bv 8 0) (Z.to_nat (E - (X + c))))] ->
  zblk m X.
Proof.
  intros H1 H2 H3 R1 R2 R3. exists j1. pose proof R1 as [[WF1 _] _]. cbn in WF1. destruct WF1 as [L1 _].
  assert (R : rw_cells psegs m A ([CB (Z.to_nat (X - A)) j1] ++ [CB (Z.to_nat c) (repeat (Z_to_bv 8 0) (Z.to_nat c))] ++ [CB (Z.to_nat (E - (X + c))) (repeat (Z_to_bv 8 0) (Z.to_nat (E - (X + c))))])).
  { apply Malloc_ifaceP.rw_cells_app. split; [exact R1|]. cbn [cells_size csize]. replace (A + Z.of_nat (Z.to_nat (X - A) + 0)) with X by lia.
    apply Malloc_ifaceP.rw_cells_app. split; [exact R2|]. cbn [cells_size csize]. replace (X + Z.of_nat (Z.to_nat c + 0)) with (X + c) by lia. exact R3. }
  eapply rw_cells_rebytes; [exact R| | |].
  - cbn. split; [exact L1|]. split; [apply repeat_length| exact I].
  - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. f_equal. rewrite repeat_app_same. f_equal. lia.
  - cbn. lia.
Qed.
End MAL0.

Lemma mal0_scan (j : nat) : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (A E P i q : Z),
  A mod 16 = 0 -> A + 16 <= E -> E <= 2^64 -> 0 <= A ->
  i = 16 * (Z.of_nat j + 1) -> i <= 4096 -> q = P - 4096 + i -> A + 4096 <= P -> P <= E ->
  zblk A E m q ->
  evt psegs (fun ms' => exists (q' i' : Z) (x3 x4 : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q') (Z_to_bv 64 (P - 4096)) (Z_to_bv 64 i') x3 x4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (if i' =? 0 then 0x2391c else 0x238dc)) fc None m (seg_rom psegs)
      /\ q' = P - 4096 + i' /\ 0 <= i' <= 4096 /\ zblk A E m q')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 (P - 4096)) (Z_to_bv 64 i) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23900) fc None m (seg_rom psegs)).
Proof.
  induction j as [|j IH]; intros until q; intros A16 AE E64 A0 Hi I4 Hq HP PE ZB.
  all: destruct (zblk_read16 A E AE A0 m q ZB ltac:(lia) ltac:(lia)) as (w1 & w2 & R1 & R2 & DOWN).
  all: replace (wa (q - 16)) with (Z_to_bv 64 (q + -16)) in R1 by (unfold wa; f_equal; lia).
  all: replace (wa (q - 8)) with (Z_to_bv 64 (q + -8)) in R2 by (unfold wa; f_equal; lia).
  all: st1; st1; st1; st1; if_cases K; zify_cond K.
  1,3:
       apply evt_done; eexists q, i, _, w2; split; [replace (i =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity|]; split; [lia|]; split; [lia| exact ZB].
  all: assert (W0 : w1 = Z_to_bv 64 0 /\ w2 = Z_to_bv 64 0)
         by (rewrite bv_or_unsigned in K || idtac; apply Z.lor_eq_0_iff in K; destruct K as [K1 K2];
             split; apply bv_eq; rewrite unsigned_lit by lia; assumption).
  all: destruct W0 as [-> ->]; specialize (DOWN eq_refl eq_refl).
  all: st1; st1; st1; if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  - exfalso. lia.
  - apply evt_done. exists (q - 16), 0, (Z_to_bv 64 0), (Z_to_bv 64 0).
    replace (q + -16) with (q - 16) by lia. replace (i + -16) with 0 by lia. split; [reflexivity|]. split; [lia|]. split; [lia| exact DOWN].
  - replace (q + -16) with (q - 16) by lia. replace (i + -16) with (i - 16) by lia.
    eapply IH; try eassumption; lia.
  - exfalso. lia.
Qed.

Lemma calloc_tail_memset2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 sv0 sv1 : word) F fc (m0 m : mem) (A E l : Z) (jf : list byte) (lo : Z),
  A mod 16 = 0 -> A + 16 <= E -> E <= 2^64 -> 0 <= A ->
  bv_unsigned s0 = A -> s1 = Z_to_bv 64 l -> 0 <= l -> A + l <= E -> E <= lo ->
  zblk A E m (A + l) -> mem_inv psegs m -> munch [(A, E)] m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp) [CB 8 jf; C8 sv1; C8 sv0; C8 ra0] ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2^64 ->
  evt psegs (calloc_zero_post ra0 sv0 sv1 sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 F fc m0 A (E - A) lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23934) fc None m (seg_rom psegs)).
Proof.
  intros until lo. intros A16 AE E64 A0 HA HL L0 LE ELO ZB MI MU0 WM0 FR ST LOS SPH. subst s1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  destruct (zblk_split A E AE A0 m (A + l) A l ZB ltac:(lia) L0 ltac:(lia) LE) as (j1 & j2 & j3 & R1 & R2 & R3).
  st1. st1. st1. st1. st1. st1. st1. release_frame FR ST (bv_unsigned sp + 32). st1.
  eapply evt_mono.
  { eapply (memset_spec _ _ gp tp); [| exact MI]. rewrite HA, unsigned_lit by lia. exact R2. }
  cbv beta. intros ms' PO. unfold memset_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ZB2).
  rewrite HA, !unsigned_lit in MU by lia. rewrite HA, !unsigned_lit, Z.mod_0_l in ZB2 by lia.
  assert (R3' : rw_cells psegs m' (A + l) [CB (Z.to_nat (A + l - (A + l))) j3; CB (Z.to_nat (E - (A + l))) (repeat (Z_to_bv 8 0) (Z.to_nat (E - (A + l))))]).
  { eapply rw_cells_transport; [exact R3| exact MU| exact WM|]. cbn. lia. }
  assert (R3'' : rw_cells psegs m' (A + l) [CB (Z.to_nat (E - (A + l))) (repeat (Z_to_bv 8 0) (Z.to_nat (E - (A + l))))]).
  { pose proof R3' as [[[L3 _] _] _]. cbn in L3. rewrite Z.sub_diag in L3. destruct j3; [| discriminate].
    eapply rw_cells_rebytes; [exact R3'| cbn; split; [apply repeat_length| exact I]| reflexivity| cbn; lia]. }
  assert (R1' : rw_cells psegs m' A [CB (Z.to_nat (A - A)) j1]) by (eapply rw_cells_transport; [exact R1| exact MU| exact WM| cbn; lia]).
  pose proof (zblk_join A E AE A0 m' A l j1 ltac:(lia) L0 LE R1' ZB2 R3'') as ZBA.
  unfold calloc_zero_post. replace (A + (E - A)) with E by lia. do 14 eexists. exists m'. split; [reflexivity|].
  split; [eapply munch_trans; [exact MU0| eapply munch_weaken; [| exact MU]; intros x; cbn; lia]|].
  split; [exact (wmono_trans _ _ _ _ WM0 WM)|]. split; [exact MI'|].
  split; [exact (zblk_all A E AE A0 m' ZBA)|].
  eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. cbn. lia.
Qed.

Lemma mal0_page : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m0 m : mem) (A E P lo : Z) (frame : list cell),
  A mod 16 = 0 -> A + 16 <= E -> E <= 2^64 -> 0 <= A -> E <= lo -> lo <= bv_unsigned sp ->
  bv_unsigned s0 = A -> A + 4096 <= P -> P <= E ->
  zblk A E m P -> mem_inv psegs m -> munch [(A, E)] m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp) frame -> stk psegs m lo (bv_unsigned sp) ->
  evt psegs (fun ms' => exists (xra x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 : word) m',
      ms' = MS (mkR xra sp gp tp x0 x1 x2 s0 (Z_to_bv 64 (P - 4096 - A)) (Z_to_bv 64 (P - 4096)) y1 y2 y3 y4 y5 y6 y7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6)
               F (Z_to_bv 64 (if P - 4096 - A <? 4096 then 0x23934 else 0x238f4)) fc None m' (seg_rom psegs)
      /\ zblk A E m' (P - 4096) /\ mem_inv psegs m' /\ munch [(A, E)] m0 m' /\ wmono psegs m0 m'
      /\ rw_cells psegs m' (bv_unsigned sp) frame /\ stk psegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x238f4) fc None m (seg_rom psegs)).
Proof.
  intros until frame. intros A16 AE E64 A0 ELO LOS HA HP PE ZB MI MU0 WM0 FR ST.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB.
  st1. st1. st1. replace (P + -2048 + -2048) with (P - 4096) by lia.
  eapply evt_cut. { eapply (mal0_scan 255 _ _ gp tp) with (A := A) (E := E) (P := P) (q := P); try eassumption; lia. }
  cbv beta. intros ms1 (q' & i' & x3 & x4 & -> & Hq' & Hi' & ZB').
  assert (MSET : forall (ra1 : word) (y3 y4 : word),
    evt psegs (fun ms' => exists (x0 x1 x2 z1 z2 z3 z4 z5 z6 z7 x5 x6 x7 x8 : word) m',
        ms' = MS (mkR ra1 sp gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 (P - 4096)) z1 z2 z3 z4 z5 z6 z7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x5 x6 x7 x8)
                 F (ret_pc ra1) fc None m' (seg_rom psegs)
        /\ zblk A E m' (P - 4096) /\ mem_inv psegs m' /\ munch [(A, E)] m0 m' /\ wmono psegs m0 m'
        /\ rw_cells psegs m' (bv_unsigned sp) frame /\ stk psegs m' lo (bv_unsigned sp))
      (MS (mkR ra1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P - 4096)) (Z_to_bv 64 0) (Z_to_bv 64 i') y3 y4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 memset_entry) fc None m (seg_rom psegs))).
  { intros ra1 y3 y4.
    destruct (zblk_split A E AE A0 m q' (P - 4096) i' ZB' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (j1 & j2 & j3 & R1 & R2 & R3).
    eapply evt_mono. { unfold memset_entry. eapply (memset_spec _ _ gp tp); [| exact MI]. rewrite !unsigned_lit by lia. exact R2. }
    cbv beta. intros ms' PO. unfold memset_post in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ZB2).
    rewrite !unsigned_lit in MU by lia. rewrite !unsigned_lit, Z.mod_0_l in ZB2 by lia.
    assert (R1' : rw_cells psegs m' A [CB (Z.to_nat (P - 4096 - A)) j1]) by (eapply rw_cells_transport; [exact R1| exact MU| exact WM| cbn; lia]).
    assert (R3' : rw_cells psegs m' (P - 4096 + i') [CB (Z.to_nat (q' - (P - 4096 + i'))) j3; CB (Z.to_nat (E - q')) (repeat (Z_to_bv 8 0) (Z.to_nat (E - q')))])
      by (eapply rw_cells_transport; [exact R3| exact MU| exact WM| cbn; lia]).
    assert (R3'' : rw_cells psegs m' (P - 4096 + i') [CB (Z.to_nat (E - (P - 4096 + i'))) (repeat (Z_to_bv 8 0) (Z.to_nat (E - (P - 4096 + i'))))]).
    { pose proof R3' as [[[L3 _] _] _]. cbn in L3. replace (q' - (P - 4096 + i')) with 0 in L3 by lia. destruct j3; [| discriminate].
      eapply rw_cells_rebytes; [exact R3'| cbn; split; [apply repeat_length| exact I]| cbn; rewrite Hq', !app_nil_r; f_equal; lia| cbn; lia]. }
    do 15 eexists. split; [reflexivity|].
    split; [exact (zblk_join A E AE A0 m' (P - 4096) i' j1 ltac:(lia) ltac:(lia) ltac:(lia) R1' ZB2 R3'')|].
    split; [exact MI'|]. split; [eapply munch_trans; [exact MU0| eapply munch_weaken; [| exact MU]; intros x; cbn; lia]|].
    split; [exact (wmono_trans _ _ _ _ WM0 WM)|].
    split; [eapply rw_cells_transport; [exact FR| exact MU| exact WM| cbn; lia]|].
    eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| cbn; lia]. }
  assert (FIN : forall (x0 x1 x2 z1 z2 z3 z4 z5 z6 z7 x5 x6 x7 x8 : word) m' (pc : Z),
    (pc = 0x23928 \/ pc = 0x238e8) ->
    zblk A E m' (P - 4096) -> mem_inv psegs m' -> munch [(A, E)] m0 m' -> wmono psegs m0 m' -> rw_cells psegs m' (bv_unsigned sp) frame -> stk psegs m' lo (bv_unsigned sp) ->
    evt psegs (fun ms' => exists (xra x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 : word) m',
      ms' = MS (mkR xra sp gp tp x0 x1 x2 s0 (Z_to_bv 64 (P - 4096 - A)) (Z_to_bv 64 (P - 4096)) y1 y2 y3 y4 y5 y6 y7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6)
               F (Z_to_bv 64 (if P - 4096 - A <? 4096 then 0x23934 else 0x238f4)) fc None m' (seg_rom psegs)
      /\ zblk A E m' (P - 4096) /\ mem_inv psegs m' /\ munch [(A, E)] m0 m' /\ wmono psegs m0 m'
      /\ rw_cells psegs m' (bv_unsigned sp) frame /\ stk psegs m' lo (bv_unsigned sp))
      (MS (mkR (Z_to_bv 64 pc) sp gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 (P - 4096)) z1 z2 z3 z4 z5 z6 z7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x5 x6 x7 x8)
          F (Z_to_bv 64 pc) fc None m' (seg_rom psegs))).
  { intros until pc. intros [-> | ->] ZB2 MI2 MU2 WM2 FR2 ST2.
    -
      st1. rewrite HA. st1. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit, ?Z.shiftr_div_pow2 in K by lia; change (2^12) with 4096 in K.
      + apply evt_done. do 16 eexists. replace (P - 4096 + - A) with (P - 4096 - A) by lia. replace (P - 4096 - A <? 4096) with false by (symmetry; apply Z.ltb_ge; lia). split; [reflexivity|]. repeat (split; [assumption|]). assumption.
      + apply evt_done. do 16 eexists. replace (P - 4096 + - A) with (P - 4096 - A) by lia. replace (P - 4096 - A <? 4096) with true by (symmetry; apply Z.ltb_lt; lia). split; [reflexivity|]. repeat (split; [assumption|]). assumption.
    -
      st1. rewrite HA. st1. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit, ?Z.shiftr_div_pow2 in K by lia; change (2^12) with 4096 in K.
      + apply evt_done. do 16 eexists. replace (P - 4096 + - A) with (P - 4096 - A) by lia. replace (P - 4096 - A <? 4096) with true by (symmetry; apply Z.ltb_lt; lia). split; [reflexivity|]. repeat (split; [assumption|]). assumption.
      + apply evt_done. do 16 eexists. replace (P - 4096 + - A) with (P - 4096 - A) by lia. replace (P - 4096 - A <? 4096) with false by (symmetry; apply Z.ltb_ge; lia). split; [reflexivity|]. repeat (split; [assumption|]). assumption. }
  destruct (Z.eqb_spec i' 0) as [I0|INZ].
  -
    rewrite I0. st1. st1. st1. first [replace (P - 4096 + - 0) with (P - 4096) by lia| replace (P - 4096 - 0) with (P - 4096) by lia]. rewrite I0 in MSET.
    eapply evt_cut; [apply MSET|]. cbv beta. intros ms' (x0 & x1 & x2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & x5 & x6 & x7 & x8 & m' & -> & ZB2 & MI2 & MU2 & WM2 & FR2 & ST2).
    replace (ret_pc (Z_to_bv 64 0x23928)) with (Z_to_bv 64 0x23928) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply FIN; [left; reflexivity| assumption..].
  -
    st1. st1. st1. first [replace (q' + - i') with (P - 4096) by lia| replace (q' - i') with (P - 4096) by lia].
    eapply evt_cut; [apply MSET|]. cbv beta. intros ms' (x0 & x1 & x2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & x5 & x6 & x7 & x8 & m' & -> & ZB2 & MI2 & MU2 & WM2 & FR2 & ST2).
    replace (ret_pc (Z_to_bv 64 0x238e8)) with (Z_to_bv 64 0x238e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply FIN; [right; reflexivity| assumption..].
Qed.

Lemma mal0_loop (k : nat) : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m0 m : mem) (A E P lo : Z) (frame : list cell),
  A mod 16 = 0 -> A + 16 <= E -> E <= 2^64 -> 0 <= A -> E <= lo -> lo <= bv_unsigned sp ->
  bv_unsigned s0 = A -> A + 4096 <= P -> P <= E -> P - A < 4096 * (Z.of_nat k + 2) ->
  zblk A E m P -> mem_inv psegs m -> munch [(A, E)] m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp) frame -> stk psegs m lo (bv_unsigned sp) ->
  evt psegs (fun ms' => exists (xra x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 : word) m' P',
      ms' = MS (mkR xra sp gp tp x0 x1 x2 s0 (Z_to_bv 64 (P' - A)) y0 y1 y2 y3 y4 y5 y6 y7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6)
               F (Z_to_bv 64 0x23934) fc None m' (seg_rom psegs)
      /\ A <= P' /\ P' - A < 4096 /\ zblk A E m' P' /\ mem_inv psegs m' /\ munch [(A, E)] m0 m' /\ wmono psegs m0 m'
      /\ rw_cells psegs m' (bv_unsigned sp) frame /\ stk psegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x238f4) fc None m (seg_rom psegs)).
Proof.
  induction k as [|k IH]; intros until frame; intros A16 AE E64 A0 ELO LOS HA HP PE BND ZB MI MU0 WM0 FR ST.
  all: eapply evt_cut; [eapply (mal0_page _ _ gp tp) with (A := A) (E := E) (P := P) (m0 := m0); eassumption|].
  all: cbv beta; intros ms' (xra & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & ZB2 & MI2 & MU2 & WM2 & FR2 & ST2).
  all: destruct (Z.ltb_spec (P - 4096 - A) 4096) as [LT|GE].
  1,3: apply evt_done; do 17 eexists; exists (P - 4096); split; [reflexivity|]; split; [lia|]; split; [lia|]; repeat (split; [assumption|]); assumption.
  - exfalso. lia.
  - eapply IH; try eassumption; lia.
Qed.

Lemma shl52_shr52 x : 0 <= x -> Z.shiftr ((Z.shiftl x 52) mod 2^64) 52 = x mod 4096.
Proof.
  intros Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^64) with (4096 * 2^52).
  rewrite Z.mul_mod_distr_r by lia. apply Z.div_mul. lia.
Qed.

Lemma land_pg x : 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros Hx.
  assert (E : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  assert (D : forall y a b, Z.land y (Z.ldiff a b) = Z.ldiff (Z.land y a) b).
  { intros. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit y n), (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite D, Z.land_ones, Z.mod_small, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12) with 4096. pose proof (Z.div_mod x 4096). lia.
Qed.

Lemma calloc_mal0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 sv0 sv1 : word) F fc (m : mem) (A len : Z) (junk jf : list byte) (lo : Z),
  bv_unsigned s0 = A -> bv_unsigned s1 = len -> 4096 <= len -> A mod 16 = 0 -> A + len <= lo ->
  rw_cells psegs m A [CB (Z.to_nat len) junk] -> mem_inv psegs m ->
  rw_cells psegs m (bv_unsigned sp) [CB 8 jf; C8 sv1; C8 sv0; C8 ra0] ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2^64 ->
  evt psegs (calloc_zero_post ra0 sv0 sv1 sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 F fc m A len lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x238b0) fc None m (seg_rom psegs)).
Proof.
  intros until lo. intros HA HL L4 A16 ALO BLK MI FR ST LOS SPH.
  replace (calloc_zero_post ra0 sv0 sv1 sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 F fc m A len lo)
     with (calloc_zero_post ra0 sv0 sv1 sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 F fc m A (A + len - A) lo) by (f_equal; lia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range 64 s0) as AR. change (bv_modulus 64) with (2^64) in AR. rewrite HA in AR.
  st1. rewrite HA, HL. st1. st1. st1. st1. st1.
  rewrite (unsigned_lit (A + len)) by lia. rewrite (unsigned_lit_wrap (Z.shiftl (A + len) 52)), shl52_shr52, land_pg by lia.
  replace (Z.to_nat len) with (Z.to_nat (A + len - A)) in BLK by lia.
  set (E := A + len) in *. assert (HE : E = A + len) by reflexivity. clearbody E.
  set (i := E mod 4096) in *. assert (Hi : 0 <= i < 4096) by (subst i; apply Z.mod_pos_bound; lia). clearbody i.
  assert (AE : A + 16 <= E) by lia. assert (A0 : 0 <= A) by lia. assert (E64 : E <= 2^64) by lia.
  pose proof (zblk_intro A E AE A0 m junk BLK) as ZB0.
  destruct (zblk_split A E AE A0 m E (E - i) i ZB0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (j1 & j2 & j3 & R1 & R2 & R3).
  replace (E - i + i) with E in R3 by lia.
  st1. eapply evt_cut. { eapply (memset_spec _ _ gp tp); [| exact MI]. rewrite !unsigned_lit by lia. exact R2. }
  cbv beta. intros ms' PO. unfold memset_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ZB2).
  rewrite !unsigned_lit in MU by lia. rewrite !unsigned_lit, Z.mod_0_l in ZB2 by lia.
  replace (ret_pc (Z_to_bv 64 0x238cc)) with (Z_to_bv 64 0x238cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (R1' : rw_cells psegs m' A [CB (Z.to_nat (E - i - A)) j1]) by (eapply rw_cells_transport; [exact R1| exact MU| exact WM| cbn; lia]).
  assert (R3' : rw_cells psegs m' E [CB (Z.to_nat (E - E)) j3; CB (Z.to_nat (E - E)) (repeat (Z_to_bv 8 0) (Z.to_nat (E - E)))])
      by (eapply rw_cells_transport; [exact R3| exact MU| exact WM| cbn; lia]).
  assert (R3'' : rw_cells psegs m' (E - i + i) [CB (Z.to_nat (E - (E - i + i))) (repeat (Z_to_bv 8 0) (Z.to_nat (E - (E - i + i))))]).
  { replace (E - i + i) with E by lia. pose proof R3' as [[[L3 _] _] _]. cbn in L3. rewrite Z.sub_diag in L3. destruct j3; [| discriminate].
    eapply rw_cells_rebytes; [exact R3'| cbn; split; [apply repeat_length| exact I]| reflexivity| cbn; lia]. }
  pose proof (zblk_join A E AE A0 m' (E - i) i j1 ltac:(lia) ltac:(lia) ltac:(lia) R1' ZB2 R3'') as ZBP.
  assert (FR' : rw_cells psegs m' (bv_unsigned sp) [CB 8 jf; C8 sv1; C8 sv0; C8 ra0]) by (eapply rw_cells_transport; [exact FR| exact MU| exact WM| cbn; lia]).
  assert (ST' : stk psegs m' lo (bv_unsigned sp)) by (eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| cbn; lia]).
  assert (MU' : munch [(A, E)] m m') by (eapply munch_weaken; [| exact MU]; intros x; cbn; lia).
  st1. rewrite HA. st1. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit, ?Z.shiftr_div_pow2 in K by lia; change (2^12) with 4096 in K.
  -
    eapply evt_cut. { eapply (mal0_loop (Z.to_nat (E - A)) _ _ gp tp) with (A := A) (E := E) (m0 := m) (lo := lo); first [eassumption| lia]. }
    cbv beta. intros ms2 (xra & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & P' & -> & LP1 & LP2 & ZB3 & MI3 & MU3 & WM3 & FR3 & ST3).
    replace P' with (A + (P' - A)) in ZB3 by lia.
    eapply (calloc_tail_memset2 _ _ gp tp) with (E := E) (l := P' - A) (lo := lo); first [eassumption| reflexivity| lia].
  -
    st1. replace (E - i + - A) with (E - i - A) by lia. replace (E - i) with (A + (E - i - A)) in ZBP by lia.
    eapply (calloc_tail_memset2 _ _ gp tp) with (E := E) (l := E - i - A) (lo := lo); first [eassumption| reflexivity| lia].
Qed.

Lemma allzerop_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m2 : mem) (s' : PState) (p : bptr) (A n : Z) (LB : list block),
  RHEAP s' ((p, A, n) :: LB) m2 -> mem_inv psegs m2 -> rblock_range A n -> a0 = Z_to_bv 64 A ->
  evt psegs (fun ms' => exists (res : bool) a0' a1' a2' a3' a4' a5' a6',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m2 (seg_rom psegs)
      /\ bv_unsigned a0' = Z.b2z res /\ (res = true -> single_use_blk (ps_m s') (fst p)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rallzerop_entry) fc None m2 (seg_rom psegs)).
Proof.
  intros until LB. intros HEAP2 MI2 BR HA0.
  destruct HEAP2 as (st & LB0 & PERM & Hst & RMR & [_ AR]).
  pose proof BR as (Ap & Am16 & N0 & AAT & AIMG).
  assert (Hin : In (p, A, n) LB0) by (eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact PERM| left; reflexivity]).
  destruct (MallocFacts_inv.areach_inv ref_reserved st LB0 AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  destruct (MallocFacts_inv.Forall2_In_l _ _ _ _ CR Hin) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c bo] n']. cbn [bslot boff bsize blk_slot blk_size blk_addr fst snd] in C1, C2, C3. subst n'.
  destruct (MI_WFree.block_facts x0 st L BL LS INV c bo n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hm. pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as Hmem.
  pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as Hli.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0'.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [SG SM]. pose proof (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [B0 B16].
  pose proof (bf_maplen _ _ _ _ _ _ _ _ _ _ _ BF) as ML0.
  destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Em).
  pose proof (MI_WFree.q16 _ _ _ _ _ _ _ _ _ _ _ BF) as (Q1 & Q0 & Q2).
  pose proof (MI_WFree.p_mod16 _ _ _ _ _ _ _ _ _ _ _ BF) as PM16.
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
  rewrite (hosts_gbase _ _ _ IM _ _ (ex_intro _ ai Hm)) in SH.
  destruct SH as (K4 & K3 & K2 & K1 & Q & _ & _ & _).
  set (pf := aadd c (UNIT * bo)) in *. set (q := (snd pf - snd bm - UNIT) / UNIT) in *.
  assert (Epf : snd pf = snd c + UNIT * bo) by reflexivity.
  change ((snd c + UNIT * bo - snd bm - UNIT) / UNIT) with q in K2, K1, Q.
  destruct (ig_region _ _ _ IG _ _ Hm) as (r & Hr & Kr).
  assert (Fc : fst c = fst bm) by (rewrite Ec; reflexivity).
  pose proof RMR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & _). atop_facts.
  assert (Cc : conc st c = r_base r + snd c) by (apply conc_region'; rewrite Fc; exact Hr).
  pose proof (ig_ok _ _ _ IG _ _ _ Hm) as GO.
  pose proof (g_masks _ _ _ _ _ _ GO) as (AV0 & FR0 & AVb & FRb & _).
  destruct (ia_areas _ IA _ _ Ha) as ((ra_ & Hra & _ & _ & Hpg & _) & _ & _ & _).
  destruct (ia_secret _ IA) as [SR [(I0 & _ & AE)|[I1 ES]]]; [rewrite AE in Ha; rewrite lookup_empty in Ha; discriminate|].
  pose proof (MallocFacts_inv3.areach_cinv_proof st LB0 AR) as CI.
  pose proof (MallocFacts_B.ci_gmetas _ _ CI bm m (ex_intro _ ai Hm)) as GOB.
  pose proof (MallocFacts_B.go_avail _ _ _ GOB) as [_ AVh]. pose proof (MallocFacts_B.go_freed _ _ _ GOB) as [_ FRh].
  change (get_meta_rec st m) with (MR st m) in AVh, FRh.
  assert (EBASE : aadd pf (- (UNIT * q) - UNIT) = bm).
  { unfold pf, aadd. cbn [fst snd]. apply injective_projections; cbn [fst snd]; [rewrite Ec; reflexivity|].
    rewrite Ec. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ (ex_intro _ ai Hm)). unfold UNIT in *. lia. }
  eapply evt_mono.
  { eapply (rallzerop_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2
              st pf r m (mkGhdr (Some m) ai) ar (i + 32 * Z.min ((snd c + get_stride (MR st m) - IB) - snd pf - n) 5) (byte_of q 0) (byte_of q 1));
      cbn zeta; rewrite ?(u16_bytes q ltac:(lia)), ?(land31_idx i _) by lia.
    all: try exact RMR. all: try exact MI2. all: try exact Kr. all: unfold MI_Inv.MR in *.
    - unfold pf. cbn [aadd fst]. rewrite Fc. exact Hr.
    - rewrite HA0, unsigned_lit by lia. rewrite C3, Cc. unfold pf, UNIT. cbn [aadd snd]. lia.
    - exact PM16.
    - rewrite Epf, Ec. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ (ex_intro _ ai Hm)).
      assert (SI0 : 0 <= get_stride (get_meta_rec st m) * i) by (apply Z.mul_nonneg_nonneg; clear - SG Hi; unfold UNIT in SG; lia).
      clear - SI0 B0 OFF. unfold UNIT in *. lia.
    - rewrite Epf, Ec. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ (ex_intro _ ai Hm)). clear - Q1 B0. unfold UNIT in *. lia.
    - rewrite Epf, Ec. cbn [snd].
      destruct (MallocFacts_B.go_region _ _ _ GOB) as (r0 & Hr0 & _ & _ & _ & GE & _).
      rewrite <- Fc in Hr. rewrite Fc in Hr0 || idtac. assert (r0 = r) by (rewrite <- Fc in Hr0 || idtac; congruence). subst r0.
      unfold MallocFacts_B.sstart_of in GE. rewrite Hmem in GE. cbn [default from_option id snd] in GE. unfold sstart.
      rewrite (hosts_gbase _ _ _ IM _ _ (ex_intro _ ai Hm)).
      assert (SI : get_stride (get_meta_rec st m) * (i + 1) <= get_stride (get_meta_rec st m) * (m_last_idx (get_meta_rec st m) + 1))
        by (apply Z.mul_le_mono_nonneg_l; clear - SG Hi; unfold UNIT in SG; lia).
      pose proof (Z.div_mod (get_stride (get_meta_rec st m)) 16 ltac:(lia)) as DM.
      clear - GE SI DM SM FIT N0' OFF SG. unfold UNIT, IB in *. nia.
    - eapply known_at; [exact K4| rewrite Epf; unfold UNIT, IB; lia| reflexivity].
    - eapply known_at; [exact K3| rewrite Epf; lia| reflexivity].
    - eapply known_at; [exact K2| rewrite Epf; lia| reflexivity].
    - eapply known_at; [exact K1| rewrite Epf; lia| reflexivity].
    - rewrite EBASE. exact Hm.
    - reflexivity.
    - exists a, ar, ka. split; [exact Ha|]. split; [exact Hka|]. exact Em.
    - rewrite Em. unfold mslot, aadd, AREA_HDR, META_SIZE. cbn [snd]. clear - Hpg Hka. unfold PGSZ, NSLOTS in *. lia.
    - rewrite EBASE. exact Hmem.
    - rewrite Em, (area_of_mslot a ka Hal Hka). exact Ha.
    - exact Hck.
    - exact I1.
    - split; [exact AV0| exact AVh].
    - split; [exact FR0| exact FRh].
    - rewrite ES. exact SR.
    - pose proof (g_li _ _ _ _ _ _ GO) as GLI. unfold MI_Inv.MR in GLI. clear - GLI. lia.
    - pose proof (g_freeable _ _ _ _ _ _ GO) as GF. unfold MI_Inv.MR in GF. rewrite GF. clear. lia.
    - destruct (g_sc _ _ _ _ _ _ GO) as [[S1 S2]|[S1 S2]]; unfold MI_Inv.MR in S1, S2; clear - S1 S2; lia.
    - destruct (g_sc _ _ _ _ _ _ GO) as [[S1 S2]|(S1 & S2 & S3 & S4)]; unfold MI_Inv.MR in S1, S2; [clear - S1 S2 ML0; lia|]. unfold MI_Inv.MR in S3.
      destruct (g_top _ _ _ _ _ _ GO S3) as (_ & rr & Hrr & _ & E4 & _). unfold MI_Inv.MR in E4.
      pose proof (WR _ _ Hrr) as (RB0' & _ & RL0' & RC' & _). pose proof (round_up_pg_ge (r_len rr)) as RG. clear - ML0 E4 RB0' RL0' RC' RG ATOPR. lia.
    - clear - Hi. lia.
    - exact (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF).
    - exact (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF).
    - intros Hsc.
      destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(Hsc' & Hle & Hst2)| E63]; unfold MI_Inv.MR in *; [| clear - Hsc E63; lia].
      pose proof (size_class_bound _ Hsc') as SB.
      assert (A16 : get_stride (get_meta_rec st m) = 16 * size_class (m_sizeclass (get_meta_rec st m)) \/ m_last_idx (get_meta_rec st m) = 0) by (unfold UNIT in Hst2; clear - Hst2; tauto).
      assert (B16' : get_stride (get_meta_rec st m) <= 16 * size_class (m_sizeclass (get_meta_rec st m)) \/ 292 <= size_class (m_sizeclass (get_meta_rec st m))).
      { destruct Hle as [Hle|H28]; [left; unfold UNIT in Hle; exact Hle| right; apply size_class_28; clear - H28 Hsc'; lia]. }
      unfold UNIT, IB in Q1, FIT. exact (guard16_arith _ _ _ _ _ _ _ (proj1 SB) Q1 FIT N0' OFF Hi A16 B16').
    - intros Hsc. destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(Hsc' & _)| E63]; unfold MI_Inv.MR in *; [clear - Hsc Hsc'; lia| exact E63].
    - intros NM. destruct (bf_top _ _ _ _ _ _ _ _ _ _ _ BF NM) as [Bz GE].
      unfold gend, cnt_of, sstart in GE. rewrite (hosts_gbase _ _ _ IM _ _ (ex_intro _ ai Hm)), Bz in GE.
      unfold UNIT, IB in Q1, FIT, GE, SG.
      pose proof (guard17_arith _ _ _ _ _ _ _ SG Q1 FIT N0' (proj1 OFF) Hi GE) as G17. unfold MI_Inv.MR in G17. clear - G17.
      replace (m_maplen (get_meta_rec st m) * 4096 / 16) with (m_maplen (get_meta_rec st m) * 256) in G17 by (rewrite <- (Z.div_mul (m_maplen (get_meta_rec st m) * 256) 16) by lia; f_equal; lia). lia. }
  cbv beta. intros ms' (x0_ & x1 & x2 & x3 & x4 & x5 & x6 & -> & RES). do 8 eexists. split; [reflexivity|]. split; [exact RES|].
  intros RT. exists m, i. rewrite <- Hst. cbn [strip s_slots get_meta_rec s_metas].
  split; [change (s_slots st !! fst p = Some (m, i)); replace (fst p) with c by (rewrite <- C1; reflexivity); exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)|].
  apply (proj1 (allzerop_res_single_use (MR st m) ltac:(destruct (g_sc _ _ _ _ _ _ GO) as [[? ?]|[? ?]]; lia) ML0)). exact RT.
Qed.

Lemma calloc_clear : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 sv0 sv1 : word) F fc (m : mem) (A len : Z) (junk jf : list byte) (lo : Z),
  bv_unsigned s0 = A -> bv_unsigned s1 = len -> 0 <= len < 2^32 -> A mod 16 = 0 -> A + len <= lo ->
  rw_cells psegs m A [CB (Z.to_nat len) junk] -> mem_inv psegs m ->
  rw_cells psegs m (bv_unsigned sp) [CB 8 jf; C8 sv1; C8 sv0; C8 ra0] ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2^64 ->
  evt psegs (calloc_zero_post ra0 sv0 sv1 sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 F fc m A len lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x238a8) fc None m (seg_rom psegs)).
Proof.
  intros until lo. intros HA HL LN A16 ALO BLK MI FR ST LOS SPH.
  st1. st1. if_cases K; zify_cond K; rewrite ?HL, ?Z.shiftr_div_pow2 in K by lia.
  - eapply calloc_tail_memset; eauto. lia.
  - eapply calloc_mal0; eauto. change (2^12) with 4096 in K. lia.
Qed.

Theorem rcalloc_spec_proof : rcalloc_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA0 HA1 N. unfold RCALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. atop_facts.
  assert (ETP : errno_addr tp = RERRNO) by (rewrite TP; unfold errno_addr, RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
  rewrite ETP in ERR.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  eapply (implM_evt psegs _ _ _ (fun ms1 => exists (a2x nw : word) (m1 : mem) (jf : list byte),
            bv_unsigned nw = n /\
            ms1 = MS (mkR (Z_to_bv 64 0x23894) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 s0 nw nw nw a2x a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 RMALLOC_SYM) fc None m1 (seg_rom psegs)
            /\ rw_cells psegs m1 (bv_unsigned sp - 32) [CB 8 jf; C8 s1; C8 s0; C8 ra]
            /\ stk psegs m1 lo (bv_unsigned sp - 32) /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono psegs m m1 /\ mem_inv psegs m1)).
  { unfold RCALLOC_SYM. rewrite HA0, HA1.
    step. carve_frame 32%nat ST. step. step. step.
    assert (FIN : forall (a2y : word) (mq : mem) (jk : list byte),
      mem_inv psegs mq -> munch [(bv_unsigned sp + -32, bv_unsigned sp)] m mq -> wmono psegs m mq -> stk psegs mq lo (bv_unsigned sp + -32) ->
      rw_cells psegs mq (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra] ->
      exists (a2x nw : word) (m1 : mem) (jf : list byte), bv_unsigned nw = n /\
        (MS (mkR (Z_to_bv 64 145556) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 n) * 1))
                 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 n) * 1)) (Z_to_bv 64 n) a2y a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 146108) fc None mq (seg_rom psegs)
        = MS (mkR (Z_to_bv 64 0x23894) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 s0 nw nw nw a2x a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 RMALLOC_SYM) fc None m1 (seg_rom psegs))
        /\ rw_cells psegs m1 (bv_unsigned sp - 32) [CB 8 jf; C8 s1; C8 s0; C8 ra]
        /\ stk psegs m1 lo (bv_unsigned sp - 32) /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono psegs m m1 /\ mem_inv psegs m1).
    { intros a2y mq jk MI0 MU0 WM0 ST0 FR0. exists a2y, (Z_to_bv 64 n), mq, jk.
      rewrite (unsigned_lit n) by lia. rewrite Z.mul_1_r. replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia.
      split; [first [reflexivity| apply unsigned_lit; lia]|]. split; [reflexivity|]. auto. }
    step. if_cases K1.
    - step. step. step. apply evt_done. eapply FIN; eassumption.
    - step. step. if_cases K2; cycle 1.
      { exfalso. zify_cond K2. apply K2. rewrite Z.mul_1_r, Z.shiftr_div_pow2, Z.div_small by lia. reflexivity. }
      step. step. step. apply evt_done. eapply FIN; eassumption. }
  intros ms1 (a2x & nw & m1 & jf & NW & -> & FR1 & ST1 & MU1 & WM1 & MI1).
  assert (ENW : nw = Z_to_bv 64 n) by (rewrite <- NW; symmetry; apply Z_to_bv_bv_unsigned).
  assert (HEAP1 : RHEAP s LB m1).
  { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HEAP| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
  assert (AUX1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AUXB| exact MU1| exact WM1|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
  assert (ERR1 : rw_cells psegs m1 RERRNO [C4 errv]).
  { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. unfold RERRNO. lia. }
  rewrite <- ETP in ERR1.
  eapply implM_post_evt.
  { eapply (MALLOCZ (Z_to_bv 64 0x23894) (Z_to_bv 64 (bv_unsigned sp - 32))) with (lo := lo) (B := B);
      rewrite ?(unsigned_lit (bv_unsigned sp - 32)) by lia;
      first [exact HEAP1| exact AUX1| exact ST1| exact CLO| exact ERR1| exact MI1| exact TP| exact ENW| unfold RMALLOC_STACK; lia| lia]. }
  cbv beta. intros r s' ms' PO.
  destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HP2 & FA2 & SO2 & RR).
  rewrite ?(unsigned_lit (bv_unsigned sp - 32)) in ST2, HP2 by lia.
  replace (ret_pc (Z_to_bv 64 0x23894)) with (Z_to_bv 64 0x23894) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (FR2 : rw_cells psegs m2 (bv_unsigned sp - 32) [CB 8 jf; C8 s1; C8 s0; C8 ra]).
  { eapply rheap_pres_rw_cells; [exact HP2| exact FR1| left; cbn; lia]. }
  assert (HP02 : rheap_pres LB (bv_unsigned sp) m m2).
  { eapply rheap_pres_trans; [| eapply rheap_pres_weaken; [exact HP2| lia| intros bb Hb; exact Hb]].
    apply (rheap_pres_of_munch LB (bv_unsigned sp) _ m m1 MU1 WM1). intros a Ha Hc. cbn. split; [| exact I].
    destruct Hc as [Hc|[[Hc _]|(bb & Hbb & Hin)]]; [lia| lia|].
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ bb HEAP Hbb) as (_ & _ & _ & BR & _). unfold in_block in Hin. lia. }
  destruct r as [p|].
  2:{
    destruct RR as [-> HEAP2].
    step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity].
    step. step. step. step. step. release_frame FR2 ST2 (bv_unsigned sp). step.
    replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned 64 sp) || rewrite Z_to_bv_bv_unsigned.
    unfold rcalloc_post. finish. { exact ERR2. } reflexivity. }
  destruct RR as (A & junk & -> & BR & HEAP2 & BLK & EXPO & FRESHZ & SUZ).
  pose proof BR as (A0 & A16 & N0' & AAT & AIMG).
  step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].
  destruct (rreplaced_chunk m2) as [mrb MRB]. unfold RMALLOC_REPLACED in MRB.
  step. step. step. step.
  assert (FINZ : forall ms', calloc_zero_post ra s0 s1 (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 A) F fc m2 A n lo ms' ->
            rcalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m (Some p) s' ms').
  { intros ms' (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & ZB & ST3).
    unfold rcalloc_post.
    replace (bv_add (Z_to_bv 64 (bv_unsigned sp - 32)) (Z_to_bv 64 32)) with sp
      by (apply bv_eq; rewrite bv_add_unsigned, !unsigned_lit by lia; rewrite bv_wrap_small; [lia| unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia]).
    rewrite unsigned_lit in ST3 by lia. replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) in ST3 by lia.
    do 15 eexists. exists m3, errv2. split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|].
    split. { eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]. cbn. rewrite ETP. unfold RERRNO. lia. }
    split. { eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    split. { eapply rheap_pres_trans; [exact HP02|]. apply (rheap_pres_of_munch LB (bv_unsigned sp) _ m2 m3 MU3 WM3).
             intros a Ha Hc. cbn. split; [| exact I].
             destruct Hc as [Hc|[[Hc NS]|(bb & Hbb & Hin)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in NS; lia|].
             pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (p, A, n) bb HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hbb)) as D.
             cbn [blk_id blk_addr blk_size fst snd] in D. unfold in_block in Hin.
             pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HEAP2) as ND. cbn [map blk_id fst] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
             assert (NE : p <> blk_id bb) by (intros E; apply NI; rewrite E; apply (in_map blk_id) in Hbb; exact Hbb).
             specialize (D NE). lia. }
    split; [exact FA2|]. split; [exact SO2|].
    exists A. split; [reflexivity|]. split; [exact BR|].
    split. { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HEAP2| exact MU3| exact WM3|]. constructor; [| constructor]. right; right.
             exists (p, A, n). split; [left; reflexivity|]. cbn. lia. }
    split; [exact ZB| exact EXPO]. }
  if_cases KR.
  2:{
      eapply evt_mono; [| exact FINZ].
      eapply (calloc_clear _ _ gp tp); try eassumption; rewrite ?unsigned_lit by lia; try lia; try eassumption. }
  step. step.
  eapply evt_cut. { eapply (allzerop_call _ _ gp tp); [exact HEAP2| exact MI2| exact BR| reflexivity]. }
  cbv beta. intros ms' (res & c0 & c1 & c2 & c3 & c4 & c5 & c6 & -> & RES & SUB).
  replace (ret_pc (Z_to_bv 64 0x23974)) with (Z_to_bv 64 0x23974) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  step. if_cases KA; zify_cond KA; rewrite ?RES in KA.
  -
    destruct res; [| exfalso; apply KA; reflexivity].
    assert (ZJ : junk = repeat (Z_to_bv 8 0) (Z.to_nat n)) by exact (SUZ (SUB eq_refl)).
    subst junk.
    step. step. step. step. step. release_frame FR2 ST2 (bv_unsigned sp). step.
    replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned 64 sp) || rewrite Z_to_bv_bv_unsigned.
    unfold rcalloc_post. finish. { exact ERR2. } exists A. split; [reflexivity|]. split; [exact BR|]. split; [exact HEAP2|]. split; [exact BLK| exact EXPO].
  -
    step. eapply evt_mono; [| exact FINZ].
    eapply (calloc_clear _ _ gp tp); try eassumption; rewrite ?unsigned_lit by lia; try lia; try eassumption.
Qed.
End TOP.

End CANSEC1.
