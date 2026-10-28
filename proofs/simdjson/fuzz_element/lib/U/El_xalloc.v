(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import STree Malloc MallocCtrl Prog KInv MI_Inv MI_Arith MI_Read MI_Pres2 MI_WFree MI_Geom.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks MallocFacts_B MallocFacts_inv F_malloc_free F_malloc_fast F_malloc_enframe.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RF_get_meta RF_enframe.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require InitMem.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Ltac st1 := step; try nrm.
Ltac probe := match goal with |- ?g => idtac "PROBE"; idtac g end; fail "PROBE".

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition aa1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (P B idx n off16 mword last_idx sc : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz idx) (wz n) (wz off16) (wz B) (wz mword) (wz last_idx) (wz (idx + 1))
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xc21dc) fc None m (seg_rom usegs)
    /\ t0 = wz RSIZE_CLASSES /\ t1 = wz (2 * sc).

Lemma aa1_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P G B A n : Z) (b3 off16 avail freed last_idx freeable sc maplen secret : Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  a0 = wz P -> s1 = wz n -> 0 <= n < 2^32 ->
  0 < P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  ov_read_bytes usegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes usegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes usegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes usegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells usegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes usegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes usegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes usegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63) ->
  mem_inv usegs m ->
  evt usegs (aa1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m P B idx n off16 mword last_idx sc)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xc20e0) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until next. intros idx mword HA0 HS1 HN P0 AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 MI.
  subst a0 s1.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  unfold wz.

  st1. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }

  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite ?unsigned_lit, zb_land_mask in K by lia. lia. }

  st1. st1. st1. st1. fold idx. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }

  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. st1.
  assert (RG' : ov_read_bytes usegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).

  st1. st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia. lia. }

  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }

  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite ?unsigned_lit by lia. rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
  assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }

  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }

  st1. st1. rewrite GW. unfold wz. rewrite ?unsigned_lit by lia. rewrite land_pgmask by lia. rewrite <- HA. st1. st1. unfold RCTX in RC. st1.
  st1. if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K7 by lia. lia. }

  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  st1. st1. st1. st1. rewrite MW2. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1.
  if_cases K8; zify_cond K8.
  -   specialize (Hsc63 ltac:(rewrite ?unsigned_lit in K8 by lia; lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?unsigned_lit in K9 by lia. lia. }
    apply evt_done. unfold aa1_post. do 7 eexists. split; [reflexivity| split; [reflexivity| unfold wz; f_equal; lia]].
  - specialize (RS ltac:(rewrite ?unsigned_lit in K8 by lia; lia)). specialize (Hsc ltac:(rewrite ?unsigned_lit in K8 by lia; lia)).
    st1.
    assert (RS' : ov_read_bytes usegs m (Z_to_bv 64 (139456 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (139456 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    clear RS. pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. apply evt_done. unfold aa1_post. do 7 eexists. split; [reflexivity| split; [reflexivity| unfold wz; f_equal; lia]].
Qed.

Definition aa2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (P B idx n mword stride : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t2 a3 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz idx) (wz n) a3 (wz B) (wz mword) (wz stride) (wz (idx + 1))
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xc2208) fc None m (seg_rom usegs)
    /\ t2 = Z_to_bv 64 (0 - P).

Lemma aa2_walk : forall ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P B n idx off16 last_idx freeable sc maplen stride : Z),
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  0 < P -> P + 16 <= 2^64 ->
  (sc < 48 -> ov_read_bytes usegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= off16 < 65536 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 -> 0 <= idx < 32 ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  (maplen <> 0 -> last_idx = 0 -> stride = maplen * 4096 - 16) ->
  (maplen = 0 \/ last_idx <> 0 -> stride = 16 * size_class sc) ->
  mem_inv usegs m ->
  evt usegs (aa2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz (2 * sc)) F fc m P B idx n mword stride)
      (MS (mkR ra sp gp tp (wz RSIZE_CLASSES) (wz (2 * sc)) t2 s0 s1 (wz P) (wz idx) (wz n) (wz off16) (wz B) (wz mword) (wz last_idx) (wz (idx + 1))
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xc21dc) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until stride. intros mword P0 PHI RS O16 LI FB SC ML IDX Hml SC48 HSTR1 HSTR2 MI.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW4 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  unfold wz, RSIZE_CLASSES in *.

  st1. rewrite MW4. st1. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  -
    specialize (RS ltac:(lia)). specialize (HSTR2 ltac:(lia)). pose proof (size_class_range sc ltac:(lia)) as SZ.
    st1.
    assert (RS' : ov_read_bytes usegs m (Z_to_bv 64 (139456 + 2 * sc)) 2 = Some (le2 (Z_to_bv 64 (size_class sc)))) by exact RS.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (size_class sc * 16) with stride by lia.
    apply evt_done. unfold aa2_post. do 7 eexists. split; [reflexivity| reflexivity].
  -
    st1. st1. st1. if_cases K2; zify_cond K2.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
        rewrite Z.land_ones in K2 by lia. rewrite Z.mod_small in K2 by lia. lia. }
    st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    +
      specialize (HSTR1 ltac:(lia) ltac:(lia)).
      st1. st1. rewrite ?unsigned_lit by lia. rewrite land_pgmask by lia.
      assert (MM12 : mword - mword mod 4096 = maplen * 4096).
      { subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
        rewrite Z.mod_add, Z.mod_small by lia. lia. }
      rewrite MM12. st1. st1.
      replace (maplen * 4096 + -16) with stride by lia.
      apply evt_done. unfold aa2_post. do 7 eexists. split; [reflexivity| reflexivity].
    +
      specialize (RS ltac:(lia)). specialize (HSTR2 ltac:(lia)). pose proof (size_class_range sc ltac:(lia)) as SZ.
      st1.
      assert (RS' : ov_read_bytes usegs m (Z_to_bv 64 (139456 + 2 * sc)) 2 = Some (le2 (Z_to_bv 64 (size_class sc)))) by exact RS.
      st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
      replace (size_class sc * 16) with stride by lia.
      apply evt_done. unfold aa2_post. do 7 eexists. split; [reflexivity| reflexivity].
Qed.

Lemma write_same : forall (m : word -> option byte) a bs,
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall i, (i < length bs)%nat -> m (wa (a + Z.of_nat i)) = nth_error bs i) ->
  forall x, write_to_mem m (wa a) bs x = m x.
Proof.
  intros m a bs Ha Hb H x. rewrite write_to_mem_spec by lia.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
  rewrite <- (H (Z.to_nat (bv_unsigned x - a))) by lia. f_equal. unfold wa. apply bv_eq. rewrite unsigned_lit by lia. lia.
Qed.

Lemma land31_shl5 : forall i r, 0 <= i < 32 -> 0 <= r -> Z.land (i + 32 * r) 31 + Z.shiftl r 5 = i + 32 * r.
Proof.
  intros i r Hi Hr. rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
  replace (i + 32 * r) with (i + r * 32) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

Definition keep (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?T => change (keep T) in H end.
Ltac unhide H := unfold keep in H.

Definition pweq (m' m : word -> option byte) : Prop := forall x, m' x = m x.
Lemma pw_ov_read : forall m' m a n, pweq m' m -> ov_read_bytes usegs m' a n = ov_read_bytes usegs m a n.
Proof. intros m' m a n PW. revert a. induction n as [|n IH]; intros a; [reflexivity|]. cbn. rewrite PW, IH. reflexivity. Qed.
Lemma pw_mrd : forall m' m a, pweq m' m -> mrd usegs m' a = mrd usegs m a.
Proof. intros m' m a PW. unfold mrd. rewrite PW. reflexivity. Qed.
Lemma pw_wview : forall m' m a, pweq m' m -> wview usegs m' a = wview usegs m a.
Proof. intros m' m a PW. unfold wview. rewrite PW. reflexivity. Qed.
Lemma pw_mem_inv : forall m' m, pweq m' m -> mem_inv usegs m -> mem_inv usegs m'.
Proof. intros m' m PW H a. unfold mem_ok_at. rewrite PW. apply H. Qed.
Lemma pw_bytes_at : forall m' m a bs, pweq m' m -> bytes_at usegs m a bs -> bytes_at usegs m' a bs.
Proof. intros m' m a bs PW (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros i Hi. rewrite (pw_mrd m' m) by exact PW. apply H. exact Hi. Qed.
Lemma pw_wr_at : forall m' m a n, pweq m' m -> wr_at usegs m a n -> wr_at usegs m' a n.
Proof. intros m' m a n PW (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros i Hi. rewrite (pw_wview m' m) by exact PW. apply H. exact Hi. Qed.
Lemma pw_rw_cells : forall m' m a cs, pweq m' m -> rw_cells usegs m a cs -> rw_cells usegs m' a cs.
Proof. intros m' m a cs PW [[W B] WR]. split; [split; [exact W| eapply pw_bytes_at; eauto]| eapply pw_wr_at; eauto]. Qed.
Lemma pw_stk : forall m' m lo hi, pweq m' m -> stk usegs m lo hi -> stk usegs m' lo hi.
Proof.
  intros m' m lo hi PW (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha. destruct (H a Ha) as [W [b Hb]].
  rewrite (pw_wview m' m), (pw_mrd m' m) by exact PW. split; [exact W| exists b; exact Hb].
Qed.
Lemma pweq_refl : forall m, pweq m m. Proof. intros m x; reflexivity. Qed.
Lemma pweq_trans : forall m1 m2 m3, pweq m1 m2 -> pweq m2 m3 -> pweq m1 m3. Proof. intros m1 m2 m3 A B x. rewrite A. apply B. Qed.

Definition aa3_post (gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 raA s0v s1v : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (P usp : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR raA (wz (usp + 32)) gp tp t0 t1 t2 s0v s1v (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc raA) fc None m' (seg_rom usegs)
    /\ (forall x, m' x = m x) /\ mem_inv usegs m'.

Lemma aa3b_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (raA s0v s1v : word) F fc m
   (P idx rsv b3 : Z),
  let usp := bv_unsigned sp in
  16 <= P -> P + 16 <= 2^64 -> 0 <= idx < 32 -> 0 <= rsv <= 5 -> b3 = idx + 32 * rsv ->
  mem_inv usegs m -> wr_at usegs m (P - 3) 1 -> bytes_at usegs m (P - 3) [b8 b3] -> m (wa (P - 3)) = Some (b8 b3) ->
  rw_cells usegs m (usp + 8) [C8 s1v; C8 s0v; C8 raA] -> usp + 32 <= 2^64 -> P <= usp + 8 ->
  evt usegs (aa3_post gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 raA s0v s1v F fc m P usp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz rsv) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xc2308) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until b3. intros usp P0 PHI IDX RSV HB3 MI W BKc V3 FR UTOP PU. subst usp.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (K31 : Z.land b3 31 = idx). { subst b3. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
    replace (idx + 32 * rsv) with (idx + rsv * 32) by lia. rewrite Z.mod_add, Z.mod_small by lia. reflexivity. }
  unfold wz.

  read_k. st1. clear RK. rewrite ?zxb_b8 by lia.
  st1. rewrite ?(unsigned_lit b3), ?K31 by lia.
  st1. rewrite ?(unsigned_lit rsv), Z.shiftl_mul_pow2 by lia.
  st1. rewrite ?(unsigned_lit (rsv * 2 ^ 5)), ?(unsigned_lit idx) by lia. rewrite (lor_shl5 rsv idx) by lia.
  assert (VB : Z.land idx 31 + Z.shiftl rsv 5 = b3).
  { rewrite Z.shiftl_mul_pow2 by lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32. rewrite Z.mod_small by lia. lia. }
  rewrite VB. hide FR.

  sok 0 1%nat (P + -3).
  st1. rewrite (le1_wz b3) by lia. sdk.
  assert (PW0 : pweq m0 m).
  { rewrite EQm0. intros x. apply write_same; [lia| cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
    replace (P + -3) with (P - 3) by lia. exact V3. }
  unhide FR. pose proof (pw_rw_cells m0 m _ _ PW0 FR) as FR0. clear FR.

  st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold aa3_post. do 15 eexists. split; [reflexivity|]. split; [exact PW0|]. assumption.
Qed.

Lemma aa3_walk : forall ra sp gp tp t0 t1 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (raA s0v s1v : word) F fc m
   (P B E n idx mword stride res b3 : Z),
  let usp := bv_unsigned sp in
  E = B + 16 + stride * (idx + 1) - 4 -> res = E - P - n ->
  16 <= P -> P mod 16 = 0 -> B + 16 <= P -> 0 <= B -> 0 <= n -> P + n <= E -> E + 1 <= 2^64 -> P + 16 <= 2^64 -> 0 <= res < 2^31 -> 0 <= idx < 32 -> 0 <= stride ->
  0 <= mword < 2^64 ->
  b3 = idx + 32 * Z.min res 5 ->
  mem_inv usegs m ->
  wr_at usegs m (P - 3) (E - P + 3) ->
  bytes_at usegs m (P - 3) [b8 b3] ->
  (res <> 0 -> m (wa (E - res)) = Some (b8 0)) ->
  (5 <= res -> m (wa (E - 5)) = Some (b8 0) /\ forall i, (i < 4)%nat -> m (wa (E - 4 + Z.of_nat i)) = nth_error (le4 (wz res)) i) ->
  m (wa (P - 3)) = Some (b8 b3) ->
  rw_cells usegs m (usp + 8) [C8 s1v; C8 s0v; C8 raA] -> usp + 32 <= 2^64 ->
  (E + 1 <= usp + 8) ->
  evt usegs (aa3_post gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 raA s0v s1v F fc m P usp)
      (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (0 - P)) (wz 16) s1 (wz P) (wz idx) (wz n) a3 (wz B) (wz mword) (wz stride) (wz (idx + 1))
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xc2208) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until b3. intros usp HE HR P0 AL BP B0 N0 PNE ETOP PHI RES IDX S0 MW HB3 MI WR BK3 V1 V2 V3 FR UTOP EU. subst usp.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold wz.

  st1. st1. st1. st1. st1.
  assert (A7 : Z.land 15 (bv_unsigned (Z_to_bv 64 (0 - P))) = 0).
  { rewrite unsigned_lit_wrap. replace ((0 - P) mod 2 ^ 64) with (2^64 - P) by (Z.div_mod_to_equations; lia).
    rewrite Z.land_comm. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2^4) with 16. Z.div_mod_to_equations. lia. }
  rewrite A7. st1. replace (B + 16 + stride * (idx + 1) + -4) with E by lia. replace (B + 16 + stride * (idx + 1)) with (E + 4) by lia.
  st1. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. }

  st1. st1. rewrite ?unsigned_lit by lia. rewrite (swrap32_small _) by lia. replace (E - (n + P)) with res by lia.
  st1. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit res) in KR by lia.
  -
    assert (W1 : wr_at usegs m (P - 3) 1) by (eapply wr_at_sub; [exact WR| lia| lia]).
    replace (Z_to_bv 64 res) with (wz (Z.min res 5)) by (unfold wz; f_equal; lia).
    eapply aa3b_walk with (idx := idx) (b3 := b3); try eassumption; try lia.
  -
    st1. rewrite ?unsigned_lit by lia. rewrite (swrap32_small _) by lia. replace (E - (n + P)) with res by lia.
    st1. rewrite ?(unsigned_lit res), (swrap32_small (0 - res)) by lia.
    st1. replace (E + (0 - res)) with (E - res + 0) by lia.
    st1. hide FR. hide BK3.
    sok (n + 3) 1%nat (E - res + 0).
    st1. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    assert (PW0 : pweq m0 m).
    { rewrite EQm0. intros x. apply write_same; [lia| cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
      replace (E - res + 0) with (E - res) by lia. exact (V1 ltac:(lia)). }

    st1. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    +
      st1. unhide FR. unhide BK3. assert (W1 : wr_at usegs m0 (P - 3) 1) by (eapply wr_at_sub; [exact WR| lia| lia]).
      replace (Z_to_bv 64 res) with (wz (Z.min res 5)) by (unfold wz; f_equal; lia).
      eapply evt_mono; [eapply aa3b_walk with (idx := idx) (rsv := Z.min res 5) (b3 := b3) (raA := raA) (s0v := s0v) (s1v := s1v); try lia|].
      * exact MI.
      * exact W1.
      * eapply pw_bytes_at; [exact PW0| exact BK3].
      * rewrite PW0. exact V3.
      * eapply pw_rw_cells; [exact PW0| exact FR].
      * intros ms' X. unfold aa3_post in X |- *. destruct X as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & mm & -> & PW & MI').
        do 15 eexists. split; [reflexivity|]. split; [| exact MI']. eapply pweq_trans; [exact PW| exact PW0].
    +
      destruct (V2 ltac:(lia)) as [V2a V2b].
      sok (E - P - 2) 1%nat (E + 4 + -9).
      st1. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      assert (PW1 : pweq m1 m0).
      { rewrite EQm1. intros x. apply write_same; [lia| cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
        replace (E + 4 + -9) with (E - 5) by lia. rewrite PW0. exact V2a. }
      sok (E - P - 1) 4%nat (E + 4 + -8).
      st1. change (le4 (Z_to_bv 64 res)) with (le4 (wz res)). sdk.
      assert (PW2 : pweq m2 m).
      { rewrite EQm2. intros x. etransitivity; [apply write_same; [lia| cbn; lia|]|].
        - intros i Hi. replace (E + 4 + -8 + Z.of_nat i) with (E - 4 + Z.of_nat i) by lia. rewrite PW1, PW0. apply V2b. cbn in Hi |- *. lia.
        - rewrite PW1. apply PW0. }
      st1. unhide FR. unhide BK3. assert (W1 : wr_at usegs m2 (P - 3) 1) by (eapply wr_at_sub; [exact WR| lia| lia]).
      replace (Z_to_bv 64 5) with (wz (Z.min res 5)) by (unfold wz; f_equal; lia).
      eapply evt_mono; [eapply aa3b_walk with (idx := idx) (rsv := Z.min res 5) (b3 := b3) (raA := raA) (s0v := s0v) (s1v := s1v); try lia|].
      * exact MI.
      * exact W1.
      * eapply pw_bytes_at; [exact PW2| exact BK3].
      * rewrite PW2. exact V3.
      * eapply pw_rw_cells; [exact PW2| exact FR].
      * intros ms' X. unfold aa3_post in X |- *. destruct X as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & mm & -> & PW & MI').
        do 15 eexists. split; [reflexivity|]. split; [| exact MI']. eapply pweq_trans; [exact PW| exact PW2].
Qed.

Lemma aa_tail_walk : forall ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (raA s0v s1v : word) F fc m
   (P G B A E n : Z) (b3 off16 avail freed last_idx freeable sc maplen secret stride res : Z) (prev next : word),
  let usp := bv_unsigned sp in
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  0 <= n < 2^32 -> 0 < P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> 0 <= B -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  E = B + 16 + stride * (idx + 1) - 4 -> res = E - P - n -> P + n <= E -> E + 1 <= 2^64 -> 0 <= res < 2^31 -> 0 <= stride ->
  b3 = idx + 32 * Z.min res 5 ->
  ov_read_bytes usegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes usegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes usegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes usegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells usegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes usegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes usegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes usegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63) ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  (maplen <> 0 -> last_idx = 0 -> stride = maplen * 4096 - 16) ->
  (maplen = 0 \/ last_idx <> 0 -> stride = 16 * size_class sc) ->
  mem_inv usegs m ->
  wr_at usegs m (P - 3) (E - P + 3) ->
  bytes_at usegs m (P - 3) [b8 b3] ->
  (res <> 0 -> m (wa (E - res)) = Some (b8 0)) ->
  (5 <= res -> m (wa (E - 5)) = Some (b8 0) /\ forall i, (i < 4)%nat -> m (wa (E - 4 + Z.of_nat i)) = nth_error (le4 (wz res)) i) ->
  m (wa (P - 3)) = Some (b8 b3) ->
  rw_cells usegs m (usp + 8) [C8 s1v; C8 s0v; C8 raA] -> usp + 32 <= 2^64 -> E + 1 <= usp + 8 ->
  evt usegs (aa3_post gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 raA s0v s1v F fc m P usp)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz 16) (wz n) (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xc20e0) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until next. intros usp idx mword HN P0 AL PLO PHI HB B0 HA GLO GHI HE HR PNE ETOP RES S0 HB3 R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml SC48 HSTR1 HSTR2 MI WR BK3 V1 V2 V3 FRM UTOP EU.
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  eapply evt_cut.
  { eapply (aa1_walk ra sp gp tp t0 t1 t2 (wz 16) (wz n) (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P G B A n b3 off16 avail freed last_idx freeable sc maplen secret prev next);
      first [reflexivity| eassumption| lia]. }
  intros ms1 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & -> & -> & ->).
  eapply evt_cut.
  { eapply (aa2_walk ra sp gp tp u2 (wz 16) (wz n) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m P B n idx off16 last_idx freeable sc maplen stride);
      first [eassumption| lia]. }
  intros ms2 (v0 & v2 & va3 & v3 & v4 & v5 & v6 & -> & ->).
  eapply (aa3_walk ra sp gp tp v0 (wz (2 * sc)) (wz n) va3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 raA s0v s1v F fc m P B E n idx mword stride res b3);
    first [eassumption| lia| idtac].
Qed.

Fixpoint segs_bot (sg : list Segment) : Z :=
  match sg with
  | [] => 2^64
  | s0 :: rest => Z.min (Z.of_N (seg_base s0)) (segs_bot rest)
  end.
Lemma find_segment_low : forall sg a n, 0 <= n -> a + n <= segs_bot sg -> a < segs_bot sg -> find_segment sg a n = None.
Proof.
  induction sg as [|s0 sg IH]; intros a n Hn Ha Hlt; [reflexivity|]. cbn [find_segment segs_bot] in *.
  replace (Z.leb (Z.of_N (seg_base s0)) a) with false by (symmetry; apply Z.leb_gt; lia).
  cbn [andb]. apply IH; lia.
Qed.
Lemma seg_rom_out : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x111000 <= a) -> a < 2^64 -> seg_rom usegs (wa a) = None.
Proof.
  intros a H0 Ha H64. unfold seg_rom, memory_read. unfold wa. rewrite unsigned_lit by lia.
  destruct Ha as [Ha|Ha].
  - rewrite find_segment_low; [reflexivity| lia| |]; change (segs_bot usegs) with 0x10000; lia.
  - rewrite (InitMem.find_segment_high usegs); [reflexivity| lia|]. change (InitMem.segs_top usegs) with 0x111000. lia.
Qed.
Lemma ov1_raw : forall (m : word -> option byte) a x,
  ov_read_bytes usegs m (wa a) 1 = Some [x] -> 0 <= a -> (a + 1 <= 0x10000 \/ 0x111000 <= a) -> a < 2^64 -> m (wa a) = Some x.
Proof.
  intros m a x H H0 Ha H64. cbn in H. pose proof (seg_rom_out a H0 Ha H64) as SR. unfold seg_rom in SR.
  destruct (m (wa a)) as [b|]; [congruence|]. rewrite SR in H. discriminate.
Qed.

Lemma b8_land255 : forall y, 0 <= y -> Z_to_bv 8 y = b8 (Z.land y 255).
Proof. intros y Hy. unfold b8. apply Z_to_bv8_mod. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma le4_byte_of : forall x, 0 <= x < 2^32 -> le4 (wz x) = [b8 (byte_of x 0); b8 (byte_of x 1); b8 (byte_of x 2); b8 (byte_of x 3)].
Proof.
  intros x Hx. unfold le4, word_to_le_bytes, wz, byte_of. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes Z.mul].
  rewrite !Z.shiftr_shiftr by lia. cbn [Z.add].
  rewrite (b8_land255 x), (b8_land255 (x ≫ 8)), (b8_land255 (x ≫ 16)), (b8_land255 (x ≫ 24)) by (rewrite ?Z.shiftr_nonneg; lia).
  rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma aa_tail_spec : forall ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (raA s0v s1v : word) F fc m
   st L BL LS LB0 (pid : bptr) (P n : Z),
  let usp := bv_unsigned sp in
  rmrep st m -> mem_inv usegs m -> CINV st LB0 -> INVL x0 st L BL LS -> CORR st LB0 BL -> In (pid, P, n) LB0 ->
  (forall g i, (s_slots st) !! (fst pid) = Some (g, i) -> get_stride (get_meta_rec st g) - IB - n < 2^31) ->
  0 <= n < 2^32 ->
  rw_cells usegs m (usp + 8) [C8 s1v; C8 s0v; C8 raA] -> usp + 32 <= 2^64 -> alloc_ceiling <= usp ->
  evt usegs (aa3_post gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 raA s0v s1v F fc m P usp)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz 16) (wz n) (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xc20e0) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until n. intros usp MR MI C INV CR Hin XRES HN FRM UTOP CEIL.

  destruct (Forall2_In_l _ _ _ _ CR Hin) as (k & Hk & (E1 & E2 & E3)). destruct k as [[c off] n']. cbn [blk_slot blk_size blk_addr bslot bsize boff fst snd] in E1, E2, E3. subst n'.
  destruct (block_facts x0 st L BL LS INV c off n Hk) as (g & bm & i & ai & a & ar & ka & BF).
  pose proof BF as [SL HO MEM HC BI BLI BAI BOFF BN FIT STR B16 NA NF NH BSC TOP MPL AREA SHD HDR0 BYT].
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (HOS : hosts st bm g) by (exists ai; exact HO).
  pose proof (ci_gmetas _ _ C bm g HOS) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & Bm0 & Bm16 & SPAN & _).
  pose proof MR as (WF & CX & GL & ARr & GR & SH). pose proof WF as (Hres & WRr & DISJ & WA & WG).
  destruct (WRr (fst bm) r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in RBC.
  destruct (ir_shape _ _ _ IR _ _ Hr) as (RBpos & _ & RLpos & _).
  pose proof (round_up_pg_ge (r_len r)) as RU.
  pose proof (rreserved_disjoint1 _ _ RFr ltac:(lia)) as DRr.

  unfold MI_Inv.MR in *.
  set (mr := get_meta_rec st g) in *.
  set (stride := get_stride mr) in *.
  set (B := r_base r + snd bm).
  set (q := (snd c + UNIT * off - snd bm - UNIT) / UNIT).
  assert (SX : stride * (i + 1) = stride * i + stride) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; reflexivity).
  set (E := B + 16 + stride * i + stride - 4).
  set (res := E - P - n).
  set (b3 := i + 32 * Z.min res 5).
  set (G := conc st g). set (A := conc st (area_of g)).
  assert (Fc : fst c = fst bm) by (rewrite HC; reflexivity).
  assert (Hrc : s_regions st !! (fst c) = Some r) by (rewrite Fc; exact Hr).
  assert (Sc : snd c = snd bm + 16 + stride * i). { rewrite HC. cbn [snd]. unfold sstart, gbase. fold mr. rewrite MEM. cbn. unfold UNIT. lia. }
  assert (HP : P = B + 16 + stride * i + 16 * off). { rewrite E3, (conc_region' st c r Hrc), Sc. unfold B, UNIT. lia. }
  pose proof (q16 _ _ _ _ _ _ _ _ _ _ _ BF) as [Q16 QR]. cbn [snd aadd] in Q16, QR. unfold MI_Inv.MR in Q16, QR. fold mr in Q16. fold mr in QR. fold stride in Q16. fold q in Q16. fold q in QR.
  unfold UNIT in Q16.
  destruct STR as [S16 SMOD]. clear B16.
  unfold sstart_of in SPAN. fold mr in SPAN. rewrite MEM in SPAN. cbn [default id snd] in SPAN. fold stride in SPAN. unfold UNIT in SPAN.
  assert (SIL : stride * i + stride <= stride * (m_last_idx mr + 1)) by (rewrite <- SX; apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia).
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  unfold IB, UNIT in FIT. fold mr stride in FIT.
  assert (E1' : fst pid = c) by exact E1.
  assert (RES31 : res < 2^31). { specialize (XRES g i ltac:(rewrite E1'; exact SL)). fold mr stride in XRES. unfold IB in XRES. subst res E. lia. }
  assert (RES0 : 0 <= res) by (subst res E; lia).
  assert (ETOP : E + 1 <= r_base r + round_up_pg (r_len r)) by (subst E B; lia).
  assert (RESE : res = stride - 4 - 16 * off - n) by (subst res E B; rewrite HP; lia).
  assert (CRNG : 16 <= snd c /\ snd c + stride - 4 + 1 <= round_up_pg (r_len r)) by (rewrite Sc; clear - SPAN SIL SI0 Bm0 S16; unfold UNIT in *; lia).

  pose proof SHD as SK. unfold blk_shadow_ok in SK. cbn [bslot boff bsize fst snd] in SK. unfold gbase in SK. fold mr in SK. rewrite MEM in SK. cbn [default id snd] in SK.
  fold stride in SK. fold q in SK.
  destruct SK as (K4 & K3 & K2 & K1 & _ & K5 & K6 & _).
  replace (snd c + stride - IB - (snd c + UNIT * off) - n) with res in K3, K5, K6 by (subst res E; unfold IB, UNIT; lia).
  fold b3 in K3.

  destruct (rmrep_shadow_read st m (fst bm) r (snd c + UNIT * off - 4) 0 MR Hr Kr ltac:(unfold UNIT; lia) ltac:(rewrite <- Fc; exact K4)) as [R4 _].
  destruct (rmrep_shadow_read st m (fst bm) r (snd c + UNIT * off - 3) b3 MR Hr Kr ltac:(unfold UNIT; lia) ltac:(rewrite <- Fc; exact K3)) as [R3 B3R].
  destruct (rmrep_shadow_read2 st m (fst bm) r (snd c + UNIT * off - 2) (byte_of q 0) (byte_of q 1) MR Hr Kr ltac:(unfold UNIT; lia) ltac:(unfold UNIT; lia)
              ltac:(rewrite <- Fc; exact K2) ltac:(rewrite <- Fc; replace (snd c + UNIT * off - 2 + 1) with (snd c + UNIT * off - 1) by lia; exact K1)) as (R2 & Q0 & Q1).
  rewrite <- (le2_lohi _ _ Q0 Q1), (u16_bytes q QR) in R2.
  replace (r_base r + (snd c + UNIT * off - 4)) with (P - 4) in R4 by (rewrite HP, Sc; unfold B, UNIT; lia).
  replace (r_base r + (snd c + UNIT * off - 3)) with (P - 3) in R3 by (rewrite HP, Sc; unfold B, UNIT; lia).
  replace (r_base r + (snd c + UNIT * off - 2)) with (P - 2) in R2 by (rewrite HP, Sc; unfold B, UNIT; lia).

  destruct (rmrep_group_read st m bm _ MR HO) as [RG _]. cbn [g_meta pw oconc] in RG. fold G in RG. rewrite (conc_region' st bm r Hr) in RG. fold B in RG.
  destruct AREA as (Ha & Hck & Hal & Hka & Eg).
  assert (MS : meta_slot st g) by (exists a, ar, ka; split; [exact Ha| split; [exact Hka| rewrite Eg; reflexivity]]).
  pose proof (rmrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite MEM in MM. unfold pw in MM, RG. cbn [oconc] in MM, RG.
  rewrite (conc_region' st bm r Hr) in MM. fold B G in MM. unfold meta_word in MM.

  assert (Har : s_areas st !! (area_of g) = Some ar) by (rewrite Eg, (area_of_mslot a ka Hal Hka); exact Ha).
  assert (INIT : c_init_done (ctx st) <> 0).
  { destruct (ia_secret _ IA) as [_ [(_ & _ & E0)|(ED1 & _)]]; [| unfold ctx; rewrite ED1; lia]. exfalso. rewrite E0 in Ha. rewrite lookup_empty in Ha. discriminate. }
  pose proof (rmrep_area_check_read st m (area_of g) ar MR Har) as RA. fold A in RA. rewrite Hck in RA.
  pose proof (rmrep_ctx_secret_read st m MR) as RC. rewrite (rsec_init _ _ INIT) in RC.
  change (c_secret (s_ctx st)) with (c_secret (ctx st)) in RA.
  rewrite <- (wz_mod64 (c_secret (ctx st) + bv_unsigned rr_secret)) in RA, RC.

  destruct (WA a ar Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
  assert (HG : G = r_base rg + snd a + (AREA_HDR + META_SIZE * ka)).
  { unfold G. rewrite Eg. unfold mslot. rewrite conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  destruct (WRr (fst a) rg Hrg) as (RG0 & RGAL & RGL0 & RGC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in RGC.
  assert (Hm4 : (r_base rg + snd a + (AREA_HDR + META_SIZE * ka)) mod 4096 = AREA_HDR + META_SIZE * ka).
  { clear - AAL RGAL Hka A0 Hal RG0. unfold AREA_HDR, META_SIZE, NSLOTS, PGSZ in *.
    replace (r_base rg + snd a + (24 + 40 * ka)) with ((24 + 40 * ka) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (HA : A = G - G mod 4096).
  { unfold A. rewrite HG, Hm4. rewrite Eg, (area_of_mslot a ka Hal Hka), (conc_region' st a rg Hrg). unfold AREA_HDR, META_SIZE. lia. }

  unfold tbit in NA, NF. fold mr in NA, NF.
  pose proof (go_avail _ _ _ GO) as AVr. pose proof (go_freed _ _ _ GO) as FRr. pose proof (go_maplen _ _ _ GO) as MLr. fold mr in AVr, FRr, MLr.
  pose proof (go_freeable _ _ _ GO) as FBL. fold mr in FBL.
  pose proof (proj2 (proj2 (proj2 (proj2 (ci_cx _ _ C))))) as SEr.

  assert (RAW : forall o v, cell_read (get_shadow st (fst bm)) o = Known v -> 0 <= o < round_up_pg (r_len r) -> m (wa (r_base r + o)) = Some (b8 v)).
  { intros o v Ko Ho. destruct (rmrep_shadow_read st m (fst bm) r o v MR Hr Kr Ho Ko) as [Rd _]. apply (ov1_raw m _ _ Rd); clear - Ho DRr RBpos RBC RU; lia. }
  assert (IDXE : Z.land b3 31 = i) by (subst b3; apply land31_idx; lia).
  eapply (aa_tail_walk ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 raA s0v s1v F fc m P G B A E n b3 q
            (m_avail mr) (m_freed mr) (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) ((c_secret (ctx st) + bv_unsigned rr_secret) mod 2^64) stride res
            (wz (oconc st (m_prev mr))) (wz (oconc st (m_next mr))));
    rewrite ?IDXE; first [eassumption | idtac].
  all: pose proof (go_li _ _ _ GO) as LIr; pose proof (go_sc _ _ _ GO) as SCr; fold mr in LIr, SCr.
  -   rewrite HP. clear - RBpos Bm0 SI0 BOFF. subst B. lia.
  -   pose proof (p_mod16 _ _ _ _ _ _ _ _ _ _ _ BF) as PM. cbn [snd aadd] in PM. rewrite E3, (conc_region' st c r Hrc).
    clear - PM RBAL. unfold UNIT in *. Z.div_mod_to_equations. lia.
  - rewrite HP. clear - Q16 Bm0 RBpos BOFF. subst B. lia.
  - subst res E B. rewrite HP in RES0. rewrite HP. clear - ETOP RBC CEIL_RANGE__ RES0 BN Bm0 SI0 BOFF RBpos. unfold ceil_window in *. lia.
  - rewrite HP. clear - Q16. subst B. lia.
  - clear - RBpos Bm0. subst B. lia.
  - rewrite HG. clear - RG0 A0 Hka. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
  - rewrite HG. clear - RGC A1 Hka CEIL_RANGE__. unfold AREA_HDR, META_SIZE, NSLOTS, ceil_window in *. lia.
  - clear - SX. subst E. lia.
  - reflexivity.
  - clear - RES0. subst res. lia.
  - clear - ETOP RBC CEIL_RANGE__. unfold ceil_window in *. lia.
  - clear - RES0 RES31. lia.
  - clear - S16. unfold UNIT in S16. lia.
  - reflexivity.
  - intros Hlt. apply rsize_classes_read; [exact MI| clear - Hlt SCr; lia].
  - apply rsec_range.
  - clear - LIr. lia.
  - clear - FBL. lia.
  - clear - SCr. lia.
  - clear - MLr. lia.
  - exact (proj2 BI).
  -   intros Hlt. clear K4 K3 K2 K1 K5 K6 RAW.
    destruct BSC as [(Hsc & Hle & Hst)| E63]; [| exfalso; clear - Hlt E63; subst mr; unfold MI_Inv.MR in E63; lia].
    fold mr in Hsc, Hle, Hst. fold stride in Hle, Hst. unfold UNIT in Hle, Hst.
    pose proof (size_class_bound _ Hsc) as SB.
    assert (AA : stride = 16 * size_class (m_sizeclass mr) \/ m_last_idx mr = 0) by (clear - Hst; tauto).
    assert (BB : stride <= 16 * size_class (m_sizeclass mr) \/ 292 <= size_class (m_sizeclass mr)).
    { destruct Hle as [Hle|H28]; [left; exact Hle| right; apply size_class_28; lia]. }
    clear - SB Q16 FIT BN BOFF BI AA BB. eapply (guard16_arith _ stride i off n q (m_last_idx mr)); try eassumption; lia.
  - clear - SCr. lia.
  -   intros NM. clear K4 K3 K2 K1 K5 K6 RAW.
    destruct (TOP ltac:(fold mr; exact NM)) as [Bz GE]. unfold gend, cnt_of, sstart, gbase in GE. fold mr in GE. rewrite MEM in GE. cbn [default id snd] in GE. rewrite Bz in GE.
    fold stride in GE. unfold UNIT in GE.
    clear - S16 Q16 FIT BN BOFF BI GE. unfold UNIT in S16.
    assert (DV : m_maplen mr * 4096 / 16 = m_maplen mr * 256) by (replace (m_maplen mr * 4096) with (m_maplen mr * 256 * 16) by lia; apply Z.div_mul; lia).
    pose proof (guard17_arith stride i off n q (m_last_idx mr) (m_maplen mr) S16 Q16 FIT BN ltac:(lia) BI ltac:(lia)) as X. rewrite DV in X. exact X.
  - clear - SCr. lia.
  - intros Hml0 Hli. subst stride. unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) Hli).
    replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hml0). cbn [andb negb]. unfold UNIT. lia.
  - intros Hcase. subst stride. unfold get_stride.
    destruct (Z.eqb_spec (m_last_idx mr) 0); destruct (Z.eqb_spec (m_maplen mr) 0); cbn [andb negb]; unfold UNIT; try lia.
  -   destruct (SH (fst bm) r Hr Kr) as [WRG _]. eapply wr_at_sub; [exact WRG| |]; rewrite HP; clear - Bm0 SI0 BOFF ETOP RES0; subst res E B; lia.
  -   split; [clear - HP RBpos Bm0 SI0 BOFF; subst B; lia|]. split; [cbn; clear - ETOP RBC CEIL_RANGE__ RES0 BN; subst res; unfold ceil_window in *; lia|].
    intros j Hj. destruct j; [| cbn in Hj; lia]. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. unfold mrd.
    rewrite (RAW (snd c + UNIT * off - 3) b3); [reflexivity| rewrite <- Fc; exact K3| rewrite Sc; clear - SPAN SIL SI0 BOFF Bm0 FIT BN S16; unfold UNIT in *; lia] || idtac.
    all: try (replace (P - 3) with (r_base r + (snd c + UNIT * off - 3)) by (rewrite HP, Sc; subst B; unfold UNIT; lia);
              rewrite (RAW (snd c + UNIT * off - 3) b3); [reflexivity| rewrite <- Fc; exact K3| rewrite Sc; clear - SPAN SIL SI0 BOFF Bm0 FIT BN S16; unfold UNIT in *; lia]).
  -   intros NZ. replace (E - res) with (r_base r + (snd c + stride - IB - res)) by (subst E B; rewrite Sc; unfold IB, UNIT; clear; lia).
    apply RAW; [rewrite <- Fc; apply K6; clear - NZ RES0; lia|]. clear - CRNG RESE RES0 NZ BOFF BN. unfold IB in *. lia.
  -   intros R5. destruct (K5 R5) as (Ka & Kb & Kc & Kd & Ke & R32). split.
    + replace (E - 5) with (r_base r + (snd c + stride - IB - 5)) by (subst E B; rewrite Sc; unfold IB, UNIT; clear; lia).
      apply RAW; [rewrite <- Fc; exact Ke|]. clear - CRNG RESE RES0 R5 BOFF BN. unfold IB in *. lia.
    + intros j Hj. rewrite (le4_byte_of res) by (clear - RES0 R32; lia).
      replace (E - 4 + Z.of_nat j) with (r_base r + (snd c + stride - IB - 4 + Z.of_nat j)) by (subst E B; rewrite Sc; unfold IB, UNIT; clear; lia).
      assert (RNG : 0 <= snd c + stride - IB - 4 + Z.of_nat j < round_up_pg (r_len r)) by (clear - CRNG RESE RES0 R5 BOFF BN Hj; unfold IB in *; lia).
      destruct j as [|[|[|[|j]]]]; [| | | | cbn in Hj; lia]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ].
      * rewrite (RAW _ (byte_of res 0)); [reflexivity| rewrite <- Fc; replace (snd c + stride - IB - 4 + 0) with (snd c + stride - IB - 4) by lia; exact Ka| exact RNG].
      * rewrite (RAW _ (byte_of res 1)); [reflexivity| rewrite <- Fc; replace (snd c + stride - IB - 4 + 1) with (snd c + stride - IB - 3) by lia; exact Kb| exact RNG].
      * rewrite (RAW _ (byte_of res 2)); [reflexivity| rewrite <- Fc; replace (snd c + stride - IB - 4 + 2) with (snd c + stride - IB - 2) by lia; exact Kc| exact RNG].
      * rewrite (RAW _ (byte_of res 3)); [reflexivity| rewrite <- Fc; replace (snd c + stride - IB - 4 + 3) with (snd c + stride - IB - 1) by lia; exact Kd| exact RNG].
  -   replace (P - 3) with (r_base r + (snd c + UNIT * off - 3)) by (rewrite HP, Sc; subst B; unfold UNIT; clear; lia).
    apply RAW; [rewrite <- Fc; exact K3|]. clear - CRNG RESE RES0 BOFF BN. unfold UNIT in *. lia.
  -   clear - ETOP RBC CEIL. lia.
Qed.
End WithCeiling0.
