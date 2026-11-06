(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import F_malloc_free F_malloc_fast MallocKit_B3.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_B RF_get_meta.
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
Definition raa_meta_post (rav sp gp tp a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (P B idx n sc stride al adj : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t2 t3,
    ms' = MS (mkR rav sp gp tp t0 (Z_to_bv 64 (sc * 2)) t2 (Z_to_bv 64 (al - 1)) (Z_to_bv 64 n) a0 (Z_to_bv 64 idx) (Z_to_bv 64 n)
                  (Z_to_bv 64 (B + 16 + stride * (idx + 1))) (Z_to_bv 64 (B + 16 + stride * (idx + 1) - 4)) (Z_to_bv 64 (B + 16)) (Z_to_bv 64 stride) (Z_to_bv 64 adj)
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x270f98) fc None m (seg_rom rsegs).

Lemma raa_meta_walk : forall rav sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret stride n al k : Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  bv_unsigned a0 = P -> 0 < P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  s0 = Z_to_bv 64 al -> s1 = Z_to_bv 64 n -> al = 2 ^ k -> 4 <= k <= 6 -> 0 <= n < 2^32 ->
  ov_read_bytes rsegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes rsegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes rsegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes rsegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells rsegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes rsegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes rsegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 48 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  size_class sc * idx <= off16 < size_class sc * (idx + 1) ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  stride = (if negb (maplen =? 0) && (last_idx =? 0) then 4096 * maplen - 16 else 16 * size_class sc) ->
  evt rsegs (raa_meta_post rav sp gp tp a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m P B idx n sc stride al ((- P) mod al))
      (MS (mkR rav sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x270e58) fc None m (seg_rom rsegs)).
Proof. try hcb. try hsb.
  intros until next. intros idx mword HP P0 AL PLO PHI HB HA GLO GHI HS0 HS1 HAL HK N R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hml STR.
  subst s0 s1.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  assert (ALR : 16 <= al <= 64).
  { rewrite HAL. split; [change 16 with (2^4); apply Z.pow_le_mono_r; lia| change 64 with (2^6); apply Z.pow_le_mono_r; lia]. }
  (* [comment removed for export] *)
  st1. if_cases Kz; zify_cond Kz. { exfalso. lia. }
  (* [comment removed for export] *)
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. fold idx. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  rewrite ?HP. st1. rewrite ?HP.
  assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  st1. st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
  assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }
  (* [comment removed for export] *)
  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  st1. st1. st1. st1. rewrite MW2. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1.
  if_cases K8; zify_cond K8. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia. lia. }
  (* [comment removed for export] *)
  st1. replace (466696 + sc * 2) with (466696 + 2 * sc) by lia.
  assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (466696 + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))).
  { replace (Z_to_bv 64 (466696 + 2 * sc)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
  pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
  try rewrite (Z.mod_small (size_class sc)) by lia.
  st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
  (* [comment removed for export] *)
  st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
  st1.
  (* [comment removed for export] *)
  assert (MW12 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (MWP : mword - mword mod 4096 = 4096 * maplen).
  { subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. lia. }
  st1. rewrite ?(wz_unsigned mword) by lia. rewrite MW12. st1. rewrite ?HP. st1.
  (* [comment removed for export] *)
  assert (ADJ : Z.land (al + -1) (bv_unsigned (Z_to_bv 64 (0 + - P))) = (- P) mod al).
  { rewrite unsigned_lit_wrap, Z.land_comm. replace (al + -1) with (Z.ones k) by (rewrite HAL, Z.ones_equiv; unfold Z.pred; lia).
    rewrite Z.land_ones by lia. rewrite <- HAL. replace (0 + - P) with (- P) by lia. apply Z.mod_mod_divide.
    exists (2 ^ (64 - k)). rewrite HAL, <- Z.pow_add_r by lia. f_equal. lia. }
  assert (KJ : forall t0v t3v a3v, evt rsegs (raa_meta_post rav sp gp tp a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m P B idx n sc stride al ((- P) mod al))
    (MS (mkR rav sp gp tp t0v (Z_to_bv 64 (sc * 2)) (Z_to_bv 64 (0 + - P)) (Z_to_bv 64 al) (Z_to_bv 64 n) a0 (Z_to_bv 64 idx) (Z_to_bv 64 n) a3v (wz B) (wz mword)
              (Z_to_bv 64 stride) (Z_to_bv 64 (idx + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6) F (Z_to_bv 64 0x270f80) fc None m (seg_rom rsegs))).
  assert (STRR : 0 <= stride < 2 ^ 53).
  { rewrite STR. pose proof (size_class_range sc ltac:(lia)). destruct (Z.eqb_spec maplen 0); destruct (Z.eqb_spec last_idx 0); cbn [negb andb]; lia. }
  { intros t0v t3v a3v.
    (* [comment removed for export] *)
    st1. rewrite ?(wz_unsigned B) by lia. st1. st1. st1. st1. rewrite ?(unsigned_lit (al + -1)), ?(unsigned_lit stride), ?(unsigned_lit (idx + 1)) by lia. rewrite ?ADJ. st1.
    replace (B + 16 + stride * (idx + 1) + -4) with (B + 16 + stride * (idx + 1) - 4) by lia. replace (al + -1) with (al - 1) by lia.
    apply evt_done. unfold raa_meta_post. do 3 eexists. reflexivity. }
  assert (K38 : forall t3v, maplen = 0 \/ last_idx <> 0 ->
    evt rsegs (raa_meta_post rav sp gp tp a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m P B idx n sc stride al ((- P) mod al))
    (MS (mkR rav sp gp tp (Z_to_bv 64 466696) (Z_to_bv 64 (sc * 2)) (Z_to_bv 64 (0 + - P)) (Z_to_bv 64 al) (Z_to_bv 64 n) a0 (Z_to_bv 64 idx) (Z_to_bv 64 n) (wz off16) (wz B) (wz mword)
              (Z_to_bv 64 last_idx) (Z_to_bv 64 (idx + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6) F (Z_to_bv 64 0x270f74) fc None m (seg_rom rsegs))).
  { intros t3v HC.
    (* [comment removed for export] *)
    st1. replace (466696 + sc * 2) with (466696 + 2 * sc) by lia. st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride).
    2:{ f_equal. rewrite STR. destruct HC as [-> | NZ]; [cbn [Z.eqb negb andb]; lia|]. replace (last_idx =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite andb_false_r. lia. }
    apply KJ. }
  if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  - apply K38. left. exact Km.
  - (* [comment removed for export] *)
    st1. st1. st1. if_cases Km2; zify_cond Km2.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in Km2 by lia. change (2^8) with 256 in Km2. change 18446744073709551615 with (Z.ones 64) in Km2.
        rewrite Z.land_ones, wz_unsigned in Km2 by lia. rewrite Z.mod_small in Km2 by lia. specialize (Hml Km). lia. }
    (* [comment removed for export] *)
    st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
    + (* [comment removed for export] *)
      st1. st1. rewrite land_pgmask by lia. rewrite ?(wz_unsigned mword) by lia. rewrite MWP. st1. st1.
      replace (Z_to_bv 64 (4096 * maplen + -16)) with (Z_to_bv 64 stride).
      2:{ f_equal. rewrite STR, (proj2 (Z.eqb_eq _ _) Kl). replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb]. lia. }
      apply KJ.
    + apply K38. right. exact Kl.
Qed.
End HCW.
