(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import F_malloc_free F_malloc_fast F_free_A.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta RF_free_A.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := unfold alloc_ceiling, UNIT, IB in *; lia.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition rrealloc_entry : Z := 0x19174.

Lemma land_ones_small y : 0 <= y < 2^64 -> Z.land y 18446744073709551615 = y.
Proof. intros. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Definition rre_frame (s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition rrh1_post (ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 gw : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (B b3 off16 mword sc : Z) : machine_state -> Prop :=
  fun ms' => exists t3 t4,
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (Z.land b3 31)) (Z_to_bv 64 (Z.land mword 31)) (Z_to_bv 64 (sc * 2))
                  s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 68648) (wz off16) (wz b3)
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x192c0) fc None m (seg_rom rsegs).

(* [comment removed for export] *)
Lemma rrealloc_h1_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret : Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  ov_read_bytes rsegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes rsegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes rsegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes rsegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells rsegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes rsegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes rsegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63) ->
  0 <= B ->
  evt rsegs (rrh1_post ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (wz G) F fc m B b3 off16 mword sc)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x191cc) fc None m (seg_rom rsegs)).
Proof.
  intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 B0.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  (* [comment removed for export] *)
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. } clear K.
  (* [comment removed for export] *)
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. } clear K2.
  (* [comment removed for export] *)
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?wz_unsigned in K3 by lia. lia. } clear K3.
  replace (Z_to_bv 64 (P - off16 * 16 + -16 + -16 + 16)) with (wz B) by (unfold wz; f_equal; lia).
  (* [comment removed for export] *)
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit, ?MW1 in K4 by lia. lia. } clear K4.
  (* [comment removed for export] *)
  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
  assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. } clear K5.
  (* [comment removed for export] *)
  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. } clear K6.
  (* [comment removed for export] *)
  st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. } clear K7.
  (* [comment removed for export] *)
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  st1. st1. st1. st1. rewrite MW2. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1.
  if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by lia.
  - (* [comment removed for export] *) specialize (Hsc63 ltac:(lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?unsigned_lit in K9 by lia. lia. } clear K9.
    apply evt_done. unfold rrh1_post. rewrite MW1. exists (Z_to_bv 64 63). eexists. rewrite GW. reflexivity.
  - specialize (RS ltac:(lia)). specialize (Hsc ltac:(lia)).
    (* [comment removed for export] *)
    st1.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (68648 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (68648 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    clear RS. pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. } clear K10.
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. } clear K11.
    st1. apply evt_done. unfold rrh1_post. rewrite MW1. do 2 eexists. rewrite GW. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rrh2_post (ra sp gp tp s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 gw : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (P B b3 mword sc S stride rsv : Z) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4,
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (S + stride - 4)) (Z_to_bv 64 S) t2
                  s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 68648) (Z_to_bv 64 (S + stride)) (Z_to_bv 64 (S + stride - 4 - P))
                  (Z_to_bv 64 (S + stride - 4 - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19358) fc None m (seg_rom rsegs).

(* [comment removed for export] *)
Lemma rrealloc_h2_walk : forall ra sp gp tp t3 t4 s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 gw F fc m
   (P B : Z) (b3 off16 last_idx freeable sc maplen r32 : Z),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let stride := if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc in
  let S := B + 16 + stride * idx in
  let E := S + stride - 4 in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  bv_unsigned a0 = P -> mem_inv rsegs m ->
  (sc < 48 -> ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  0 <= B -> 16 <= stride -> P <= E -> E + 1 <= 2^64 ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at rsegs m (E - 4) (le4 (wz r32)) /\ bytes_at rsegs m (E - 5) [b8 0]) ->
  rsv <= E - P -> bytes_at rsegs m (E - rsv) [b8 0] -> bytes_at rsegs m E [b8 0] ->
  evt rsegs (rrh2_post ra sp gp tp s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 gw F fc m P B b3 mword sc S stride rsv)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 (Z.land mword 31)) (Z_to_bv 64 (sc * 2))
               s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 68648) (wz off16) (wz b3)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x192c0) fc None m (seg_rom rsegs)).
Proof.
  intros until r32. intros idx mword stride S E rsv0 rsv HP MI RS B3 O16 LI FB SC ML Hml SC48 B0 S16 PE EHI BIG RSVLE RB0r RE0.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (MW12 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (MWP : mword - mword mod 4096 = 4096 * maplen).
  { subst mword.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. lia. }
  assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  pose proof (bv_unsigned_in_range 64 a0) as A0R. change (bv_modulus 64) with (2^64) in A0R.
  pose proof (bytes_at_read rsegs m _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr.
  change (take 1 (drop (Z.to_nat 0) [b8 0])) with [b8 0] in RDr. rewrite Z.add_0_r in RDr.
  pose proof (bytes_at_read rsegs m _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe.
  change (take 1 (drop (Z.to_nat 0) [b8 0])) with [b8 0] in RDe. rewrite Z.add_0_r in RDe.
  (* [comment removed for export] *)
  assert (K2 : forall t2v t3v,
    evt rsegs (rrh2_post ra sp gp tp s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 gw F fc m P B b3 mword sc S stride rsv)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 (Z.land mword 31)) t2v
               s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 68648) (Z_to_bv 64 stride) (wz b3)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6) F (Z_to_bv 64 0x192e8) fc None m (seg_rom rsegs))).
  { intros t2v t3v.
    (* [comment removed for export] *)
    st1. st1. st1. st1. st1. st1. st1.
    rewrite ?(wz_unsigned B), ?(wz_unsigned b3), ?unsigned_lit by lia. fold rsv0.
    replace (B + stride * idx + 16) with S by (unfold S; lia).
    replace (S + stride + -4) with E by (unfold E; lia).
    (* [comment removed for export] *)
    assert (TAIL : forall a7v,
      evt rsegs (rrh2_post ra sp gp tp s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 gw F fc m P B b3 mword sc S stride rsv)
        (MS (mkR ra sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 S) (Z_to_bv 64 rsv)
                 s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 68648) (Z_to_bv 64 (S + stride)) a7v
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 160) t4 t5 t6) F (Z_to_bv 64 0x19330) fc None m (seg_rom rsegs))).
    { intros a7v.
      (* [comment removed for export] *)
      st1. rewrite ?HP, ?unsigned_lit by lia. replace (E + - P) with (E - P) by lia.
      st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?land_ones_small, ?unsigned_lit in K1 by lia. lia. } clear K1.
      rewrite ?land_ones_small by lia.
      (* [comment removed for export] *)
      st1. rewrite ?unsigned_lit by lia. replace (E + - rsv) with (E - rsv) by lia.
      change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
      st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. } clear K2.
      (* [comment removed for export] *)
      change (Z_to_bv 64 E) with (wa E).
      st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. } clear K3.
      apply evt_done. unfold rrh2_post. do 3 eexists. unfold wa, E. reflexivity. }
    (* [comment removed for export] *)
    st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned, ?unsigned_lit in Kb by lia.
    - (* [comment removed for export] *)
      replace (Z_to_bv 64 rsv0) with (Z_to_bv 64 rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
      apply TAIL.
    - (* [comment removed for export] *)
      destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
      pose proof (bytes_at_read rsegs m _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
      change (drop (Z.to_nat 0) (le4 (wz r32))) with (le4 (wz r32)) in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
      replace (E - 4) with (S + stride + -8) in RD4 by (unfold E; lia).
      pose proof (bytes_at_read rsegs m _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5.
      change (take 1 (drop (Z.to_nat 0) [b8 0])) with [b8 0] in RD5. rewrite Z.add_0_r in RD5.
      replace (E - 5) with (S + stride + -9) in RD5 by (unfold E; lia).
      (* [comment removed for export] *)
      st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?unsigned_lit in K5 by lia. lia. } clear K5.
      (* [comment removed for export] *)
      st1. rewrite zx32_wz by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. } clear K6.
      (* [comment removed for export] *)
      st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. reflexivity. } clear K7.
      replace (wz r32) with (Z_to_bv 64 rsv) by (unfold rsv, wz; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
      apply TAIL. }
  (* [comment removed for export] *)
  st1. rewrite ?(wz_unsigned mword), MW12 by lia. st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  - (* [comment removed for export] *)
    specialize (SC48 ltac:(lia)). specialize (RS SC48).
    assert (STR : stride = 16 * size_class sc) by (unfold stride; rewrite (proj2 (Z.eqb_eq _ _) Km), andb_false_r; reflexivity).
    st1.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (68648 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (68648 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    pose proof (size_class_range sc ltac:(lia)) as SZ.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
    apply K2.
  - (* [comment removed for export] *)
    specialize (Hml ltac:(lia)).
    st1. st1. st1. if_cases K9; zify_cond K9.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2, ?wz_unsigned in K9 by lia. change (2^8) with 256 in K9.
        rewrite land_ones_small in K9 by lia. lia. }
    clear K9.
    st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit, ?MW1 in Kl by lia.
    + (* [comment removed for export] *)
      st1. st1. rewrite land_pgmask by lia. rewrite ?(wz_unsigned mword), MWP by lia. st1. st1.
      replace (Z_to_bv 64 (4096 * maplen + -16)) with (Z_to_bv 64 stride).
      2:{ unfold stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. lia. }
      apply K2.
    + (* [comment removed for export] *)
      specialize (SC48 ltac:(lia)). specialize (RS SC48).
      assert (STR : stride = 16 * size_class sc) by (unfold stride; rewrite (proj2 (Z.eqb_neq _ _) Kl); reflexivity).
      st1.
      assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (68648 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
      { replace (Z_to_bv 64 (68648 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
      pose proof (size_class_range sc ltac:(lia)) as SZ.
      st1. try rewrite (Z.mod_small (size_class sc)) by lia.
      st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
      replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
      apply K2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod16_of_region (b o : Z) : b mod 4096 = 0 -> o mod 16 = 0 -> (b + o) mod 16 = 0.
Proof. intros Hb Ho. rewrite Z.add_mod, Ho by lia. replace (b mod 16) with 0; [reflexivity|]. symmetry. Z.div_mod_to_equations. lia. Qed.

Definition rrhead_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (G P B b3 mword sc S stride rsv : Z) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 (S + stride - 4)) (Z_to_bv 64 S) t2
                  s0 (wz G) a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 68648) (Z_to_bv 64 (S + stride)) (Z_to_bv 64 (S + stride - 4 - P))
                  (Z_to_bv 64 (S + stride - 4 - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19358) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells rsegs m' (bv_unsigned sp + -64) (rre_frame s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rmrep st m'.

Lemma rrealloc_head : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (lo n : Z) st (p : aptr) r g gh ar (b3 lo8 hi r32 : Z),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo8 + 256 * hi in
  let idx := Z.land b3 31 in
  let base := aadd p (- (UNIT * off16) - UNIT) in
  let mr := get_meta_rec st g in
  let stride := get_stride mr in
  let S := conc st base + UNIT + stride * idx in
  let E := S + stride - IB in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  rmrep st m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
  a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
  cell_read sh (po - 2) = Known lo8 -> cell_read sh (po - 1) = Known hi ->
  (s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
  m_mem mr = Some base ->
  (s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
  0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
  (m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
  (48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
  (m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
  (m_maplen mr = 0 \/ m_last_idx mr <> 0 -> m_sizeclass mr < 48) ->
  UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at rsegs m (E - 4) (le4 (wz r32)) /\ bytes_at rsegs m (E - 5) [b8 0]) ->
  rsv <= E - (r_base r + po) -> bytes_at rsegs m (E - rsv) [b8 0] -> bytes_at rsegs m E [b8 0] ->
  evt rsegs (rrhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 t5 t6 F fc lo st m
               (conc st g) (r_base r + po) (conc st base) b3 (meta_word mr) (m_sizeclass mr) S stride rsv)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until r32. intros sh po off16 idx base mr stride S E rsv0 rsv MR MI ST LO SLO Hr Hk HP AL A1 N P16 PLO PHI C4 C3 C2 C1 Hgh Hg MSL G0 Hmem Har Hchk
         AV FRD SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48 S16 ELO EHI BIG RSVLE RB0r RE0.
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint1 _ _ RFr ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as DR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUs.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (mod16_of_region _ _ BAL AL) as PAL.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  (* [comment removed for export] *)
  destruct (WG base gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. clear Hrb.
  assert (HB : conc st base = (r_base r + po) - 16 * off16 - 16).
  { unfold base. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
  pose proof MSL as MSL0. destruct MSL as (a & ara & k & Ha & Hkk & Eg).
  destruct (WA a ara Ha) as (rg & Hrg & A0 & A1' & AAL & ANG & _).
  assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  destruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _).
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
  assert (GR : 0 <= conc st g /\ conc st g + 40 <= 2^64).
  { rewrite HG. unfold AREA_HDR, META_SIZE, NSLOTS, alloc_ceiling in *. pose proof (round_up_pg_ge (r_len rg)). lia. }
  clear Hm RBAL AAL BAL A1' Eg.
  destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [_ B3].
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  unfold rrealloc_entry, alloc_ceiling, UNIT, IB in *.
  (* [comment removed for export] *)
  pose proof (conj BIG (conj RB0r RE0)) as MEMF. clear BIG RB0r RE0.
  (* [comment removed for export] *)
  st1. if_cases K0; zify_cond K0. { exfalso. lia. } clear K0.
  carve_frame 64%nat ST.
  st1. st1. st1. st1. st1. st1. st1. st1. st1.
  st1. st1. st1. subst a1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. cbn in K1. lia. } clear K1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM |]; intros l h [E1|[]]; inversion E1; subst; unfold alloc_ceiling; lia) end.
  destruct (rmrep_shadow_read st _ (fst p) r (po - 4) 0 MR1 Hr Hk ltac:(lia) C4) as [R4 _].
  destruct (rmrep_shadow_read st _ (fst p) r (po - 3) b3 MR1 Hr Hk ltac:(lia) C3) as [R3 _].
  destruct (rmrep_shadow_read2 st _ (fst p) r (po - 2) lo8 hi MR1 Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1)) as (R2 & LO8 & HI).
  rewrite <- le2_lohi in R2 by lia. fold off16 in R2.
  destruct (rmrep_group_read st _ base gh MR1 Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.
  pose proof (rmrep_meta_chunk st _ g MR1 MSL0) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  pose proof (rmrep_area_check_read st _ (area_of g) ar MR1 Har) as RA. rewrite Hchk in RA.
  pose proof (rmrep_ctx_secret_read st _ MR1) as RC.
  assert (MW : mw_ok mr) by (unfold mw_ok; lia).
  eapply evt_cut.
  { eapply (rrealloc_h1_walk _ _ gp tp _ _ _ s0 _ a0 _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ t5 t6 F fc _
              (r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
              (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
              (pw st (m_prev mr)) (pw st (m_next mr)));
      first [exact HP | exact PAL | exact MM | exact RA | exact RC | exact Hav | exact Hfr | idtac]; try lia.
    - replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
    - replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
    - replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
    - exact RG.
    - intros Hlt. apply rsize_classes_read; [assumption | lia]. }
  cbv beta. intros ms1 (t3' & t4' & ->).
  change (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) with (meta_word mr).
  (* [comment removed for export] *)
  destruct MEMF as (BIG & RB0r & RE0).
  lazymatch type of MUs with munch ?W _ _ => assert (DJ : forall A kk, A + kk <= lo -> disjoint_from W A kk) by (intros A kk HA'; cbn; lia) end.
  eapply evt_mono.
  { eapply (rrealloc_h2_walk _ _ gp tp _ _ s0 a0 _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 _ F fc _
              (r_base r + po) (conc st base) b3 off16 (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) r32);
      first [exact HP | idtac]; try lia.
    all: change (if (m_last_idx mr =? 0) && negb (m_maplen mr =? 0) then m_maplen mr * 4096 - 16 else 16 * size_class (m_sizeclass mr))
           with stride.
    all: change (conc st base + 16 + stride * Z.land b3 31 + stride - 4) with E; try lia.
    - assumption.
    - intros Hlt. apply rsize_classes_read; [assumption | lia].
    - intros Hb3. destruct (BIG Hb3) as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|].
      split; (eapply bytes_at_transport; [eassumption| exact MUs| apply DJ; cbn; try rewrite length_le4; lia]).
    - fold rsv0. fold rsv. exact RSVLE.
    - fold rsv0. fold rsv. eapply bytes_at_transport; [exact RB0r| exact MUs| apply DJ; cbn; lia].
    - eapply bytes_at_transport; [exact RE0| exact MUs| apply DJ; cbn; lia]. }
  cbv beta. intros ms2 (t2' & t3'' & t4'' & ->).
  unfold rrhead_post. exists t2', t3'', t4''. eexists. split; [reflexivity|].
  split; [exact MUs|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR1].
Qed.
End RC__1.
