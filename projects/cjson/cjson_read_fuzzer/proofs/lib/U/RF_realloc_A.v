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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Export UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_free_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.



(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rrealloc_entry : Z := 0x17cd4.

(* [comment removed for export] *)
Definition rr_frame (ra s0 s1 s2 s3 s4 s5 s6 : word) : list cell :=
  [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition rr_hdr1_post (sp gp tp t1v s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (G B b3 off16 mword sc : Z) (ra s1 : word) : machine_state -> Prop :=
  fun ms' => exists t3 t4,
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 (Z.land b3 31)) (Z_to_bv 64 (Z.land mword 31)) (Z_to_bv 64 (sc * 2))
                  s0 (wz G) a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES) (wz off16) (wz b3)
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x17e20) fc None m (seg_rom usegs).

Lemma rr_hdr1_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
    (m : word -> option byte) (junk : list byte) (lo : Z)
    (P n G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret : Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 64 <= bv_unsigned sp ->
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> 0 <= n < 2^32 -> 0 < P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  (* [comment removed for export] *)
  alloc_ceiling <= lo -> P <= alloc_ceiling -> G + 40 <= alloc_ceiling -> A + 8 <= alloc_ceiling ->
  bytes_at usegs m (P - 4) ([b8 0; b8 b3] ++ le2 (wz off16)) ->
  bytes_at usegs m B (le8 (wz G)) ->
  rw_cells usegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  bytes_at usegs m A (le8 (wz secret)) ->
  bytes_at usegs m RCTX (le8 (wz secret)) ->
  mem_inv usegs m ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63) ->
  evt usegs (fun ms' => exists m', rr_hdr1_post sp gp tp t1 s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m' G B b3 off16 mword sc ra (wz G) ms'
                          /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                          /\ stk usegs m' lo (bv_unsigned sp + -64)
                          /\ rw_cells usegs m' (bv_unsigned sp + -64) (rr_frame ra s0 s1 s2 s3 s4 s5 s6))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom usegs)).
Proof using .
  intros until next. intros idx mword ST SLO SP64 HP HN N P0 AL PLO PHI HB HA GLO GHI CLO PC GC AC HDR RG MM RA RC MI
    B3 O16 AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  unfold alloc_ceiling, RCTX in *. unfold rrealloc_entry.
  (* [comment removed for export] *)
  st1. if_cases K0; zify_cond K0. { exfalso. rewrite HP in K0. lia. }
  (* [comment removed for export] *)
  carve_frame 64%nat ST.
  st1. st1. st1. st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. st1. st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. change 15 with (2^4 - 1) in K2. rewrite zb_land_mask in K2 by lia. lia. }
  (* [comment removed for export] *)
  pose proof (bytes_at_read usegs _ _ _ 0 1 HDR ltac:(lia) ltac:(cbn; lia)) as R4.
  pose proof (bytes_at_read usegs _ _ _ 1 1 HDR ltac:(lia) ltac:(cbn; lia)) as R3.
  pose proof (bytes_at_read usegs _ _ _ 2 2 HDR ltac:(lia) ltac:(cbn; lia)) as R2.
  change (Z.to_nat 0) with 0%nat in R4. change (Z.to_nat 1) with 1%nat in R3. change (Z.to_nat 2) with 2%nat in R2.
  cbn [take drop app] in R4, R3, R2. rewrite Z.add_0_r in R4. rewrite take_0 in R3. rewrite drop_0, take_ge in R2 by (rewrite length_le2; lia).
  replace (P - 4 + 1) with (P - 3) in R3 by lia. replace (P - 4 + 2) with (P - 2) in R2 by lia.
  rewrite <- HP in R4, R3, R2.
  (* [comment removed for export] *)
  st1. st1. st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. st1.
  pose proof (bytes_at_read usegs _ _ _ 0 8 RG ltac:(lia) ltac:(rewrite length_le8; lia)) as RG'.
  change (Z.to_nat 0) with 0%nat in RG'. rewrite drop_0, take_ge in RG' by (rewrite length_le8; lia).
  replace (B + 0) with (bv_unsigned a0 - off16 * 16 + -16) in RG' by lia.
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  st1. st1. st1. fold idx. st1. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite wz_unsigned in K4 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite MW1 in K5. lia. }
  (* [comment removed for export] *)
  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
  assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
  (* [comment removed for export] *)
  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. reflexivity. }
  (* [comment removed for export] *)
  pose proof (bytes_at_read usegs _ _ _ 0 8 RA ltac:(lia) ltac:(rewrite length_le8; lia)) as RA'.
  change (Z.to_nat 0) with 0%nat in RA'. rewrite drop_0, take_ge in RA' by (rewrite length_le8; lia). rewrite Z.add_0_r in RA'.
  pose proof (bytes_at_read usegs _ _ _ 0 8 RC ltac:(lia) ltac:(rewrite length_le8; lia)) as RC'.
  change (Z.to_nat 0) with 0%nat in RC'. rewrite drop_0, take_ge in RC' by (rewrite length_le8; lia). rewrite Z.add_0_r in RC'.
  st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. st1. st1.
  if_cases K8; zify_cond K8. 2:{ exfalso. rewrite ?wz_unsigned in K8 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  st1. st1. st1. st1. rewrite MW2. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1.
  if_cases K9; zify_cond K9.
  - (* [comment removed for export] *) specialize (Hsc63 ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia; lia)).
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by lia. lia. }
    apply evt_done. eexists. split; [| split; [exact MU| split; [exact WM| split; [exact MI| split; [exact ST| exact FR0]]]]].
    unfold rr_hdr1_post. do 2 eexists. rewrite GW. unfold RSIZE_CLASSES. reflexivity.
  - pose proof (rsize_classes_read _ sc MI ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia; lia)) as RS.
    specialize (Hsc ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia; lia)).
    assert (RS' : ov_read_bytes usegs m1 (Z_to_bv 64 (67704 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (67704 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    clear RS. pose proof (size_class_range sc ltac:(lia)) as SZ.
    (* [comment removed for export] *)
    st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
    st1. st1. if_cases K11; zify_cond K11. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    (* [comment removed for export] *)
    st1. st1. st1. if_cases K12; zify_cond K12. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K12 by nia. nia. }
    st1.
    apply evt_done. eexists. split; [| split; [exact MU| split; [exact WM| split; [exact MI| split; [exact ST| exact FR0]]]]].
    unfold rr_hdr1_post. do 2 eexists. rewrite GW. unfold RSIZE_CLASSES. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rr_hdr2_post (sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (G B mword sc stride E rsv : Z) (idx : Z) (ra gw : word) : machine_state -> Prop :=
  fun ms' => exists t3 t4,
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + stride * idx + 16)) (wz 0)
                  s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E + - bv_unsigned a0))
                  (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x17eb8) fc None m (seg_rom usegs).

(* [comment removed for export] *)
Lemma rr_hdr2_tail : forall ra sp gp tp t1v t2v t3v t4v s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 gw F fc
    (m : word -> option byte)
    (P G B : Z) (b3 mword sc stride r32 : Z),
  let idx := Z.land b3 31 in
  let E := B + 16 + stride * idx + stride - IB in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  bv_unsigned a0 = P -> 0 <= B -> 0 <= mword < 2^64 -> 0 <= sc < 64 ->
  UNIT <= stride -> stride < 2^52 -> P <= E -> E + 1 <= alloc_ceiling ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at usegs m (E - 4) (le4 (wz r32)) /\ bytes_at usegs m (E - 5) [b8 0]) ->
  rsv <= E - P -> bytes_at usegs m (E - rsv) [b8 0] -> bytes_at usegs m E [b8 0] ->
  mem_inv usegs m -> 0 <= b3 < 256 ->
  evt usegs (rr_hdr2_post sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m G B mword sc stride E rsv idx ra gw)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 idx) t1v t2v
               s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES) (Z_to_bv 64 stride) (wz b3)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4v t5 t6)
          F (Z_to_bv 64 0x17e48) fc None m (seg_rom usegs)).
Proof using .
  intros until r32. intros idx E rsv0 rsv HP B0 MWR SC S16 S52 PE EC FOOT RSV RB0r RE0 MI B3.
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  unfold alloc_ceiling, UNIT, IB in *.
  pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R.
  assert (SK : 0 <= stride * idx <= stride * 31) by nia.
  pose proof (bytes_at_read usegs m _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. change (Z.to_nat 0) with 0%nat in RDr. cbn [take drop] in RDr. rewrite Z.add_0_r in RDr.
  pose proof (bytes_at_read usegs m _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. change (Z.to_nat 0) with 0%nat in RDe. cbn [take drop] in RDe. rewrite Z.add_0_r in RDe.
  assert (R0R : 0 <= rsv0 < 8) by (subst rsv0; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; Z.div_mod_to_equations; lia).
  assert (R0S : b3 < 160 -> rsv0 < 5) by (intros; subst rsv0; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; Z.div_mod_to_equations; lia).
  assert (RSVR : 0 <= rsv < 2^32) by (subst rsv; destruct (Z.leb_spec 160 b3); [(nelim (FOOT ltac:(lia)) 3%nat; intros _ ? _); lia| lia]).
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. fold rsv0. st1.
  replace (B + stride * idx + 16 + stride + -4) with E by (subst E; lia).
  replace (B + stride * idx + 16 + stride) with (E + 4) by (subst E; lia).
  if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *)
    assert (RS5 : rsv = rsv0) by (subst rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
    specialize (R0S K1).
    (* [comment removed for export] *)
    st1. st1. if_cases K2; zify_cond K2.
    2:{ exfalso. try (change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones, Z.mod_small in K2 by lia).
        rewrite ?unsigned_lit in K2 by lia. clearbody rsv E idx rsv0. lia. }
    (* [comment removed for export] *)
    st1. rewrite <- RS5. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
    st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
    (* [comment removed for export] *)
    change (Z_to_bv 64 E) with (wa E).
    st1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. apply K4. reflexivity. }
    apply evt_done. unfold rr_hdr2_post. do 2 eexists. reflexivity.
  - (* [comment removed for export] *)
    (nelim (FOOT ltac:(lia)) 4%nat; intros R05 R32 RB4 RB5).
    assert (RS5 : rsv = r32) by (subst rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
    pose proof (bytes_at_read usegs m _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; lia)) as RD4.
    change (Z.to_nat 0) with 0%nat in RD4. rewrite drop_0, take_ge in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
    pose proof (bytes_at_read usegs m _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. change (Z.to_nat 0) with 0%nat in RD5. cbn [take drop] in RD5. rewrite Z.add_0_r in RD5.
    (* [comment removed for export] *)
    st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
    (* [comment removed for export] *)
    replace (E + 4 + -8) with (E - 4) by lia. change (Z_to_bv 64 (E - 4)) with (wa (E - 4)).
    st1. rewrite zx32_wz by lia. st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia. lia. }
    (* [comment removed for export] *)
    replace (E + 4 + -9) with (E - 5) by lia. change (Z_to_bv 64 (E - 5)) with (wa (E - 5)).
    st1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. apply K4. reflexivity. }
    (* [comment removed for export] *)
    st1. st1. if_cases K5; zify_cond K5.
    2:{ exfalso. try (change 18446744073709551615 with (Z.ones 64) in K5; rewrite Z.land_ones, Z.mod_small in K5 by lia).
        rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. clearbody rsv E idx rsv0. lia. }
    (* [comment removed for export] *)
    st1. rewrite <- RS5. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
    st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
    (* [comment removed for export] *)
    change (Z_to_bv 64 E) with (wa E).
    st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. reflexivity. }
    apply evt_done. unfold rr_hdr2_post. do 2 eexists. reflexivity.
Qed.


Lemma rr_hdr2_walk : forall ra sp gp tp t3v t4v s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 gw F fc
    (m : word -> option byte)
    (P G B : Z) (b3 off16 last_idx freeable sc maplen r32 : Z),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let stride := if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - UNIT else UNIT * size_class sc in
  let E := B + 16 + stride * idx + stride - IB in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  bv_unsigned a0 = P -> 0 <= B ->
  P <= E -> E + 1 <= alloc_ceiling ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at usegs m (E - 4) (le4 (wz r32)) /\ bytes_at usegs m (E - 5) [b8 0]) ->
  rsv <= E - P -> bytes_at usegs m (E - rsv) [b8 0] -> bytes_at usegs m E [b8 0] ->
  mem_inv usegs m ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  evt usegs (rr_hdr2_post sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m G B mword sc stride E rsv idx ra gw)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 idx) (Z_to_bv 64 (Z.land mword 31)) (Z_to_bv 64 (sc * 2))
               s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES) (wz off16) (wz b3)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4v t5 t6)
          F (Z_to_bv 64 0x17e20) fc None m (seg_rom usegs)).
Proof using .
  intros until r32. intros idx mword stride E rsv0 rsv HP B0 PE EC FOOT RSV RB0r RE0 MI B3 O16 LI FB SC ML Hidx Hml Hsc48.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (MW4 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (MWP : mword - mword mod 4096 = 4096 * maplen).
  { subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. lia. }
  assert (S16 : UNIT <= stride).
  { subst stride. destruct ((last_idx =? 0) && negb (maplen =? 0)) eqn:Eb.
    - apply andb_prop in Eb as [E1 E2]. destruct (Z.eqb_spec maplen 0); [discriminate|]. unfold UNIT. lia.
    - assert (SCS : sc < 48).
      { apply Hsc48. destruct (Z.eqb_spec maplen 0); [left; assumption|]. destruct (Z.eqb_spec last_idx 0); [cbn in Eb; discriminate| right; assumption]. }
      pose proof (size_class_range sc ltac:(lia)). unfold UNIT. lia. }
  assert (S52 : stride < 2^52).
  { subst stride. destruct ((last_idx =? 0) && negb (maplen =? 0)) eqn:Eb; [unfold UNIT; lia|].
    assert (SCS : sc < 48).
    { apply Hsc48. destruct (Z.eqb_spec maplen 0); [left; assumption|]. destruct (Z.eqb_spec last_idx 0); [cbn in Eb; discriminate| right; assumption]. }
    pose proof (size_class_range sc ltac:(lia)). unfold UNIT. lia. }
  pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R.
  unfold alloc_ceiling, IB in EC, PE, E. rewrite MW1.
  (* [comment removed for export] *)
  st1. rewrite MW4. st1. if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *)
    assert (SCS : sc < 48) by (apply Hsc48; left; exact K1).
    assert (STR : stride = 16 * size_class sc).
    { subst stride. replace (maplen =? 0) with true by (symmetry; apply Z.eqb_eq; exact K1). rewrite andb_false_r. unfold UNIT. lia. }
    pose proof (rsize_classes_read _ sc MI ltac:(lia)) as RS.
    assert (RS' : ov_read_bytes usegs m (Z_to_bv 64 (67704 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (67704 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    clear RS. pose proof (size_class_range sc ltac:(lia)) as SZ.
    (* [comment removed for export] *)
    st1. unfold RSIZE_CLASSES. st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
    rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (size_class sc * 16) with stride by lia. fold RSIZE_CLASSES. change 67704 with RSIZE_CLASSES.
    eapply rr_hdr2_tail; eauto; unfold alloc_ceiling, IB; try lia.
  - (* [comment removed for export] *)
    specialize (Hml K1).
    st1. st1. st1. if_cases K2; zify_cond K2.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2.
        try (change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones in K2 by lia).
        rewrite ?wz_unsigned, ?unsigned_lit, ?Z.mod_small in K2 by lia. lia. }
    (* [comment removed for export] *)
    st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    + (* [comment removed for export] *)
      assert (STR : stride = maplen * 4096 - 16).
      { subst stride. replace (last_idx =? 0) with true by (symmetry; apply Z.eqb_eq; exact K3).
        replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; exact K1). cbn. unfold UNIT. lia. }
      st1. st1. rewrite land_pgmask by lia. rewrite MWP. st1. st1.
      replace (4096 * maplen + -16) with stride by lia.
      eapply rr_hdr2_tail; eauto; unfold alloc_ceiling, IB; try lia.
    + (* [comment removed for export] *)
      assert (SCS : sc < 48) by (apply Hsc48; right; exact K3).
      assert (STR : stride = 16 * size_class sc).
      { subst stride. replace (last_idx =? 0) with false by (symmetry; apply Z.eqb_neq; exact K3). cbn. unfold UNIT. lia. }
      pose proof (rsize_classes_read _ sc MI ltac:(lia)) as RS.
      assert (RS' : ov_read_bytes usegs m (Z_to_bv 64 (67704 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
      { replace (Z_to_bv 64 (67704 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
      clear RS. pose proof (size_class_range sc ltac:(lia)) as SZ.
      st1. unfold RSIZE_CLASSES. st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
      rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
      replace (size_class sc * 16) with stride by lia. change 67704 with RSIZE_CLASSES.
      eapply rr_hdr2_tail; eauto; unfold alloc_ceiling, IB; try lia.
Qed.


End CeilWrap.
