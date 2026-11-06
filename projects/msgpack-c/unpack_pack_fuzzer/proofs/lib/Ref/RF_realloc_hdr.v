(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_malloc_free A_F_malloc_fast A_MallocKit_AB A_MallocBlocks A_MallocHINV A_MallocFacts_B A_Malloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl MallocInv MI_Inv MI_Read MI_Geom MI_Pres2 MI_WFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP RF_get_meta RF_malloc_top RMemEq.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require A_MallocFacts_inv A_MallocFacts_inv2.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RF_aligned16_W.

Set Keyed Unification.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma zx32_wz' x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. intros. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Section HDR.
Variables (ra1 sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (P n old G B AREA stride : Z) (i res off16 avail freed last_idx freeable sc maplen secret : Z) (prev next : word).
Let b3 := i + 32 * Z.min res 5.
Let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen.
Let E := B + 16 + stride * (i + 1) - 4.

Definition hdr_post : machine_state -> Prop :=
  fun ms' => exists y7 y28 y29,
    ms' = MS (mkR ra1 sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + stride * i + 16)) y7 s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n)
                  (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 87200) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
                  (Z_to_bv 64 (P + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
             F (Z_to_bv 64 0x49bf4) fc None m (seg_rom rsegs).
Hypotheses (HN : 0 <= n < 2^48) (HO : 0 <= old)
  (P0 : 0 < P) (AL : P mod 16 = 0) (PLO : 16 * off16 + 16 <= P) (PHI : P + 16 <= 2^64)
  (HB : B = P - 16 * off16 - 16) (HAREA : AREA = G - G mod 4096) (GLO : 0 <= G) (GHI : G + 40 <= 2^64)
  (R4 : ov_read_bytes rsegs m (wa (P - 4)) 1 = Some [b8 0])
  (R3 : ov_read_bytes rsegs m (wa (P - 3)) 1 = Some [b8 b3])
  (R2 : ov_read_bytes rsegs m (wa (P - 2)) 2 = Some (le2 (wz off16)))
  (RG : ov_read_bytes rsegs m (wa B) 8 = Some (le8 (wz G)))
  (MM : rw_cells rsegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)])
  (RA : ov_read_bytes rsegs m (wa AREA) 8 = Some (le8 (wz secret)))
  (RC : ov_read_bytes rsegs m (wa RCTX) 8 = Some (le8 (wz secret)))
  (RS : sc < 48 -> ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc))))
  (IR : 0 <= i < 32) (O16 : 0 <= off16 < 65536) (AV : 0 <= avail < 2^32) (FRD : 0 <= freed < 2^32) (SE : 0 <= secret < 2^64)
  (LI : 0 <= last_idx < 32) (FB : 0 <= freeable < 2) (SC : 0 <= sc < 64) (ML : 0 <= maplen < 2^40)
  (Hidx : i <= last_idx) (Hav : Z.testbit avail i = false) (Hfr : Z.testbit freed i = false)
  (Hsc : sc < 48 -> size_class sc * i <= off16 < size_class sc * (i + 1))
  (Hsc63 : 48 <= sc -> sc = 63)
  (Hml : maplen <> 0 -> off16 <= maplen * 256 - 1)
  (STR1 : maplen = 0 \/ last_idx <> 0 -> sc < 48 /\ stride = 16 * size_class sc)
  (STR2 : last_idx = 0 /\ maplen <> 0 -> stride = maplen * 4096 - 16)
  (RES : 0 <= res < 2^32) (RESE : res = E - P - old) (HEAPR : E + 1 <= 0x10000 \/ 0x88000 <= P - 4) (EHI : E + 1 <= 2^64)
  (RB0 : 0 < res -> ov_read_bytes rsegs m (wa (E - res)) 1 = Some [b8 0])
  (RB5 : 5 <= res -> ov_read_bytes rsegs m (wa (E - 5)) 1 = Some [b8 0] /\ ov_read_bytes rsegs m (wa (E - 4)) 4 = Some (le4 (wz res)))
  (RE0 : ov_read_bytes rsegs m (wa E) 1 = Some [b8 0]).

Lemma hdr_544 : forall (y7 y28 y29 : word),
  evt rsegs hdr_post
      (MS (mkR ra1 sp gp tp (Z_to_bv 64 i) (Z_to_bv 64 last_idx) y7 s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n)
                (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 87200) (Z_to_bv 64 stride) (wz b3)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
          F (Z_to_bv 64 0x49b84) fc None m (seg_rom rsegs)).
Proof.
  intros.
  assert (B3R : 0 <= b3 < 256) by (subst b3; lia).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (shr5 : Z.shiftr b3 5 = Z.min res 5).
  { subst b3. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. lia. }

  assert (K58 : forall a7v t3v,
    evt rsegs hdr_post
      (MS (mkR ra1 sp gp tp (Z_to_bv 64 (B + stride * i + 16 + stride + -4)) (Z_to_bv 64 (B + stride * i + 16)) (Z_to_bv 64 res) s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n)
                (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 87200) (Z_to_bv 64 (B + stride * i + 16 + stride)) a7v
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v y29 t5 t6)
          F (Z_to_bv 64 0x49bcc) fc None m (seg_rom rsegs))).
  { intros a7v t3v.

    st1. st1. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia. 2:{ exfalso. lia. }

    st1.
    assert (RBX : ov_read_bytes rsegs m (Z_to_bv 64 (B + stride * i + 16 + stride + -4 - res)) 1 = Some [b8 0]).
    { destruct (Z.eq_dec res 0) as [R0|R0].
      - rewrite R0, Z.sub_0_r. replace (B + stride * i + 16 + stride + -4) with E by (subst E; lia). exact RE0.
      - replace (B + stride * i + 16 + stride + -4 - res) with (E - res) by (subst E; lia). apply RB0. lia. }
    st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }

    assert (REX : ov_read_bytes rsegs m (Z_to_bv 64 (B + stride * i + 16 + stride + -4)) 1 = Some [b8 0]).
    { replace (B + stride * i + 16 + stride + -4) with E by (subst E; lia). exact RE0. }
    st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
    replace (Z_to_bv 64 (B + stride * i + 16 + stride + -4 + - res)) with (Z_to_bv 64 (P + old)) by (f_equal; subst E; lia).
    replace (Z_to_bv 64 (B + stride * i + 16 + stride + -4)) with (Z_to_bv 64 E) by (f_equal; subst E; lia).
    replace (Z_to_bv 64 (B + stride * i + 16 + stride)) with (Z_to_bv 64 (E + 4)) by (f_equal; subst E; lia).
    replace (Z_to_bv 64 (B + stride * i + 16 + stride + -4 - P)) with (Z_to_bv 64 (E - P)) by (f_equal; subst E; lia).
    apply evt_done. unfold hdr_post. exists (Z_to_bv 64 0). eexists. eexists. Show. reflexivity. }

  st1. st1. st1. st1. st1. st1. st1. st1. if_cases K0; zify_cond K0; rewrite ?wz_unsigned, ?unsigned_lit in K0 by lia.
  -   rewrite shr5. replace (Z.min res 5) with res by lia. apply K58.
  -
    rewrite shr5. replace (Z.min res 5) with 5 by lia. destruct (RB5 ltac:(lia)) as [RB5a RB5b].
    st1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }

    assert (RB5b' : ov_read_bytes rsegs m (Z_to_bv 64 (B + stride * i + 16 + stride + -8)) 4 = Some (le4 (wz res))).
    { replace (B + stride * i + 16 + stride + -8) with (E - 4) by (unfold E; lia). exact RB5b. }
    st1. rewrite zx32_wz' by lia. st1. st1. if_cases K5; zify_cond K5; rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. 2:{ exfalso. lia. }

    assert (RB5a' : ov_read_bytes rsegs m (Z_to_bv 64 (B + stride * i + 16 + stride + -9)) 1 = Some [b8 0]).
    { replace (B + stride * i + 16 + stride + -9) with (E - 5) by (unfold E; lia). exact RB5a. }
    st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
    apply K58.
Qed.

Lemma hdr_51c : forall (y28 y29 : word),
  evt rsegs hdr_post
      (MS (mkR ra1 sp gp tp (Z_to_bv 64 i) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n)
                (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 87200) (wz off16) (wz b3)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
          F (Z_to_bv 64 0x49b5c) fc None m (seg_rom rsegs)).
Proof.
  intros.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW4 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  pose proof hdr_544 as K. cbv delta [mkR] in K.

  st1. rewrite ?wz_unsigned, MW4 by lia. st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  -
    destruct (STR1 ltac:(lia)) as [SC48 STR].
    st1.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (87200 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (87200 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). apply RS. lia. }
    pose proof (size_class_range sc ltac:(lia)) as SZ.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
    rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (f_equal; lia).
    apply K.
  -
    specialize (Hml ltac:(lia)).
    st1. st1. st1. if_cases K2; zify_cond K2.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
        rewrite Z.land_ones, ?wz_unsigned, ?unsigned_lit in K2 by lia. rewrite Z.mod_small in K2 by lia. lia. }

    st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    +
      pose proof (STR2 ltac:(lia)) as STR.
      assert (MWP : mword - mword mod 4096 = 4096 * maplen).
      { unfold mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
        rewrite Z.mod_add, Z.mod_small by lia. lia. }
      st1. st1. rewrite ?wz_unsigned, land_pgmask by lia. rewrite MWP. st1. st1.
      replace (Z_to_bv 64 (4096 * maplen + -16)) with (Z_to_bv 64 stride) by (f_equal; lia).
      apply K.
    +
      destruct (STR1 ltac:(lia)) as [SC48 STR].
      st1.
      assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (87200 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
      { replace (Z_to_bv 64 (87200 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). apply RS. lia. }
      pose proof (size_class_range sc ltac:(lia)) as SZ.
      st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
      rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
      replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (f_equal; lia).
      apply K.
Qed.

Lemma hdr_428 : forall (y7 y12 y13 y14 y15 y16 y17 y28 y29 : word),
  evt rsegs hdr_post
      (MS (mkR ra1 sp gp tp t0 t1 y7 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) y12 y13 y14 y15 y16 y17
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
          F (Z_to_bv 64 0x49a68) fc None m (seg_rom rsegs)).
Proof.
  intros.
  assert (MWR : 0 <= mword < 2^64) by (unfold mword; lia).
  assert (B3R : 0 <= b3 < 256) by (unfold b3; lia).
  assert (IDX : Z.land b3 31 = i) by (unfold b3; apply land_idx_code; lia).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof hdr_51c as KB. cbv delta [mkR] in KB.

  st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. change 15 with (2^4 - 1) in K1. rewrite zb_land_mask in K1 by lia. rewrite ?unsigned_lit in K1 by lia. lia. }

  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }

  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).

  st1. st1. st1. rewrite IDX. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }

  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. unfold mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }

  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite ?unsigned_lit by lia. rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ i < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ i)) as SXI.
  assert (LA : Z.land avail (2 ^ i) = 0) by (apply (proj2 (land_pow2_testbit avail i ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ i) = 0) by (apply (proj2 (land_pow2_testbit freed i ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }

  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }

  st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HAREA. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  clear K1 K2 K3 K4 K5 K6 K7.

  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  st1. st1. st1. st1. rewrite MW2. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1.
  if_cases K8; zify_cond K8; rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia.
  -
    specialize (Hsc63 ltac:(lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
    apply KB.
  -
    specialize (RS ltac:(lia)). specialize (Hsc ltac:(lia)).
    st1.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (87200 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (87200 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. apply KB.
Qed.
End HDR.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_fast OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_AB OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_B OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocInv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Read OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Geom OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Pres2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_WFree.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog.
Import RMallocRep.TwinB RMallocTree.TwinB RMallocKit_B.TwinB RMalloc_iface.TwinB RMalloc_ifaceP.TwinB RF_get_meta.TwinB RF_malloc_top.TwinB RMemEq.TwinB.

Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import RF_aligned16_W.TwinB.

Set Keyed Unification.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma zx32_wz' x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. intros. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Section HDR.
Variables (ra1 sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (P n old G B AREA stride : Z) (i res off16 avail freed last_idx freeable sc maplen secret : Z) (prev next : word).
Let b3 := i + 32 * Z.min res 5.
Let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen.
Let E := B + 16 + stride * (i + 1) - 4.

Definition hdr_post : machine_state -> Prop :=
  fun ms' => exists y7 y28 y29,
    ms' = MS (mkR ra1 sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + stride * i + 16)) y7 s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n)
                  (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 87344) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
                  (Z_to_bv 64 (P + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
             F (Z_to_bv 64 0x4b3f8) fc None m (seg_rom rsegs).
Hypotheses (HN : 0 <= n < 2^48) (HO : 0 <= old)
  (P0 : 0 < P) (AL : P mod 16 = 0) (PLO : 16 * off16 + 16 <= P) (PHI : P + 16 <= 2^64)
  (HB : B = P - 16 * off16 - 16) (HAREA : AREA = G - G mod 4096) (GLO : 0 <= G) (GHI : G + 40 <= 2^64)
  (R4 : ov_read_bytes rsegs m (wa (P - 4)) 1 = Some [b8 0])
  (R3 : ov_read_bytes rsegs m (wa (P - 3)) 1 = Some [b8 b3])
  (R2 : ov_read_bytes rsegs m (wa (P - 2)) 2 = Some (le2 (wz off16)))
  (RG : ov_read_bytes rsegs m (wa B) 8 = Some (le8 (wz G)))
  (MM : rw_cells rsegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)])
  (RA : ov_read_bytes rsegs m (wa AREA) 8 = Some (le8 (wz secret)))
  (RC : ov_read_bytes rsegs m (wa RCTX) 8 = Some (le8 (wz secret)))
  (RS : sc < 48 -> ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc))))
  (IR : 0 <= i < 32) (O16 : 0 <= off16 < 65536) (AV : 0 <= avail < 2^32) (FRD : 0 <= freed < 2^32) (SE : 0 <= secret < 2^64)
  (LI : 0 <= last_idx < 32) (FB : 0 <= freeable < 2) (SC : 0 <= sc < 64) (ML : 0 <= maplen < 2^40)
  (Hidx : i <= last_idx) (Hav : Z.testbit avail i = false) (Hfr : Z.testbit freed i = false)
  (Hsc : sc < 48 -> size_class sc * i <= off16 < size_class sc * (i + 1))
  (Hsc63 : 48 <= sc -> sc = 63)
  (Hml : maplen <> 0 -> off16 <= maplen * 256 - 1)
  (STR1 : maplen = 0 \/ last_idx <> 0 -> sc < 48 /\ stride = 16 * size_class sc)
  (STR2 : last_idx = 0 /\ maplen <> 0 -> stride = maplen * 4096 - 16)
  (RES : 0 <= res < 2^32) (RESE : res = E - P - old) (HEAPR : E + 1 <= 0x10000 \/ 0x8a000 <= P - 4) (EHI : E + 1 <= 2^64)
  (RB0 : 0 < res -> ov_read_bytes rsegs m (wa (E - res)) 1 = Some [b8 0])
  (RB5 : 5 <= res -> ov_read_bytes rsegs m (wa (E - 5)) 1 = Some [b8 0] /\ ov_read_bytes rsegs m (wa (E - 4)) 4 = Some (le4 (wz res)))
  (RE0 : ov_read_bytes rsegs m (wa E) 1 = Some [b8 0]).

Lemma hdr_544 : forall (y7 y28 y29 : word),
  evt rsegs hdr_post
      (MS (mkR ra1 sp gp tp (Z_to_bv 64 i) (Z_to_bv 64 last_idx) y7 s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n)
                (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 87344) (Z_to_bv 64 stride) (wz b3)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
          F (Z_to_bv 64 0x4b388) fc None m (seg_rom rsegs)).
Proof.
  intros.
  assert (B3R : 0 <= b3 < 256) by (subst b3; lia).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (shr5 : Z.shiftr b3 5 = Z.min res 5).
  { subst b3. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. lia. }

  assert (K58 : forall a7v t3v,
    evt rsegs hdr_post
      (MS (mkR ra1 sp gp tp (Z_to_bv 64 (B + stride * i + 16 + stride + -4)) (Z_to_bv 64 (B + stride * i + 16)) (Z_to_bv 64 res) s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n)
                (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 87344) (Z_to_bv 64 (B + stride * i + 16 + stride)) a7v
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v y29 t5 t6)
          F (Z_to_bv 64 0x4b3d0) fc None m (seg_rom rsegs))).
  { intros a7v t3v.

    st1. st1. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia. 2:{ exfalso. lia. }

    st1.
    assert (RBX : ov_read_bytes rsegs m (Z_to_bv 64 (B + stride * i + 16 + stride + -4 - res)) 1 = Some [b8 0]).
    { destruct (Z.eq_dec res 0) as [R0|R0].
      - rewrite R0, Z.sub_0_r. replace (B + stride * i + 16 + stride + -4) with E by (subst E; lia). exact RE0.
      - replace (B + stride * i + 16 + stride + -4 - res) with (E - res) by (subst E; lia). apply RB0. lia. }
    st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }

    assert (REX : ov_read_bytes rsegs m (Z_to_bv 64 (B + stride * i + 16 + stride + -4)) 1 = Some [b8 0]).
    { replace (B + stride * i + 16 + stride + -4) with E by (subst E; lia). exact RE0. }
    st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
    replace (Z_to_bv 64 (B + stride * i + 16 + stride + -4 + - res)) with (Z_to_bv 64 (P + old)) by (f_equal; subst E; lia).
    replace (Z_to_bv 64 (B + stride * i + 16 + stride + -4)) with (Z_to_bv 64 E) by (f_equal; subst E; lia).
    replace (Z_to_bv 64 (B + stride * i + 16 + stride)) with (Z_to_bv 64 (E + 4)) by (f_equal; subst E; lia).
    replace (Z_to_bv 64 (B + stride * i + 16 + stride + -4 - P)) with (Z_to_bv 64 (E - P)) by (f_equal; subst E; lia).
    apply evt_done. unfold hdr_post. exists (Z_to_bv 64 0). eexists. eexists. Show. reflexivity. }

  st1. st1. st1. st1. st1. st1. st1. st1. if_cases K0; zify_cond K0; rewrite ?wz_unsigned, ?unsigned_lit in K0 by lia.
  -   rewrite shr5. replace (Z.min res 5) with res by lia. apply K58.
  -
    rewrite shr5. replace (Z.min res 5) with 5 by lia. destruct (RB5 ltac:(lia)) as [RB5a RB5b].
    st1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }

    assert (RB5b' : ov_read_bytes rsegs m (Z_to_bv 64 (B + stride * i + 16 + stride + -8)) 4 = Some (le4 (wz res))).
    { replace (B + stride * i + 16 + stride + -8) with (E - 4) by (unfold E; lia). exact RB5b. }
    st1. rewrite zx32_wz' by lia. st1. st1. if_cases K5; zify_cond K5; rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. 2:{ exfalso. lia. }

    assert (RB5a' : ov_read_bytes rsegs m (Z_to_bv 64 (B + stride * i + 16 + stride + -9)) 1 = Some [b8 0]).
    { replace (B + stride * i + 16 + stride + -9) with (E - 5) by (unfold E; lia). exact RB5a. }
    st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
    apply K58.
Qed.

Lemma hdr_51c : forall (y28 y29 : word),
  evt rsegs hdr_post
      (MS (mkR ra1 sp gp tp (Z_to_bv 64 i) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n)
                (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 87344) (wz off16) (wz b3)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
          F (Z_to_bv 64 0x4b360) fc None m (seg_rom rsegs)).
Proof.
  intros.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW4 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  pose proof hdr_544 as K. cbv delta [mkR] in K.

  st1. rewrite ?wz_unsigned, MW4 by lia. st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  -
    destruct (STR1 ltac:(lia)) as [SC48 STR].
    st1.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (87344 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (87344 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). apply RS. lia. }
    pose proof (size_class_range sc ltac:(lia)) as SZ.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
    rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (f_equal; lia).
    apply K.
  -
    specialize (Hml ltac:(lia)).
    st1. st1. st1. if_cases K2; zify_cond K2.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
        rewrite Z.land_ones, ?wz_unsigned, ?unsigned_lit in K2 by lia. rewrite Z.mod_small in K2 by lia. lia. }

    st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    +
      pose proof (STR2 ltac:(lia)) as STR.
      assert (MWP : mword - mword mod 4096 = 4096 * maplen).
      { unfold mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
        rewrite Z.mod_add, Z.mod_small by lia. lia. }
      st1. st1. rewrite ?wz_unsigned, land_pgmask by lia. rewrite MWP. st1. st1.
      replace (Z_to_bv 64 (4096 * maplen + -16)) with (Z_to_bv 64 stride) by (f_equal; lia).
      apply K.
    +
      destruct (STR1 ltac:(lia)) as [SC48 STR].
      st1.
      assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (87344 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
      { replace (Z_to_bv 64 (87344 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). apply RS. lia. }
      pose proof (size_class_range sc ltac:(lia)) as SZ.
      st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
      rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
      replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (f_equal; lia).
      apply K.
Qed.

Lemma hdr_428 : forall (y7 y12 y13 y14 y15 y16 y17 y28 y29 : word),
  evt rsegs hdr_post
      (MS (mkR ra1 sp gp tp t0 t1 y7 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) y12 y13 y14 y15 y16 y17
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
          F (Z_to_bv 64 0x4b26c) fc None m (seg_rom rsegs)).
Proof.
  intros.
  assert (MWR : 0 <= mword < 2^64) by (unfold mword; lia).
  assert (B3R : 0 <= b3 < 256) by (unfold b3; lia).
  assert (IDX : Z.land b3 31 = i) by (unfold b3; apply land_idx_code; lia).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof hdr_51c as KB. cbv delta [mkR] in KB.

  st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. change 15 with (2^4 - 1) in K1. rewrite zb_land_mask in K1 by lia. rewrite ?unsigned_lit in K1 by lia. lia. }

  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }

  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).

  st1. st1. st1. rewrite IDX. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }

  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. unfold mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }

  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite ?unsigned_lit by lia. rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ i < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ i)) as SXI.
  assert (LA : Z.land avail (2 ^ i) = 0) by (apply (proj2 (land_pow2_testbit avail i ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ i) = 0) by (apply (proj2 (land_pow2_testbit freed i ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }

  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }

  st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HAREA. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  clear K1 K2 K3 K4 K5 K6 K7.

  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  st1. st1. st1. st1. rewrite MW2. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1.
  if_cases K8; zify_cond K8; rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia.
  -
    specialize (Hsc63 ltac:(lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
    apply KB.
  -
    specialize (RS ltac:(lia)). specialize (Hsc ltac:(lia)).
    st1.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (87344 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (87344 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. apply KB.
Qed.
End HDR.

End CEIL.
End TwinB.
