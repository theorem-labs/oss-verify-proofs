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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import F_malloc_free F_malloc_fast MallocKit_B3.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import RMallocRep RMallocTree RMallocKit_B RF_get_meta.
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
Definition rre_pro_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a2 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b7d28) fc None m' (seg_rom usegs)
    /\ rw_cells usegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk usegs m' lo (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Lemma rre_pro_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo P n : Z),
  bv_unsigned a0 = P -> 0 < P -> a1 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
  stk usegs m lo (bv_unsigned sp) -> 0x358000 <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv usegs m ->
  evt usegs (rre_pro_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b7cd0) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until n. intros HP P0 HA N ST ILO LO MI. subst a1.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold MMAP_THRESHOLD in N.
  step. if_cases K0; zify_cond K0. { exfalso. lia. }
  carve_frame 64%nat ST. step. step. step. step. step. step. step. step. step.
  step. step. step.
  step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  apply evt_done. unfold rre_pro_post. do 2 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| eassumption].
Qed.
(* [comment removed for export] *)
Definition rre_meta_post (ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 gw : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (B idx lidx mword b3 sc stride : Z) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4,
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 lidx) t2 s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES)
                  (Z_to_bv 64 stride) (wz b3) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b7e44) fc None m (seg_rom usegs).

Lemma rre_meta_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret stride : Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
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
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  stride = (if negb (maplen =? 0) && (last_idx =? 0) then 4096 * maplen - 16 else 16 * size_class sc) ->
  evt usegs (rre_meta_post ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (wz G) F fc m B idx last_idx mword b3 sc stride)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b7d28) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml SC48 STR.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  (* [comment removed for export] *)
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  rewrite ?HP. st1. rewrite ?HP.
  (* [comment removed for export] *)
  assert (RG' : ov_read_bytes usegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }
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
  st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  st1. st1. st1. st1. rewrite MW2. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1.
  assert (MW12 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (MWP : mword - mword mod 4096 = 4096 * maplen).
  { subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. lia. }
  (* [comment removed for export] *)
  assert (KAC : forall t3v t4v, evt usegs (rre_meta_post ra sp gp tp s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 gw F fc m B idx last_idx mword b3 sc stride)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 467704)
               (wz off16) (wz b3) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4v t5 t6)
          F (Z_to_bv 64 0x2b7e1c) fc None m (seg_rom usegs))).
  { intros t3v t4v.
    (* [comment removed for export] *)
    st1. rewrite MW12. st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
    - (* [comment removed for export] *)
      specialize (SC48 ltac:(left; exact Km)). specialize (RS SC48).
      st1. replace (467704 + sc * 2) with (467704 + 2 * sc) by lia.
      assert (RS' : ov_read_bytes usegs m (Z_to_bv 64 (467704 + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))).
      { replace (Z_to_bv 64 (467704 + 2 * sc)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
      pose proof (size_class_range sc ltac:(lia)) as SZ.
      st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
      replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (f_equal; rewrite STR, (proj2 (Z.eqb_eq _ _) Km); cbn [negb andb]; lia).
      apply evt_done. unfold rre_meta_post. do 3 eexists. rewrite GW. unfold RSIZE_CLASSES. reflexivity.
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
        apply evt_done. unfold rre_meta_post. do 3 eexists. rewrite GW. unfold RSIZE_CLASSES. reflexivity.
      + (* [comment removed for export] *)
        specialize (SC48 ltac:(right; exact Kl)). specialize (RS SC48).
        st1. replace (467704 + sc * 2) with (467704 + 2 * sc) by lia.
        assert (RS' : ov_read_bytes usegs m (Z_to_bv 64 (467704 + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))).
        { replace (Z_to_bv 64 (467704 + 2 * sc)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
        pose proof (size_class_range sc ltac:(lia)) as SZ.
        st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
        replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride).
        2:{ f_equal. rewrite STR. replace (last_idx =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite andb_false_r. lia. }
        apply evt_done. unfold rre_meta_post. do 3 eexists. rewrite GW. unfold RSIZE_CLASSES. reflexivity. }
  st1. if_cases K8; zify_cond K8.
  - (* [comment removed for export] *) specialize (Hsc63 ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
    apply KAC.
  - specialize (RS ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)). specialize (Hsc ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).
    (* [comment removed for export] *)
    st1. replace (467704 + sc * 2) with (467704 + 2 * sc) by lia.
    assert (RS' : ov_read_bytes usegs m (Z_to_bv 64 (467704 + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (467704 + 2 * sc)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    (* [comment removed for export] *)
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. apply KAC.
Qed.
End HCW.
