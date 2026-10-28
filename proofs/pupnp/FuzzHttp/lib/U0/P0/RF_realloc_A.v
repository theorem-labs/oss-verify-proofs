(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_malloc_free F_malloc_fast F_free_A.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta RF_free_A.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := ceil_facts; unfold UNIT, IB in *; lia.

Definition rrealloc_sym : Z := 0x1995c.

Definition rr_frame (s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition rr0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0x7fffffffffffefff) a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x199b8) fc None m' (seg_rom rsegs)
    /\ rw_cells rsegs m' (bv_unsigned sp + -64) (rr_frame s6 s5 s4 s3 s2 s1 s0 ra)
    /\ stk rsegs m' lo (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma rrealloc_A0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo P n : Z),
  a0 = Z_to_bv 64 P -> 0 < P < 2^64 -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  stk rsegs m lo (bv_unsigned sp) -> 0x5d000 <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv rsegs m ->
  evt rsegs (rr0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rrealloc_sym) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros HA HP HN N ST ILO LO MI. subst a0 a1.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold rrealloc_sym.
  step. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  carve_frame 64%nat ST.
  step. step. step. step. step. step. step. step. step.
  step. step. step.
  step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  apply evt_done. unfold rr0_post, rr_frame. eexists. split; [reflexivity|].
  split; [assumption|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.

Definition rr1_post (ra sp gp tp t5 t6 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (gw : word) (B sc mword off16 b3 last_idx : Z) : machine_state -> Prop :=
  fun ms' => exists t3 t4,
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (Z.land b3 31)) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 gw a0 a1
                  (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES) (wz off16) (wz b3)
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19aac) fc None m (seg_rom rsegs).

Lemma rrealloc_A1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret: Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  mem_inv rsegs m ->
  ov_read_bytes rsegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes rsegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes rsegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes rsegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells rsegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes rsegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes rsegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 -> 0 <= B ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63) ->
  evt rsegs (rr1_post ra sp gp tp t5 t6 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (wz G) B sc mword off16 b3 last_idx)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x199b8) fc None m (seg_rom rsegs)).
Proof.
  intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI MI R4 R3 R2 RG MM RA RC B3 O16 AV FR SE LI FB SC ML B0
    Hidx Hav Hfr Hsc Hsc63.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }

  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }

  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }

  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
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

  st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }

  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  st1. st1. st1. st1. rewrite MW2. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. if_cases K8; zify_cond K8.
  -   specialize (Hsc63 ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
    apply evt_done. unfold rr1_post, RSIZE_CLASSES. rewrite GW. do 2 eexists. reflexivity.
  - specialize (Hsc ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).
    assert (SC48 : sc < 48) by (rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia).

    st1.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (70240 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (70240 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). apply rsize_classes_read; [exact MI| lia]. }
    pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.

    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }

    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. apply evt_done. unfold rr1_post, RSIZE_CLASSES. rewrite GW. do 2 eexists. reflexivity.
Qed.

Definition rr3_post (ra sp gp tp t5 t6 s0 s1 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (gw : word) (P B sc mword stride E rsv b3 : Z) : machine_state -> Prop :=
  fun ms' => exists t4,
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + 16 + stride * Z.land b3 31)) (Z_to_bv 64 0) s0 gw a0 a1
                  (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
                  (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 160) t4 t5 t6)
             F (Z_to_bv 64 0x19b44) fc None m (seg_rom rsegs).

Lemma rrealloc_A3 : forall (ra sp gp tp t3 t4 t5 t6 s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 gw : word) F fc (m : mem)
   (P B : Z) (b3 off16 last_idx freeable sc maplen stride r32 : Z),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let E := B + 16 + stride * idx + stride - 4 in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  bv_unsigned a0 = P -> 0 <= B -> B + 16 <= P ->
  mem_inv rsegs m ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen <> 0 /\ last_idx = 0 -> stride = maplen * 4096 - 16) ->
  (maplen = 0 \/ last_idx <> 0 -> stride = 16 * size_class sc /\ sc < 48) ->
  16 <= stride -> P <= E -> E + 5 <= 2^64 ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at rsegs m (E - 4) (le4 (wz r32)) /\ bytes_at rsegs m (E - 5) [b8 0]) ->
  rsv <= E - P -> bytes_at rsegs m (E - rsv) [b8 0] -> bytes_at rsegs m E [b8 0] ->
  evt rsegs (rr3_post ra sp gp tp t5 t6 s0 gw a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m gw P B sc mword stride E rsv b3)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 gw a0 a1
               (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES) (wz off16) (wz b3)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19aac) fc None m (seg_rom rsegs)).
Proof.
  intros until r32. intros idx mword E rsv0 rsv HP B0 BP MI B3 O16 LI FB SC ML Hml STR1 STR2 S16 PE ETOP BIG RSVLE RB0r RE0.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  pose proof (bytes_at_read rsegs m _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
  pose proof (bytes_at_read rsegs m _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.
  assert (MW12 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (MWP : mword - mword mod 4096 = 4096 * maplen) by (subst mword; Z.div_mod_to_equations; lia).
  unfold RSIZE_CLASSES in *.

  assert (TAIL : forall t2v t3v : word, evt rsegs (rr3_post ra sp gp tp t5 t6 s0 gw a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m gw P B sc mword stride E rsv b3)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 last_idx) t2v s0 gw a0 a1
               (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 70240) (Z_to_bv 64 stride) (wz b3)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
          F (Z_to_bv 64 0x19ad4) fc None m (seg_rom rsegs))).
  { intros t2v t3v.

    st1. st1. st1. st1. st1. st1. st1.
    replace (B + stride * idx + 16 + stride + -4) with E by (unfold E; lia).
    replace (B + stride * idx + 16 + stride) with (E + 4) by (unfold E; lia).
    replace (B + stride * idx + 16) with (B + 16 + stride * idx) by lia.
    fold rsv0.

    assert (J : forall a7v t2w : word, bv_unsigned t2w = rsv ->
      evt rsegs (rr3_post ra sp gp tp t5 t6 s0 gw a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m gw P B sc mword stride E rsv b3)
        (MS (mkR ra sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + 16 + stride * idx)) t2w s0 gw a0 a1
                 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 70240) (Z_to_bv 64 (E + 4)) a7v
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 160) t4 t5 t6)
            F (Z_to_bv 64 0x19b1c) fc None m (seg_rom rsegs))).
    { intros a7v t2w HT2.

      st1. rewrite HP. replace (E + - P) with (E - P) by lia.
      st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }

      st1. rewrite HT2. replace (E - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
      st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }

      change (Z_to_bv 64 E) with (wa E).
      st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
      apply evt_done. unfold rr3_post. eexists. reflexivity. }

    st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
    -   apply J. unfold rsv. destruct (Z.leb_spec 160 b3); [lia|]. apply unsigned_lit. lia.
    - destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
      pose proof (bytes_at_read rsegs m _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
      cbn [skipn Z.to_nat] in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
      replace (E - 4) with (E + 4 + -8) in RD4 by lia.
      pose proof (bytes_at_read rsegs m _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.
      replace (E - 5) with (E + 4 + -9) in RD5 by lia.

      st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }

      st1. rewrite zx32_wz by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }

      st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
      apply J. unfold rsv. destruct (Z.leb_spec 160 b3); [| lia]. apply wz_unsigned. lia. }

  st1. rewrite MW12. st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  -
    destruct (STR2 ltac:(left; exact Km)) as [STR SC48].
    st1. replace (70240 + sc * 2) with (70240 + 2 * sc) by lia.
    pose proof (rsize_classes_read m sc MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
    pose proof (size_class_range sc ltac:(lia)) as SZ.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
    apply TAIL.
  -
    specialize (Hml Km).
    st1. st1. st1. if_cases K9; zify_cond K9.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K9 by lia. change (2^8) with 256 in K9. change 18446744073709551615 with (Z.ones 64) in K9.
        rewrite ?Z.land_ones, ?wz_unsigned, ?unsigned_lit in K9 by lia. rewrite ?Z.mod_small in K9 by lia. lia. }

    st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
    +
      specialize (STR1 ltac:(split; [exact Km| exact Kl])).
      st1. st1. rewrite land_pgmask by lia. rewrite MWP. st1. st1.
      replace (Z_to_bv 64 (4096 * maplen + -16)) with (Z_to_bv 64 stride) by (rewrite STR1; f_equal; lia).
      apply TAIL.
    + destruct (STR2 ltac:(right; exact Kl)) as [STR SC48].
      st1. replace (70240 + sc * 2) with (70240 + 2 * sc) by lia.
      pose proof (rsize_classes_read m sc MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
      pose proof (size_class_range sc ltac:(lia)) as SZ.
      st1. try rewrite (Z.mod_small (size_class sc)) by lia.
      st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
      replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
      apply TAIL.
Qed.
