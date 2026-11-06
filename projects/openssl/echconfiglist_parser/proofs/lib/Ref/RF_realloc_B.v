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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import F_malloc_free F_malloc_fast MallocKit_B3 F_malloc_entry.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_B RF_get_meta RF_malloc_entry RF_realloc_A.
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

Lemma zx32_wz' x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. try hcb. try hsb. intros. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition rre_nom_post (ra sp gp tp s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 gw : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (P B mword sc stride E rsv : Z) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 (E + 4 - stride)) (Z_to_bv 64 131072) s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES)
                  (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P)) (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 131051) t4 t5 t6)
             F (Z_to_bv 64 0x271288) fc None m (seg_rom rsegs).

Lemma rre_nom_walk : forall (ra sp gp tp t2 s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc (m : mem)
    (P B idx lidx mword b3 sc stride E r32 : Z),
  let rsv := if 160 <=? b3 then r32 else Z.shiftr b3 5 in
  bv_unsigned a0 = P -> E = B + 16 + stride * idx + stride - 4 ->
  0 <= B -> 0 <= idx < 32 -> 0 <= stride -> 0 <= stride * idx -> P <= E -> E + 5 <= 2^64 -> 0 <= b3 < 256 -> 0 <= mword < 2^64 ->
  (160 <= b3 -> Z.shiftr b3 5 = 5 /\ 5 <= r32 < 2^32 /\ ov_read_bytes rsegs m (wa (E - 4)) 4 = Some (le4 (wz r32)) /\ ov_read_bytes rsegs m (wa (E - 5)) 1 = Some [b8 0]) ->
  rsv <= E - P -> ov_read_bytes rsegs m (wa (E - rsv)) 1 = Some [b8 0] -> ov_read_bytes rsegs m (wa E) 1 = Some [b8 0] ->
  evt rsegs (rre_nom_post ra sp gp tp s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 gw F fc m P B mword sc stride E rsv)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 lidx) t2 s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES)
               (Z_to_bv 64 stride) (wz b3) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x271210) fc None m (seg_rom rsegs)).
Proof. try hcb. try hsb.
  intros until r32. intros rsv HP HE B0 I0 S0 SI0 PE EHI B3 MW BIG RSV RR RE.
  pose proof (bv_unsigned_in_range _ a0) as PR. change (bv_modulus 64) with (2^64) in PR. rewrite HP in PR.
  assert (RSV0 : 0 <= Z.shiftr b3 5 < 8).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32) by (subst rsv; destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]).
  (* [comment removed for export] *)
  st1. rewrite ?(unsigned_lit idx) by lia. st1. st1. st1. st1. st1. st1. rewrite ?(wz_unsigned b3) by lia.
  replace (B + stride * idx + 16 + stride + -4) with E by lia.
  replace (B + stride * idx + 16 + stride) with (E + 4) by lia.
  replace (B + stride * idx + 16) with (E + 4 - stride) by lia.
  (* [comment removed for export] *)
  assert (KJ : forall a7v t3v, evt rsegs (rre_nom_post ra sp gp tp s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 gw F fc m P B mword sc stride E rsv)
     (MS (mkR ra sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 (E + 4 - stride)) (Z_to_bv 64 rsv) s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES)
              (Z_to_bv 64 (E + 4)) a7v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
         F (Z_to_bv 64 0x271258) fc None m (seg_rom rsegs))).
  { intros a7v t3v.
    (* [comment removed for export] *)
    st1. rewrite ?HP. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?unsigned_lit in K5 by lia. lia. }
    (* [comment removed for export] *)
    st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)) at 1.
    st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
    (* [comment removed for export] *)
    change (Z_to_bv 64 E) with (wa E) at 1.
    st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. reflexivity. }
    (* [comment removed for export] *)
    st1. st1. apply evt_done. unfold rre_nom_post. reflexivity. }
  (* [comment removed for export] *)
  st1. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned b3), ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *) replace (Z.shiftr b3 5) with rsv by (subst rsv; replace (160 <=? b3) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
    apply KJ.
  - destruct (BIG ltac:(lia)) as (R5 & R32 & RD4 & RD5). rewrite R5.
    (* [comment removed for export] *)
    st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
    (* [comment removed for export] *)
    assert (RD4' : ov_read_bytes rsegs m (Z_to_bv 64 (E + 4 + -8)) 4 = Some (le4 (wz r32))) by (replace (E + 4 + -8) with (E - 4) by lia; exact RD4).
    st1. rewrite ?zx32_wz by lia.
    (* [comment removed for export] *)
    st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia. lia. }
    (* [comment removed for export] *)
    assert (RD5' : ov_read_bytes rsegs m (Z_to_bv 64 (E + 4 + -9)) 1 = Some [b8 0]) by (replace (E + 4 + -9) with (E - 5) by lia; exact RD5).
    st1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. apply K4. reflexivity. }
    replace (wz r32) with (Z_to_bv 64 rsv) by (subst rsv; replace (160 <=? b3) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
    change (Z_to_bv 64 rsv) with (wz rsv). rewrite zx32_wz' by lia. apply KJ.
Qed.

(* [comment removed for export] *)
Definition rinplace (n avail sc : Z) : bool := (n <=? avail) && (sc <=? size_to_class n + 1).

(* [comment removed for export] *)
Definition rre_dec_post (ra sp gp tp s0 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 gw : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (n P sc E rsv : Z) : machine_state -> Prop :=
  fun ms' => exists a2 a4 a5 a7 t1 t2,
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 E) t1 t2 s0 gw a0 (Z_to_bv 64 n) a2 (Z_to_bv 64 sc) a4 a5
                  (Z_to_bv 64 (E + 4)) a7 (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 131051) t4 t5 t6)
             F (Z_to_bv 64 (if rinplace n (E - P) sc then 0x271464 else 0x271424)) fc None m (seg_rom rsegs).

Lemma rre_dec_walk : forall (ra sp gp tp s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 gw : word) F fc (m : mem)
    (n P B mword sc stride E rsv : Z),
  a1 = Z_to_bv 64 n -> 1 <= n < MMAP_THRESHOLD -> 0 <= P <= E -> E + 5 <= 2^64 -> 0 <= sc < 64 -> mem_inv rsegs m ->
  evt rsegs (rre_dec_post ra sp gp tp s0 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 gw F fc m n P sc E rsv)
    (MS (mkR ra sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 (E + 4 - stride)) (Z_to_bv 64 131072) s0 gw a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES)
                  (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P)) (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 131051) t4 t5 t6)
        F (Z_to_bv 64 0x271288) fc None m (seg_rom rsegs)).
Proof. try hcb. try hsb.
  intros until rsv. intros HA N PE EHI SC MI. subst a1.
  pose proof (size_to_class_props n ltac:(lia)) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
  (* [comment removed for export] *)
  st1. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia. { exfalso. lia. }
  (* [comment removed for export] *)
  st1. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  { (* [comment removed for export] *)
    st1. st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia. 2:{ exfalso. lia. }
    apply evt_done. unfold rre_dec_post, rinplace. replace (n <=? E - P) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
    do 6 eexists. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1.
  rewrite ?(unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
  assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
  (* [comment removed for export] *)
  assert (KF : forall (a4v a5v a7v t1v : word),
    evt rsegs (rre_dec_post ra sp gp tp s0 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 gw F fc m n P sc E rsv)
      (MS (mkR ra sp gp tp (Z_to_bv 64 E) t1v (Z_to_bv 64 131072) s0 gw a0 (Z_to_bv 64 n) (Z_to_bv 64 (size_to_class n)) (Z_to_bv 64 sc) a4v a5v
                  (Z_to_bv 64 (E + 4)) a7v (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 131051) t4 t5 t6)
          F (Z_to_bv 64 0x27141c) fc None m (seg_rom rsegs))).
  { intros a4v a5v a7v t1v. st1. rewrite ?(unsigned_lit (size_to_class n)) by lia. rewrite ?(swrap32_small (size_to_class n + 1)) by lia.
    st1. if_cases KD; zify_cond KD; rewrite ?signed_of_Z in KD by lia.
    - apply evt_done. unfold rre_dec_post, rinplace. replace (n <=? E - P) with true by (symmetry; apply Z.leb_le; lia).
      replace (sc <=? size_to_class n + 1) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. do 6 eexists. reflexivity.
    - apply evt_done. unfold rre_dec_post, rinplace. replace (n <=? E - P) with true by (symmetry; apply Z.leb_le; lia).
      replace (sc <=? size_to_class n + 1) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb]. do 6 eexists. reflexivity. }
  st1. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit n) in K3 by lia.
  - (* [comment removed for export] *)
    replace (Z_to_bv 64 q) with (Z_to_bv 64 (size_to_class n)).
    2:{ f_equal. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity. }
    apply KF.
  - (* [comment removed for export] *)
    assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (rclz_pow_eq x XR) as [PW RV4].
    (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    assert (K13 : 3 <= k <= 12) by (apply LG; lia).
    (* [comment removed for export] *)
    step. step. step.
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. unfold RDEBRUIJN in DBR.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
    step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. unfold RSIZE_CLASSES. replace (466696 + (i + 1) * 2) with (466696 + 2 * (i + 1)) by lia.
    pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
    step. rewrite ?zx16_wz by lia. clear RS1.
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      evt rsegs (rre_dec_post ra sp gp tp s0 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 gw F fc m n P sc E rsv)
        (MS (mkR ra sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 298224) (Z_to_bv 64 131072) s0 gw a0 (Z_to_bv 64 n)
                 (Z_to_bv 64 q) (Z_to_bv 64 sc) (Z_to_bv 64 (120 - i)) (Z_to_bv 64 466696) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 c)
                 (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 131051) t4 t5 t6)
            F (Z_to_bv 64 0x271400) fc None m (seg_rom rsegs))).
    { intros i1 c Hi1 Hc.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite ?(unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
      step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (466696 + i1 * 2) with (466696 + 2 * i1) by lia.
      pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      (* [comment removed for export] *)
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
        replace (Z_to_bv 64 i1) with (Z_to_bv 64 (size_to_class n)).
        2:{ f_equal. rewrite STC, STQ. cbv zeta. rewrite <- Hi1. replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
        apply KF.
      * rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        replace (Z_to_bv 64 (i1 + 1)) with (Z_to_bv 64 (size_to_class n)).
        2:{ f_equal. rewrite STC, STQ. cbv zeta. rewrite <- Hi1. replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
        apply KF. }
    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K4 by lia.
    + (* [comment removed for export] *)
      step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + (* [comment removed for export] *)
      step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End HCW.
