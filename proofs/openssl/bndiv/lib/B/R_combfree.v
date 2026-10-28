(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout R_small R_m2s R_cache_defs R_sizeclass R_classid.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma class_of_addr_shift : forall c off, (0 <= c < 32)%Z -> (0 <= off < 2^32)%Z ->
  Z.shiftr (Z.shiftl (c * 2^32 + off) 27 mod 18446744073709551616) 59 = c.
Proof.
  intros c off Hc Hoff. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  change 18446744073709551616%Z with (2^64)%Z.
  replace ((c * 2 ^ 32 + off) * 2 ^ 27)%Z with (c * 2^59 + off * 2^27)%Z by lia.
  rewrite Z.mod_small by lia. symmetry. apply Z.div_unique with (off * 2^27)%Z; lia.
Qed.

Lemma shr32_region : forall c off, (0 <= c)%Z -> (0 <= off < 2^32)%Z -> Z.shiftr (c * 2^32 + off) 32 = c.
Proof.
  intros c off Hc Hoff. rewrite Z.shiftr_div_pow2 by lia. symmetry. apply Z.div_unique with off; lia.
Qed.

Lemma land31_small : forall c, (0 <= c < 32)%Z -> Z.land c 31 = c.
Proof. intros c Hc. change 31%Z with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma v_divuw_region : forall c off y, (0 <= c < 32)%Z -> (0 <= off < 2^32)%Z -> (2 <= y < 2^31)%Z ->
  v_divuw (Z_to_bv 64 (c * 2^32 + off)) (Z_to_bv 64 y) = Z_to_bv 64 (off / y).
Proof.
  intros c off y Hc Hoff Hy. unfold v_divuw. rewrite !unsigned_lit by lia. rewrite (wrap32_small y) by lia.
  rewrite (proj2 (Z.eqb_neq y 0)) by lia.
  replace (bv_wrap 32 (c * 2 ^ 32 + off)) with off.
  2:{ unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.add_comm, Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }
  f_equal. apply swrap32_small. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
Qed.

Definition size_e2 (c : Z) : Z :=
  (Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl c 63))) 63 mod 18446744073709551616)
         (Z.shiftr (Z.shiftl 512 (Z.shiftr (c + -16) 1 mod 64) mod 18446744073709551616) 1)
   + Z.shiftl 512 (Z.shiftr (c + -16) 1 mod 64))%Z.
Lemma size_e2_ok : forall c, (17 <= c <= 30)%Z -> size_e2 c = ClassSize c.
Proof. intros c Hc. exact (brute_eq size_e2 ClassSize 17 30 ltac:(vm_compute; reflexivity) c Hc). Qed.

Definition gbb_pc0 : Z := 0x19806c.
Definition gbb_pc1 : Z := 0x198134.

Definition gbb_post (ra sp gp tp t0 t1 t2 s0 s1 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (SB blk : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (a2' a3' a4' a5' a6' a7' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SB) (Z_to_bv 64 (SB + 2^37)) a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 blk) s3 (Z_to_bv 64 (2^37)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 gbb_pc1) fc None m (seg_rom bsegs).

Lemma gbb_frag_spec : forall ra sp gp tp t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c idx d mu : Z),
  (1 <= c <= 30)%Z -> (0 <= idx)%Z -> (0 <= d < ClassSize c)%Z -> ((idx + 1) * ClassSize c <= mu <= 0xE0000000)%Z ->
  rw_cells bsegs m i_spacebeg [C8 (Z_to_bv 64 SB); C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (SB + 2^37))] ->
  rw_cells bsegs m (SB + 2^37 + 128 * c + 48) [C8 (Z_to_bv 64 mu)] ->
  SB_ok ACEIL SB ->
  mem_inv bsegs m ->
  let blk := (SB + c * 2^32 + idx * ClassSize c)%Z in
  evt bsegs (gbb_post ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (blk + d)) (Z_to_bv 64 INST) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc SB blk m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (blk + d)) a0 (Z_to_bv 64 (blk + d)) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 INST) s4
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 gbb_pc0) fc None m (seg_rom bsegs)).
Proof.
  intros until mu. intros Hc Hidx Hd Hmu SBC RI HSB MI blk.
  destruct HSB as (HSB1 & HSB2 & HSB3 & HSB4). unfold kHighShadowEnd in *.
  pose proof (ClassSize_range c ltac:(lia)) as [HCS _].
  unfold i_spacebeg, INST, gbb_pc0, gbb_pc1, g_instance in *.
  change (6947736 + 32)%Z with 6947768%Z in SBC.
  assert (Hoff : (0 <= idx * ClassSize c + d < 2^32)%Z) by nia.
  zhide.
  do 4 zstep. ifF.
  do 2 zstep. ifF.
  do 5 zstep.
  assert (EO : (blk + d - SB = c * 2^32 + (idx * ClassSize c + d))%Z) by (unfold blk; lia).
  rewrite EO. rewrite (shr32_region c (idx * ClassSize c + d)) by lia. rewrite (land31_small c) by lia.
  ifF.
  do 2 zstep.
  assert (JOIN : forall a6' a7',
    evt bsegs (gbb_post ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (blk + d)) (Z_to_bv 64 6947736) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc SB blk m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (blk + d)) (Z_to_bv 64 SB) (Z_to_bv 64 (SB + 2^37)) (Z_to_bv 64 c) (Z_to_bv 64 c)
             (Z_to_bv 64 (c * 2 ^ 32 + (idx * ClassSize c + d))) (Z_to_bv 64 (ClassSize c)) a6' a7' s2 (Z_to_bv 64 6947736) (Z_to_bv 64 (2^37))
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1980f0) fc None m (seg_rom bsegs))).
  { intros a6' a7'.
    zstep. rewrite v_divuw_region by lia.
    replace ((idx * ClassSize c + d) / ClassSize c)%Z with idx by (apply Z.div_unique with d; lia).
    change (2^37)%Z with 137438953472%Z in RI.
    do 6 zstep.
    replace (SB + 137438953472 + Z.shiftl c 7)%Z with (SB + 137438953472 + 128 * c)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    do 9 zstep.
    assert (Hidx32 : (idx mod 4294967296 = idx)%Z) by (apply Z.mod_small; nia).
    rewrite Hidx32.
    rewrite (proj2 (Z.ltb_ge mu (ClassSize c * idx + ClassSize c))) by nia. cbn [Z.b2z].
    change ((0 + -1) mod 18446744073709551616)%Z with 18446744073709551615%Z.
    replace (Z.land 18446744073709551615 ((Z.shiftl c 32 + SB + ClassSize c * idx) mod 18446744073709551616)) with blk.
    2:{ rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (unfold blk in *; nia).
        change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
        rewrite Z.mod_small by (unfold blk in *; nia). unfold blk. lia. }
    assert (Hblk : (SB <= blk < SB + 2^37)%Z) by (unfold blk; nia).
    ifF. zstep. ifF.
    apply evt_done. unfold gbb_post. do 6 eexists. reflexivity. }
  destruct (Z.le_gt_cases c 16) as [Hs|Hl].
  - ifF. zstep. ifF.
    do 2 zstep.
    replace (Z.shiftl c 5) with (ClassSize c).
    2:{ rewrite Z.shiftl_mul_pow2 by lia. unfold ClassSize. rewrite (proj2 (Z.eqb_neq c 31)) by lia.
        rewrite (proj2 (Z.leb_le c 16)) by lia. lia. }
    apply JOIN.
  - ifT.
    do 9 zstep.
    let e := getreg 15%Z in lazymatch e with Z_to_bv 64 ?E => replace E with (ClassSize c) by (exact (eq_sym (size_e2_ok c ltac:(lia)))) end.
    apply JOIN.
Qed.

(* [comment removed for export] *)
Definition rtail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (cache c p lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 cache) (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 p)
                  a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x198444) fc None m' (seg_rom bsegs)
    /\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Lemma rtail_frag_spec : forall ra0 sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (cb : word) (s0o s1o s2o s3o s4o rao : word) (ACEIL SB cache c off lo : Z),
  (1 <= c <= 31)%Z -> (0 <= off < 2^32)%Z -> (0 <= cache < 2^64)%Z ->
  rw_cells bsegs m i_spacebeg [C8 (Z_to_bv 64 SB)] ->
  rw_cells bsegs m (bv_unsigned cb) [C8 (Z_to_bv 64 cache)] ->
  SB_ok ACEIL SB ->
  rw_cells bsegs m (bv_unsigned sp - 48) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  stk bsegs m lo (bv_unsigned sp - 48) -> (lo <= bv_unsigned sp - 48)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (rtail_post rao sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc cache c (SB + c * 2^32 + off) lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 cb s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (SB + c * 2^32 + off)) (Z_to_bv 64 INST) (Z_to_bv 64 (2^37)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1981dc) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros Hc Hoff Hcache SBC CBC HSB FR ST HLO2 HSP MI.
  destruct HSB as (HSB1 & HSB2 & HSB3 & HSB4). unfold kHighShadowEnd in *.
  unfold i_spacebeg, INST, g_instance in *.
  change (6947736 + 32)%Z with 6947768%Z in SBC.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zhide.
  do 2 zstep. ifF.
  do 2 zstep. ifF.
  do 4 zstep.
  replace (SB + c * 4294967296 + off - SB)%Z with (c * 2^32 + off)%Z by lia.
  rewrite (class_of_addr_shift c off) by lia.
  do 11 zstep.
  replace (bv_unsigned sp - 48 + 48)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Definition drdealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (cache c b : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR (Z_to_bv 64 0x198004) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 cache) (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 b)
                  a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x198444) fc None m (seg_rom bsegs).

Lemma drdealloc_frag_spec : forall ra sp gp tp t0 t1 t2 s0 s2 s3 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB cache c off : Z),
  (1 <= c <= 31)%Z -> (0 <= off < 2^32)%Z -> (0 <= cache < 2^64)%Z ->
  rw_cells bsegs m i_spacebeg [C8 (Z_to_bv 64 SB)] ->
  rw_cells bsegs m (bv_unsigned sp + 8) [C8 (Z_to_bv 64 cache)] ->
  SB_ok ACEIL SB -> (bv_unsigned sp + 16 <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (drdealloc_post ra sp gp tp s0 (Z_to_bv 64 INST) s2 s3 (Z_to_bv 64 (SB + c * 2^32 + off)) (Z_to_bv 64 (2^37))
               s6 s7 s8 s9 s10 s11 F fc cache c (SB + c * 2^32 + off) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (SB + c * 2^32 + off))
             (Z_to_bv 64 (2^37)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x197fd8) fc None m (seg_rom bsegs)).
Proof.
  intros until off. intros Hc Hoff Hcache SBC CBC HSB HSP MI.
  destruct HSB as (HSB1 & HSB2 & HSB3 & HSB4). unfold kHighShadowEnd in *.
  unfold i_spacebeg, INST, g_instance in *.
  change (6947736 + 32)%Z with 6947768%Z in SBC.
  zhide.
  do 2 zstep. ifF.
  do 2 zstep. ifF.
  do 4 zstep.
  replace (SB + c * 4294967296 + off - SB)%Z with (c * 2^32 + off)%Z by lia.
  rewrite (class_of_addr_shift c off) by lia.
  do 3 zstep.
  apply evt_done. unfold drdealloc_post. do 11 eexists. reflexivity.
Qed.
