(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

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

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Notation mem := (word -> option byte).

Definition cdealloc_entry : Z := 0x5dd7c.
Definition cdealloc_retD : Z := 0x5df2c.
Definition drainhalf_retB : Z := 0x5e174.
Definition rta_entry : Z := 0x5e2b4.

Definition compact_of (SB c p : Z) : Z := (p - SB - c * 2^32) / 16.

Lemma compact_code : forall SB c p, (0 <= c < 2^31)%Z -> (0 <= SB)%Z -> (0 <= p - SB - c * 2^32 < 2^32)%Z ->
  Z.shiftr (Z.land (p + - Z.land (Z.shiftl c 32) 18446744073709551615 + - SB) 18446744073709551615) 4 = compact_of SB c p.
Proof.
  intros SB c p Hc HSB Hp. unfold compact_of. change 18446744073709551615%Z with (Z.ones 64).
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.land_ones (c * 2 ^ 32)) by lia. rewrite Z.mod_small by lia.
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. f_equal; lia.
Qed.

Lemma compact_of_range : forall SB c p, (0 <= p - SB - c * 2^32 < 2^32)%Z -> (0 <= compact_of SB c p < 2^28)%Z.
Proof. intros SB c p Hp. unfold compact_of. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. Qed.

Definition cdealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T SB c p cnt mc cs : Z) (ws : list word) (W : list (Z * Z)) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (stj : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ pc_cells m' (pc_addr T c) (cnt + 1) mc cs
    /\ u32arr asegs m' (pc_addr T c + 16) (upd ws (Z.to_nat cnt) (Z_to_bv 64 (compact_of SB c p)))
    /\ rw_cells asegs m' (cstat_alloc T) [C8 stj]
    /\ rw_cells asegs m' i_spacebeg [C8 (Z_to_bv 64 SB)]
    /\ stk asegs m' lo (bv_unsigned sp).

Definition cdealloc_W (T c : Z) (sp : word) : list (Z * Z) :=
  [(pc_addr T c, pc_addr T c + 4); (pc_addr T c + 16, pc_addr T c + 80); (cstat_alloc T, cstat_alloc T + 8);
   (bv_unsigned sp - 48, bv_unsigned sp)]%Z.

Lemma cdealloc_push_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL T SB c p cnt mc cs lo : Z) (ws : list word) (stj : word),
  (1 <= c <= 31)%Z ->
  (SB + c * 2^32 <= p < SB + c * 2^32 + 2^32)%Z -> ((p - SB - c * 2^32) mod 16 = 0)%Z ->
  rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] ->
  pc_cells m (pc_addr T c) cnt mc cs -> (0 <= cnt < mc)%Z -> (1 <= mc <= 16)%Z -> (0 <= cs < 2^63)%Z ->
  u32arr asegs m (pc_addr T c + 16) ws -> length ws = 16%nat ->
  rw_cells asegs m (cstat_alloc T) [C8 stj] ->
  T_ok ACEIL T -> SB_ok ACEIL SB ->
  stk asegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (cdealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T SB c p cnt mc cs ws (cdealloc_W T c sp) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 p)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until stj. intros Hc Hp Hpal SBC PC Hcnt Hmc Hcs ARR Hlen STA HT HSB ST HLO HLOH HLO2 HSP MI.
  destruct HT as (HT1 & HT2 & HT3 & HT4 & HT5). unfold img_hull_lo, img_hull_hi in HT5. destruct HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  unfold kHighShadowEnd in *.
  unfold cdealloc_W, pc_cells, pc_addr, cstat_alloc, cacheT, i_spacebeg, INST, cdealloc_entry, g_instance in *.
  change (1508824 + 32)%Z with 1508856%Z in SBC.
  remember (T + 208 + 80 * c)%Z as P eqn:EP.
  pose proof (munch_refl [(P, P + 4); (P + 16, P + 80); (T + 2784, T + 2784 + 8); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  zidle_begin sp 48%Z MUz WMz.
  do 8 zstep.
  zidle_end MUz WMz.
  ifF.
  do 2 zstep. ifF.
  do 3 zstep.
  replace (T + 208 + c * 80)%Z with P by lia.
  zstep. rewrite (sx32_small_A mc) by lia. zstep. ifF.
  zstep. rewrite (sx32_small_A cnt) by lia. zstep. ifF.
  do 12 zstep.
  rewrite (shl32_shr30 cnt) by lia.
  rewrite (compact_code SB c p) by lia.
  pose proof (compact_of_range SB c p ltac:(lia)) as HCP.
  zstep.
  pose proof (u32arr_store_ok asegs m0 (P + 16) ws cnt (Z_to_bv 64 (P + 4 * cnt + 16)) ARR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SO.
  zstep.
  pose proof (u32arr_write asegs m0 (P + 16) ws cnt (Z_to_bv 64 (compact_of SB c p)) ARR ltac:(lia)) as ARR'.
  replace (P + 16 + 4 * cnt)%Z with (P + 4 * cnt + 16)%Z in ARR' by lia.
  store_done.
  zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (T + 2784)) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. lia. }
  amo_step AMO.
  do 8 zstep.
  release_frame FR ST (bv_unsigned sp).
  finish; unfold pc_addr, cstat_alloc, pc_cells; try rewrite <- EP; try eassumption.
  eapply munch_weaken; [|exact MU]. intros x Hx. cbn in *. lia.
Qed.

Definition cdealloc_drain_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T c p P mc cs lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 drainhalf_retB) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0' t1' t2' (Z_to_bv 64 P)
                  (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 INST) (Z_to_bv 64 (bv_unsigned sp - 104)) (Z_to_bv 64 (cstats T))
                  (Z_to_bv 64 c) (Z_to_bv 64 (P + 16 + 4 * (mc - mc / 2))) (Z_to_bv 64 (mc / 2)) a6' a7'
                  (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 p) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 rta_entry) fc None m' (seg_rom asegs)
    /\ munch [(P, P + 4); (bv_unsigned sp - 112, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ pc_cells m' P (mc - mc / 2) mc cs
    /\ rw_cells asegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (bv_unsigned sp - 112) [CB 8 junk; C8 (Z_to_bv 64 INST); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                                 C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 cdealloc_retD)]
    /\ stk asegs m' lo (bv_unsigned sp - 112).

Lemma cdealloc_drain_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL T c p mc cs lo : Z),
  (1 <= c <= 31)%Z ->
  pc_cells m (pc_addr T c) mc mc cs -> (2 <= mc <= 16)%Z -> (0 <= cs < 2^63)%Z ->
  T_ok ACEIL T ->
  stk asegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 112)%Z ->
  (bv_unsigned sp <= 2^47)%Z -> (0 <= p < 2^64)%Z ->
  mem_inv asegs m ->
  evt asegs (cdealloc_drain_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T c p (pc_addr T c) mc cs lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 p)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros Hc PC Hmc Hcs HT ST HLO HLOH HLO2 HSP Hp MI.
  destruct HT as (HT1 & HT2 & HT3 & HT4 & HT5). unfold img_hull_lo, img_hull_hi in HT5. unfold kHighShadowEnd in *.
  unfold pc_cells, pc_addr, cstats, cacheT, INST, cdealloc_entry, drainhalf_retB, rta_entry, cdealloc_retD, g_instance in *.
  remember (T + 208 + 80 * c)%Z as P eqn:EP.
  pose proof (munch_refl [(P, P + 4); (bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  zidle_begin sp 48%Z MUz WMz.
  do 8 zstep.
  zidle_end MUz WMz.
  ifF.
  do 2 zstep. ifF.
  do 3 zstep.
  replace (T + 208 + c * 80)%Z with P by lia.
  zstep. rewrite (sx32_small_A mc) by lia. zstep. ifF.
  zstep. rewrite (sx32_small_A mc) by lia. zstep. ifT.
  do 7 zstep.
  carve_frame 64%nat ST.
  do 2 zstep.
  zstep; fix_lit_store.
  zstep; fix_lit_store.
  zstep; fix_lit_store.
  zstep. rewrite (sx32_small_A mc) by lia.
  zstep. rewrite (zx32_small mc) by lia.
  zstep; fix_lit_store.
  zstep; fix_lit_store.
  zstep; fix_lit_store.
  zstep; fix_lit_store.
  do 3 zstep.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
  replace (Z.land mc 4294967295) with mc by (change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
  zstep. ifF.
  do 11 zstep.
  replace (P + Z.shiftl (mc + - (mc / 2)) 2 + 16)%Z with (P + 16 + 4 * (mc - mc / 2))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (bv_unsigned sp + -104)%Z with (bv_unsigned sp - 104)%Z by lia.
  replace (bv_unsigned sp + -112)%Z with (bv_unsigned sp - 112)%Z in * by lia.
  replace (bv_unsigned sp + -48)%Z with (bv_unsigned sp - 48)%Z in * by lia.
  finish; try rewrite <- EP; try eassumption.
Qed.

Lemma cdealloc_drain_B_spec : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s0o s1o s2o s3o s4o rao : word) (junk : list byte)
    (ACEIL T SB c p cnt mc cs lo : Z) (ws : list word) (stj : word),
  (1 <= c <= 31)%Z ->
  (SB + c * 2^32 <= p < SB + c * 2^32 + 2^32)%Z -> ((p - SB - c * 2^32) mod 16 = 0)%Z ->
  rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] ->
  pc_cells m (pc_addr T c) cnt mc cs -> (0 <= cnt < mc)%Z -> (1 <= mc <= 16)%Z -> (0 <= cs < 2^63)%Z ->
  u32arr asegs m (pc_addr T c + 16) ws -> length ws = 16%nat ->
  rw_cells asegs m (cstat_alloc T) [C8 stj] ->
  T_ok ACEIL T -> SB_ok ACEIL SB ->
  rw_cells asegs m (bv_unsigned sp - 48) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  rw_cells asegs m (bv_unsigned sp - 112) [CB 8 junk; C8 (Z_to_bv 64 INST); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                          C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 cdealloc_retD)] ->
  stk asegs m lo (bv_unsigned sp - 112) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 160)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (cdealloc_post rao sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc T SB c p cnt mc cs ws
               [(pc_addr T c, pc_addr T c + 4); (pc_addr T c + 16, pc_addr T c + 80); (cstat_alloc T, cstat_alloc T + 8);
                (bv_unsigned sp - 160, bv_unsigned sp)]%Z lo m)
    (MS (mkR (Z_to_bv 64 drainhalf_retB) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2 (Z_to_bv 64 (pc_addr T c))
             (Z_to_bv 64 (cacheT T)) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 p)
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 drainhalf_retB) fc None m (seg_rom asegs)).
Proof.
  intros until stj. intros Hc Hp Hpal SBC PC Hcnt Hmc Hcs ARR Hlen STA HT HSB FR FR1 ST HLO HLOH HLO2 HSP MI.
  destruct HT as (HT1 & HT2 & HT3 & HT4 & HT5). unfold img_hull_lo, img_hull_hi in HT5. destruct HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  unfold kHighShadowEnd in *.
  unfold pc_cells, pc_addr, cstat_alloc, cacheT, i_spacebeg, INST, drainhalf_retB, cdealloc_retD, g_instance in *.
  change (1508824 + 32)%Z with 1508856%Z in SBC.
  remember (T + 208 + 80 * c)%Z as P eqn:EP.
  pose proof (munch_refl [(P, P + 4); (P + 16, P + 80); (T + 2784, T + 2784 + 8); (bv_unsigned sp - 160, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z in * by lia.
  replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z in * by lia.
  zhide.
  do 3 zstep.
  carve_frame 48%nat ST.
  zstep.
  zstep. zstep; try fix_lit_store. zstep. zstep. zstep; try fix_lit_store.
  zstep. ifT.
  do 6 zstep.
  release_frame FR0 ST (bv_unsigned sp + -112)%Z.
  do 3 zstep.
  release_frame FR1 ST (bv_unsigned sp + -48)%Z.
  do 4 zstep.
  zstep. rewrite (sx32_small_A cnt) by lia.
  zstep.
  do 12 zstep.
  rewrite (shl32_shr30 cnt) by lia.
  rewrite (compact_code SB c p) by lia.
  pose proof (compact_of_range SB c p ltac:(lia)) as HCP.
  zstep.
  pose proof (u32arr_store_ok asegs m0 (P + 16) ws cnt (Z_to_bv 64 (P + 4 * cnt + 16)) ARR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SO.
  zstep.
  pose proof (u32arr_write asegs m0 (P + 16) ws cnt (Z_to_bv 64 (compact_of SB c p)) ARR ltac:(lia)) as ARR'.
  replace (P + 16 + 4 * cnt)%Z with (P + 4 * cnt + 16)%Z in ARR' by lia.
  store_done.
  zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (T + 2784)) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. lia. }
  amo_step AMO.
  do 8 zstep.
  release_frame FR ST (bv_unsigned sp).
  finish; unfold pc_addr, cstat_alloc, pc_cells; try rewrite <- EP; try eassumption.
  eapply munch_weaken; [|exact MU]. intros x Hx. cbn in *. lia.
Qed.
