(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_classid R_comballoc R_refill.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition comballoc_retR : Z := 0x5d9dc.
Definition comballoc_retS : Z := 0x5d7d4.
Definition sec_alloc_entry : Z := 0x5da04.

Definition comballoc_miss_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T c P lo : Z) (m : mem) (K : mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 comballoc_retR) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0' t1' t2' (Z_to_bv 64 c) (Z_to_bv 64 P)
                  (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 P) (Z_to_bv 64 INST) (Z_to_bv 64 c) a4' a5' a6' a7'
                  (Z_to_bv 64 8) (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 INST) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 refill_entry) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk bsegs m' lo (bv_unsigned sp - 48)
    /\ K m'.

Lemma comballoc_miss_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL T size mc cs lo : Z),
  (1 <= size <= 65536)%Z ->
  pc_cells m (pc_addr T (ClassID size)) 0 mc cs -> (0 <= mc < 2^31)%Z -> (0 <= cs < 2^63)%Z ->
  T_ok ACEIL T ->
  stk bsegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (comballoc_miss_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T (ClassID size) (pc_addr T (ClassID size)) lo m
               (fun m' => pc_cells m' (pc_addr T (ClassID size)) 0 mc cs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 size) (Z_to_bv 64 8)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 comballoc_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros Hsz PC Hmc Hcs HT ST HLO HLOH HLO2 HSP MI.
  pose proof (ClassID_props size Hsz) as [Hc Hcsz].
  set (c := ClassID size) in *.
  destruct HT as (HT1 & HT2 & HT3 & HT4 & HT5). unfold kHighShadowEnd in *.
  unfold pc_cells, pc_addr, cacheT, INST, comballoc_entry, refill_entry, comballoc_retR, g_instance in *.
  remember (T + 208 + 80 * c)%Z as P eqn:EP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  do 7 zstep.
  do 2 zstep.
  rewrite (proj2 (Z.ltb_ge size 1)) by lia. cbn [Z.b2z]. rewrite Z.add_0_r.
  do 2 zstep. rewrite zb_lxor_ones by lia. ifT.
  do 3 zstep. ifT.
  do 2 zstep. ifF.
  zstep. ifF.
  eapply evt_cut; [apply classid_35x_spec; [lia| assumption]|].
  intros ms' (t0' & t1' & a2' & a4' & a5' & a6' & a7' & ->). fold c.
  zstep. ifF.
  do 2 zstep. ifF.
  do 3 zstep.
  replace (T + 208 + c * 80)%Z with P by lia.
  zstep. rewrite (sx32_small_A 0) by lia.
  zstep. ifT.
  do 8 zstep.
  finish; try rewrite <- EP; try eassumption.
Qed.

Lemma comballoc_miss_B_spec : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s0o s1o s2o s3o s4o rao : word) (ACEIL T SB c cnt mc cs lo : Z) (ws : list word) (w stj : word),
  (1 <= c <= 30)%Z -> bv_unsigned a0 <> 0%Z ->
  rw_cells bsegs m i_spacebeg [C8 (Z_to_bv 64 SB)] ->
  pc_cells m (pc_addr T c) cnt mc cs -> (1 <= cnt <= 16)%Z -> (0 <= mc < 2^31)%Z -> (0 <= cs < 2^63)%Z ->
  u32arr bsegs m (pc_addr T c + 16) ws -> length ws = 16%nat -> nth_error ws (Z.to_nat (cnt - 1)) = Some w ->
  rw_cells bsegs m (cstat_alloc T) [C8 stj] ->
  T_ok ACEIL T -> SB_ok ACEIL SB ->
  rw_cells bsegs m (bv_unsigned sp - 48) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  stk bsegs m lo (bv_unsigned sp - 48) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (comballoc_hit_post rao sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc T SB c cnt mc cs ws w lo m)
    (MS (mkR (Z_to_bv 64 comballoc_retR) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 (pc_addr T c))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 8) (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 INST) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 comballoc_retR) fc None m (seg_rom bsegs)).
Proof.
  intros until stj. intros Hc Ha0 SBC PC Hcnt Hmc Hcs ARR Hlen Hw STA HT HSB FR ST HLO HLOH HLO2 HSP MI.
  destruct HT as (HT1 & HT2 & HT3 & HT4 & HT5). destruct HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  unfold kHighShadowEnd in *.
  unfold pc_cells, pc_addr, cstat_alloc, cacheT, i_spacebeg, INST, comballoc_retR, g_instance in *.
  change (1522392 + 32)%Z with 1522424%Z in SBC.
  remember (T + 208 + 80 * c)%Z as P eqn:EP.
  pose proof (munch_refl [(P, P + 4); (T + 2784, T + 2784 + 8); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  zhide.
  zstep. ifF.
  zstep. rewrite (sx32_small_A cnt) by lia.
  do 11 zstep.
  rewrite (shl32_shr30 (cnt + -1)) by lia.
  zstep.
  pose proof (u32arr_read bsegs m0 (P + 16) ws (cnt - 1) w (Z_to_bv 64 (P + 4 * (cnt + -1) + 16)) ARR Hw ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. change (zx32 w) with (Z_to_bv 64 (cptr w)). clear RD.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (T + 2784)) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. lia. }
  amo_step AMO.
  do 7 zstep. ifT.
  do 8 zstep.
  replace (Z.shiftl (Z.land (cptr w) 18446744073709551615) 4 + (Z.shiftl c 32 + SB))%Z with (chunk_addr SB c w).
  2:{ unfold chunk_addr. pose proof (cptr_range w). change 18446744073709551615%Z with (Z.ones 64).
      rewrite Z.land_ones, Z.mod_small by lia. rewrite !Z.shiftl_mul_pow2 by lia. lia. }
  replace (bv_unsigned sp - 48 + 48)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  finish; unfold pc_addr, cstat_alloc, pc_cells; try rewrite <- EP; try eassumption.
Qed.

Definition comballoc_big_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (size lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 comballoc_retS) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0' t1' t2' (Z_to_bv 64 8) s1
                  (Z_to_bv 64 (INST + 64)) (Z_to_bv 64 (INST + 688)) (Z_to_bv 64 size) (Z_to_bv 64 8) a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 sec_alloc_entry) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk bsegs m' lo (bv_unsigned sp - 48).

Lemma comballoc_big_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL size lo : Z),
  (65536 < size <= 2^40)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (comballoc_big_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc size lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) a1 (Z_to_bv 64 size) (Z_to_bv 64 8)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 comballoc_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros Hsz ST HLO HLOH HLO2 HSP MI. unfold kHighShadowEnd in *.
  unfold INST, comballoc_entry, comballoc_retS, sec_alloc_entry, g_instance in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  do 7 zstep.
  do 2 zstep.
  rewrite (proj2 (Z.ltb_ge size 1)) by lia. cbn [Z.b2z]. rewrite Z.add_0_r.
  do 2 zstep. rewrite zb_lxor_ones by lia. ifT.
  do 3 zstep. ifT.
  do 2 zstep. ifF.
  zstep. ifT.
  do 5 zstep.
  finish.
Qed.

Lemma comballoc_big_B_spec : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s0o rao : word) (ACEIL lo : Z),
  rw_cells bsegs m (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0o; C8 rao] ->
  stk bsegs m lo (bv_unsigned sp - 48) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (frame_post rao sp gp tp s0o s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0)
               [(bv_unsigned sp - 48, bv_unsigned sp)]%Z lo m)
    (MS (mkR (Z_to_bv 64 comballoc_retS) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 8) s1
             a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 comballoc_retS) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros FR ST HLO HLOH HLO2 HSP MI. unfold kHighShadowEnd in *.
  unfold comballoc_retS in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  zhide.
  do 3 zstep. ifF.
  do 9 zstep.
  replace (bv_unsigned sp - 48 + 48)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  unfold frame_post. rewrite Z_to_bv_bv_unsigned.
  finish.
Qed.
