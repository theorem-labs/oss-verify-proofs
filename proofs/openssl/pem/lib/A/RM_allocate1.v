(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_thread R_cache_defs R_prim_defs R_leaves R_rzlog R_depot_defs R_asan_defs R_allocate1.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac arith_goal := lazymatch goal with
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac
  | |- Z.gt _ _ => idtac | |- le _ _ => idtac | |- lt _ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac
  | |- False => idtac end.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
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
Local Ltac zidle_begin sp n :=
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
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Definition alloc_frame64 (m : mem) (A : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : Prop :=
  rw_cells asegs m (A + 8) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 64); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4;
                             C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition allocate_p1_post64 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n B T lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x19af0c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (T + 208))
                  (Z_to_bv 64 (needed2 n + 64)) (Z_to_bv 64 8) a4' a5' a6' a7' (Z_to_bv 64 64) (Z_to_bv 64 (needed2 n + 64))
                  (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (64)))
                  (Z_to_bv 64 63) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
             F (Z_to_bv 64 0x19f4cc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ (exists j, rw_cells asegs m' (bv_unsigned sp + -128) [CB 8 j])
    /\ alloc_frame64 m' (bv_unsigned sp + -128) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    /\ stk asegs m' lo (bv_unsigned sp + -128).

Lemma allocate_p1_spec64 : forall ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (n B TCX T lo : Z),
  (1 <= n <= 2^31)%Z -> (n mod 64 = 0)%Z -> (needed n + 64 <= 64512)%Z -> (0 < B < 2^63)%Z ->
  rw_cells asegs m g_asan_inited [C1 (Z_to_bv 8 1)] -> rw_cells asegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m i_max_user [C8 (Z_to_bv 64 (2^40))] -> rw_cells asegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T < 2^63)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 144)%Z -> (0xbc6000 <= lo)%Z -> (bv_unsigned sp <= 2^63)%Z ->
  mem_inv asegs m ->
  evt asegs (allocate_p1_post64 ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n B T lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 64) (Z_to_bv 64 B)
             (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros Hn Hn64 HND HB AI RS MX RZ TC HTCX HTCXl HT ST HLO HIMG HSP MI. unfold allocate_entry.
  destruct TC as [(KI & K & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  unfold g_asan_inited, g_rss_limit_exceeded, INST, g_instance in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 120%nat ST. carve_frame 8%nat ST.
  zhide.
  zidle1 AI. zidle1 RS. zidle1 MX. zidle1 RZ. zidle1 KI. zidle1 K. zidle1 TS. zidle1 T0. zidle1 TT.
  do 21 zstep.
  zidle_end_m m.
  call (asan_inited_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _).
  all: try eassumption.
  zstep. ifF.
  zstep.
  call (rss_limit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _).
  all: try eassumption.
  zstep. ifF.
  zstep. ifF.
  ro_debruijn MI.
  zstep. zstep. ifT.
  do 3 zstep. ifT.
  do 3 zstep. ifF.
  do 9 zstep. fold_reg 11%Z. do 6 zstep. ifF.
  do 4 zstep. ifF.
  zstep. zstep. zstep; fix_lit_store. zstep; fix_lit_store.
  eapply rz_cascade; [lia|]. intros a0'.
  do 6 zstep.
  sp_facts.
  call (rzlog_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 0%Z lo).
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  do 5 zstep.
  call (rzlog_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 7%Z lo).
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  eapply rz_clamp; [lia|].
  do 9 zstep.
  assert (EA : (Z.land (Z.max n 8 + 63) (Z.land (0 + - (64)) 18446744073709551615) + Z.land (Z.land (Z.b2z (64 <? 9) + -1) 18446744073709551615) 64 = n + 64)%Z).
  { change (Z.land (Z.land (Z.b2z (64 <? 9) + -1) 18446744073709551615) 64) with 64%Z.
    change (Z.land (0 + - (64)) 18446744073709551615) with (Z.ldiff (Z.ones 64) (Z.ones 6)).
    assert (N64 : (64 <= n)%Z) by (clear - Hn Hzq; lia).
    rewrite Z.max_l by lia.
    rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite (Z.mod_small (n + 63) (2^64)) by lia.
    rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
    change (2^6)%Z with 64%Z. clear - Hn Hzq. Z.div_mod_to_equations. lia. }
  rewrite EA.
  assert (ER7 : Z.land (Z.land (n + 64) 18446744073709551615) 7 = 0%Z).
  { change 18446744073709551615%Z with (Z.ones 64). change 7%Z with (Z.ones 3).
    rewrite !Z.land_ones by lia. rewrite (Z.mod_small (n + 64) (2^64)) by lia. change (2^3)%Z with 8%Z. clear - Hzq. Z.div_mod_to_equations. lia. }
  rewrite ER7.
  zstep. ifF. do 15 zstep.
  pose proof (rz_size_range n) as RZR. pose proof (rz_log_range n) as RLR.
  pose proof (rounded_range n ltac:(lia)) as (RR1 & RR2 & RR3).
  assert (ERN : rounded n = n) by (clear - RR1 RR2 RR3 Hzq Hn; Z.div_mod_to_equations; lia).
  assert (Erz : bv_swrap 32 (Z.shiftl 16 (Z.land (rz_log n) 18446744073709551615 mod 32)) = rz_size n).
  { change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
    rewrite (Z.mod_small (rz_log n) (2^64)), (Z.mod_small (rz_log n) 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    apply bv_swrap_small. change (bv_half_modulus 32) with (2^31)%Z. lia. }
  rewrite Erz.
  assert (FP : from_primary n = true) by (unfold from_primary; apply Z.leb_le; clear - HND; lia).
  assert (Efp : Z.land (Z.b2z (64 <? 65537)) (Z.b2z (Z.land (n + 64 + rz_size n) 18446744073709551615 <? 65537))
                = Z.b2z (from_primary n)).
  { rewrite FP. change (Z.b2z (64 <? 65537)) with 1%Z. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
    rewrite (Z.mod_small (n + 64 + rz_size n) (2^64)) by lia. unfold needed in HND. rewrite ERN in HND.
    rewrite (proj2 (Z.ltb_lt _ 65537)) by lia. reflexivity. }
  rewrite Efp.
  assert (Enn : (Z.land (Z.land (Z.b2z (from_primary n) + -1) 18446744073709551615) (Z.land (rz_size n) 18446744073709551615)
                + (n + 64 + rz_size n) = needed2 n + 64)%Z).
  { unfold needed2, needed. rewrite FP, ERN. cbn [Z.b2z Z.add]. rewrite Z.land_0_l. lia. }
  rewrite Enn.
  rewrite (proj2 (Z.ltb_ge n 1)) by lia. cbn [Z.b2z]. rewrite Z.add_0_r.
  pose proof (needed2_range n Hn) as NR.
  ifF. zstep. ifF.
  do 2 zstep. ifT.
  zstep.
  call (get_current_thread_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [assumption| split; [assumption| split; assumption]]| assumption]. }
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  do 2 zstep. ifF.
  do 5 zstep.
  finish.
  - eexists. eassumption.
  - unfold alloc_frame64. replace (bv_unsigned sp + -128 + 8)%Z with (bv_unsigned sp + -120)%Z by lia. eassumption.
Qed.
