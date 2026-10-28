(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk Image SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanRehashModel AsanRegModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_arrkit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_ibase R_small R_cache_defs XR_rehash XR_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require FX_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma land_le_r : forall a b, 0 <= b -> Z.land a b <= b.
Proof.
  intros a b Hb.
  set (x := Z.land a b). set (y := Z.land (Z.lnot a) b).
  assert (D : Z.land x y = 0).
  { apply Z.bits_inj'. intros n Hn. subst x y. rewrite !Z.land_spec, Z.lnot_spec, Z.bits_0 by exact Hn.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  assert (E : Z.lor x y = b).
  { apply Z.bits_inj'. intros n Hn. subst x y. rewrite Z.lor_spec, !Z.land_spec, Z.lnot_spec by exact Hn.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  assert (S : x + y = b) by (rewrite (Z.add_nocarry_lxor _ _ D), (Z.lxor_lor _ _ D); exact E).
  assert (0 <= y) by (apply Z.land_nonneg; right; exact Hb). lia.
Qed.

Lemma land_mask_range : forall x N, 1 <= N -> 0 <= x -> 0 <= Z.land x (N - 1) < N.
Proof. intros x N HN Hx. split; [apply Z.land_nonneg; left; exact Hx|]. pose proof (land_le_r x (N - 1) ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma rgm_upd_eq : forall ks i v, RGM.upd ks i v = RHM.upd ks i v.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma probe_ins_range : forall fuel N ks key idx t p, 1 <= N -> 0 <= idx < N -> 0 <= t ->
  RGM.probe_ins N ks key idx t fuel = Some p -> 0 <= p < N.
Proof.
  induction fuel as [|f IH]; intros N ks key idx t p HN Hi Ht H; cbn [RGM.probe_ins] in H; [discriminate|].
  destruct (nth (Z.to_nat idx) ks 0 =? RGM.EMPTY); [injection H as <-; exact Hi|].
  destruct ((nth (Z.to_nat idx) ks 0 =? key) || (nth (Z.to_nat idx) ks 0 =? RGM.TOMB))%bool; [discriminate|].
  apply (IH N ks key (Z.land (idx + t) (N - 1)) (t + 1) p HN); [apply land_mask_range; lia| lia| exact H].
Qed.

Notation MAPA := 0x66a418%Z (only parsing).       (* [comment removed for export] *)

Section FAC.
Variables (B N key : Z).
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Hypothesis HN : 8 <= N <= 2 ^ 20.
Hypothesis B0 : 0 < B.
Hypothesis BT : B + 32 * N <= 2 ^ 47.
Hypothesis Hkey : 0 <= key < 2 ^ 64 - 2.

(* [comment removed for export] *)
Lemma fac_probe_loop : forall (fuel : nat) (idx t p : Z) (ks : list Z) (nws : list word) (m : mem) (ra sp' a0 a2 : word),
  RGM.probe_ins N ks key idx t fuel = Some p ->
  0 <= idx < N -> 1 <= t -> t + Z.of_nat fuel <= 2 ^ 22 ->
  nth (Z.to_nat idx) ks 0 <> key ->
  u64arr asegs m B nws -> keys_rep (Z.to_nat N) nws ks ->
  (forall e, 0 <= e < N -> 0 <= nth (Z.to_nat e) ks 0 < 2 ^ 64) ->
  mem_inv asegs m ->
  (forall a6' t1', 0 <= p < N -> nth (Z.to_nat p) ks 0 = RGM.EMPTY ->
     evt asegs Q (MS (mkR ra sp' gp tp (Z_to_bv 64 (-1)) t1' (Z_to_bv 64 RGM.EMPTY) s0 s1 a0 (Z_to_bv 64 (B + 32 * p)) a2
                          (Z_to_bv 64 key) (Z_to_bv 64 B) (Z_to_bv 64 (N - 1)) a6' (Z_to_bv 64 0)
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x1ab1d4) fc None m (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp' gp tp (Z_to_bv 64 (-1)) (Z_to_bv 64 t) (Z_to_bv 64 (nth (Z.to_nat idx) ks 0)) s0 s1 a0 (Z_to_bv 64 (B + 32 * idx)) a2
                       (Z_to_bv 64 key) (Z_to_bv 64 B) (Z_to_bv 64 (N - 1)) (Z_to_bv 64 idx) (Z_to_bv 64 0)
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x1ab20c) fc None m (seg_rom asegs)).
Proof.
  induction fuel as [|fuel IH]; intros idx t p ks nws m ra sp' a0 a2 PF Hidx Ht Hfu Hne ARR KR KD MI K; [cbn in PF; discriminate|].
  cbn [RGM.probe_ins] in PF.
  pose proof (KD idx Hidx) as Kr.
  remember (nth (Z.to_nat idx) ks 0) as kk eqn:Ekk.
  assert (EUk : bv_unsigned (Z_to_bv 64 kk) = kk) by (apply unsigned_lit; lia).
  assert (EUm1 : bv_unsigned (Z_to_bv 64 (-1)) = 18446744073709551615) by reflexivity.
  zstep. rewrite bv_eqb_Z, EUk, EUm1.
  destruct (Z.eqb_spec kk RGM.EMPTY) as [EE|NE].
  - injection PF as <-. change RGM.EMPTY with 18446744073709551615 in EE. rewrite (proj2 (Z.eqb_eq _ _) EE).
    zstep. ifT.
    rewrite EE. change 18446744073709551615 with RGM.EMPTY.
    apply K; [exact Hidx | rewrite <- Ekk; exact EE].
  - change RGM.EMPTY with 18446744073709551615 in NE. rewrite (proj2 (Z.eqb_neq _ _) NE).
    destruct ((kk =? key) || (kk =? RGM.TOMB))%bool eqn:EB; [discriminate|].
    apply orb_false_iff in EB as [_ Kt]. apply Z.eqb_neq in Kt. change RGM.TOMB with 18446744073709551614 in Kt.
    zstep. zstep.
    assert (XR : 0 <= Z.lxor kk 18446744073709551614 < 2 ^ 64) by (apply zr_lxor; unfold inr64; lia).
    assert (XN : Z.lxor kk 18446744073709551614 <> 0) by (intros E; apply (proj1 (zb_lxor_eq0 _ _)) in E; apply Kt; exact E).
    assert (EUx : bv_unsigned (Z_to_bv 64 (Z.lxor kk 18446744073709551614)) = Z.lxor kk 18446744073709551614) by (apply unsigned_lit; lia).
    zstep. ifF.
    zstep. zstep. zstep. zstep.
    set (idx' := Z.land (idx + t) (N - 1)) in *.
    assert (Hidx' : 0 <= idx' < N) by (apply land_mask_range; lia).
    assert (EUi : bv_unsigned (Z_to_bv 64 idx') = idx') by (apply unsigned_lit; lia).
    zstep. zstep. zstep.
    rewrite (scale32 idx') by lia.
    assert (Hn : nth_error nws (Z.to_nat (4 * idx')) = Some (Z_to_bv 64 (nth (Z.to_nat idx') ks 0))).
    { destruct KR as (_ & _ & KR). replace (Z.to_nat (4 * idx')) with (4 * Z.to_nat idx')%nat by lia. apply KR. lia. }
    pose proof (u64arr_read asegs m B nws (4 * idx') _ (Z_to_bv 64 (B + 32 * idx')) ARR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep.
    pose proof (KD idx' Hidx') as Kr'.
    assert (EUk' : bv_unsigned (Z_to_bv 64 (nth (Z.to_nat idx') ks 0)) = nth (Z.to_nat idx') ks 0) by (apply unsigned_lit; lia).
    assert (EUkey : bv_unsigned (Z_to_bv 64 key) = key) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    assert (Kk' : nth (Z.to_nat idx') ks 0 <> key).
    { destruct fuel as [|fuel']; [cbn in PF; discriminate|]. cbn [RGM.probe_ins] in PF. fold idx' in PF.
      destruct (nth (Z.to_nat idx') ks 0 =? RGM.EMPTY) eqn:E1.
      - apply Z.eqb_eq in E1. rewrite E1. unfold RGM.EMPTY. lia.
      - destruct ((nth (Z.to_nat idx') ks 0 =? key) || (nth (Z.to_nat idx') ks 0 =? RGM.TOMB))%bool eqn:E2; [discriminate|].
        apply orb_false_iff in E2 as [E2 _]. apply Z.eqb_neq in E2. exact E2. }
    zstep. rewrite bv_eqb_Z, EUkey, EUk'. rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym Kk')).
    zstep.
    apply (IH idx' (t + 1) p ks nws m ra sp' a0 a2 PF Hidx' ltac:(lia) ltac:(lia) Kk' ARR KR KD MI K).
Qed.

End FAC.

Ltac showpc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc" pc end.
Ltac showgoal := lazymatch goal with |- ?G => idtac G end.

Lemma fac_spec : forall (B N ne key p KSA SP RA : Z) (ks : list Z) (nws : list word)
    (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (m : mem),
  RGM.probe_ins N ks key (RGM.hash0 N key) 1 (Z.to_nat N) = Some p ->
  RGM.no_grow N ne = true ->
  8 <= N <= 2 ^ 20 -> 0 <= ne -> Forall (fun k => 0 <= k < 2 ^ 64) ks -> 0 <= key < 2 ^ 64 - 2 ->
  rw_cells asegs m KSA [C8 (Z_to_bv 64 key)] ->
  rw_cells asegs m MAPA [C8 (Z_to_bv 64 B); C4 (Z_to_bv 64 ne); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 N)] ->
  u64arr asegs m B nws -> keys_rep (Z.to_nat N) nws ks ->
  stk asegs m (SP - 32) SP ->
  0 < B -> B + 32 * N <= 2 ^ 47 -> (B + 32 * N <= 0x10000 \/ SEGTOP_A <= B) ->
  SEGTOP_A <= SP - 32 -> SP <= KSA -> KSA + 8 <= 2 ^ 47 ->
  (B + 32 * N <= SP - 32 \/ KSA + 8 <= B) ->
  0 <= RA < 2 ^ 47 -> RA mod 4 = 0 ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' : word) (nws' : list word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 SP) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (B + 32 * p)) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 RA) fc None m' (seg_rom asegs)
      /\ munch [(SP - 32, SP); (MAPA + 8, MAPA + 12); (B + 32 * p, B + 32 * p + 32)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' MAPA [C8 (Z_to_bv 64 B); C4 (Z_to_bv 64 (ne + 1)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 N)]
      /\ u64arr asegs m' B nws' /\ keys_rep (Z.to_nat N) nws' (RGM.upd ks (Z.to_nat p) key)
      /\ nth_error nws' (Z.to_nat (4 * p + 1)) = Some (Z_to_bv 64 0)
      /\ stk asegs m' (SP - 32) SP /\ 0 <= p < N)
    (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 MAPA) (Z_to_bv 64 KSA) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ab170) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros PI NG HN Hne KF Hkey KS MAP NA KR FRS B0 BT BI SPlo SPK KT APART HRA HRA4 MI.
  unfold SEGTOP_A in *.
  assert (KD : forall e, 0 <= e < N -> 0 <= nth (Z.to_nat e) ks 0 < 2 ^ 64).
  { intros e He. destruct KR as (_ & Lk & _). apply (proj1 (Forall_forall _ _) KF). apply nth_In. lia. }
  pose proof (munch_refl [(SP - 32, SP); (0x66a418 + 8, 0x66a418 + 12); (B + 32 * p, B + 32 * p + 32)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply unsigned_lit; lia).
  assert (HLn : length nws = (4 * Z.to_nat N)%nat) by (destruct KR as (L & _); exact L).
  assert (EUkey : bv_unsigned (Z_to_bv 64 key) = key) by (apply unsigned_lit; lia).
  carve_frame 16%nat FRS.
  zstep. zstep. zstep. rewrite (sx32_small_A N) by lia.
  zstep. zstep. ifF.
  zstep. zstep. zstep. ifF. zstep. zstep. ifF.
  zstep. zstep. zstep. zstep. zstep.
  replace (Z.land (Z.land (key * 37) 18446744073709551615) (N + -1)) with (RGM.hash0 N key)
    by (unfold RGM.hash0; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; f_equal; lia).
  set (h := RGM.hash0 N key) in *.
  assert (Hh : 0 <= h < N) by (unfold h, RGM.hash0; apply land_mask_range; [lia | apply Z.mod_pos_bound; lia]).
  assert (EUh : bv_unsigned (Z_to_bv 64 h) = h) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. rewrite (scale32 h) by lia.
  assert (Hn0 : nth_error nws (Z.to_nat (4 * h)) = Some (Z_to_bv 64 (nth (Z.to_nat h) ks 0))).
  { destruct KR as (_ & _ & KR'). replace (Z.to_nat (4 * h)) with (4 * Z.to_nat h)%nat by lia. apply KR'. lia. }
  pose proof (u64arr_read asegs m0 B nws (4 * h) _ (Z_to_bv 64 (B + 32 * h)) NA Hn0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD.
  (* [comment removed for export] *)
  assert (Kk0 : nth (Z.to_nat h) ks 0 <> key).
  { destruct (Z.to_nat N) as [|fuel'] eqn:EN; [lia|]. cbn [RGM.probe_ins] in PI. fold h in PI.
    destruct (nth (Z.to_nat h) ks 0 =? RGM.EMPTY) eqn:E1.
    - apply Z.eqb_eq in E1. rewrite E1. unfold RGM.EMPTY. lia.
    - destruct ((nth (Z.to_nat h) ks 0 =? key) || (nth (Z.to_nat h) ks 0 =? RGM.TOMB))%bool eqn:E2; [discriminate|].
      apply orb_false_iff in E2 as [E2 _]. apply Z.eqb_neq in E2. exact E2. }
  pose proof (KD h Hh) as Kr0.
  assert (EUk0 : bv_unsigned (Z_to_bv 64 (nth (Z.to_nat h) ks 0)) = nth (Z.to_nat h) ks 0) by (apply unsigned_lit; lia).
  zstep. rewrite bv_eqb_Z, EUkey, EUk0. rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym Kk0)). cbn [negb].
  zstep. zstep. zstep.
  lazymatch goal with |- evt asegs ?QQ _ =>
    apply (fac_probe_loop B N key gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc QQ HN B0 BT Hkey
             (Z.to_nat N) h 1 p ks nws m0 _ _ _ _ PI Hh ltac:(lia) ltac:(lia) Kk0 NA KR KD ltac:(assumption)) end.
  intros a6' t1' Hp EEp.
  zstep. zstep.
  replace (SP + -16 + 16) with SP by lia.
  release_frame FR FRS SP.
  zstep.
  carve_frame 32%nat FRS.
  zstep. zstep. zstep. zstep.
  zstep. rewrite (sx32_small_A ne) by (unfold RGM.no_grow in NG; lia).
  zstep. rewrite (sx32_small_A N) by lia.
  assert (NG1 : 4 * (ne + 1) < 3 * N /\ N / 8 < N - (ne + 1)).
  { unfold RGM.no_grow in NG. apply andb_prop in NG as [G1 G2]. apply Z.ltb_lt in G1, G2. split; assumption. }
  assert (L1 : Z.land ne 18446744073709551615 = ne) by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite ?L1. rewrite (Z.shiftl_mul_pow2 ne 2) by lia. rewrite (Z.shiftl_mul_pow2 N 1) by lia.
  replace (Z.land (ne * 2 ^ 2) 18446744073709551615) with (4 * ne)
    by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; lia).
  rewrite (SysStep.swrap32_small (4 * ne + 4)) by lia.
  rewrite (SysStep.swrap32_small (N * 2 ^ 1)) by lia.
  replace (Z.land (N * 2 ^ 1) 18446744073709551615) with (2 * N)
    by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; lia).
  rewrite (SysStep.swrap32_small (2 * N + N)) by lia.
  ifF.
  zstep. zstep. zstep. zstep. zstep. zstep.
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.sub_0_r.
  rewrite (SysStep.swrap32_small N) by lia.
  replace (Z.land N 18446744073709551615) with N
    by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
  rewrite (zb_lxor_ones ne) by lia.
  replace (bv_swrap 32 (N + (18446744073709551615 - ne))) with (N - ne - 1)
    by (rewrite FX_lib.swrap32_eq; replace (N + (18446744073709551615 - ne) + 2147483648) with ((N - ne - 1 + 2147483648) + 4294967296 * 4294967296) by lia;
        rewrite Z.mod_add by lia; rewrite Z.mod_small by lia; lia).
  replace (bv_swrap 32 (bv_wrap 32 N ≫ 3)) with (N / 8)
    by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; rewrite (Z.mod_small N) by lia; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
        rewrite SysStep.swrap32_small by (Z.div_mod_to_equations; lia); reflexivity).
  ifF.
  assert (EUbk : bv_unsigned (Z_to_bv 64 (B + 32 * p)) = B + 32 * p) by (apply unsigned_lit; lia).
  zstep. ifF.
  zstep. rewrite (sx32_small_A ne) by lia.
  assert (Hnp : nth_error nws (Z.to_nat (4 * p)) = Some (Z_to_bv 64 (nth (Z.to_nat p) ks 0))).
  { destruct KR as (_ & _ & KR'). replace (Z.to_nat (4 * p)) with (4 * Z.to_nat p)%nat by lia. apply KR'. lia. }
  lazymatch goal with NAx : u64arr asegs ?mm B nws |- _ =>
    pose proof (u64arr_read asegs mm B nws (4 * p) _ (Z_to_bv 64 (B + 32 * p)) NAx Hnp ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  zstep. clear RD. rewrite EEp.
  zstep. zstep. zstep.
  zstep. change (bv_eqb (Z_to_bv 64 RGM.EMPTY) (Z_to_bv 64 (-1))) with true. cbv iota.
  zstep.
  (* [comment removed for export] *)
  lazymatch goal with NAx : u64arr asegs ?mm B ?xs |- _ =>
    pose proof (u64arr_store_ok asegs mm B _ (4 * p + 1) (wa (B + 8 * (4 * p + 1))) NAx ltac:(rewrite ?upd_length, HLn; lia) eq_refl) as SOK;
    pose proof (u64arr_write asegs mm B _ (4 * p + 1) (Z_to_bv 64 0) NAx ltac:(rewrite ?upd_length, HLn; lia)) as NA1 end.
  replace (B + 8 * (4 * p + 1)) with (B + 32 * p + 8) in SOK, NA1 by lia.
  zstep. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). clear NA. store_done.
  lazymatch goal with NAx : u64arr asegs ?mm B ?xs |- _ =>
    pose proof (u64arr_store_ok asegs mm B _ (4 * p) (wa (B + 8 * (4 * p))) NAx ltac:(rewrite ?upd_length, HLn; lia) eq_refl) as SOK;
    pose proof (u64arr_write asegs mm B _ (4 * p) (Z_to_bv 64 key) NAx ltac:(rewrite ?upd_length, HLn; lia)) as NA2 end.
  replace (B + 8 * (4 * p)) with (B + 32 * p) in SOK, NA2 by lia.
  zstep. clear NA1. store_done.
  lazymatch goal with NAx : u64arr asegs ?mm B ?xs |- _ =>
    pose proof (u64arr_store_ok asegs mm B _ (4 * p + 2) (wa (B + 8 * (4 * p + 2))) NAx ltac:(rewrite ?upd_length, HLn; lia) eq_refl) as SOK;
    pose proof (u64arr_write asegs mm B _ (4 * p + 2) (Z_to_bv 64 0) NAx ltac:(rewrite ?upd_length, HLn; lia)) as NA3 end.
  replace (B + 8 * (4 * p + 2)) with (B + 32 * p + 16) in SOK, NA3 by lia.
  zstep. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). clear NA2. store_done.
  lazymatch goal with NAx : u64arr asegs ?mm B ?xs |- _ =>
    pose proof (u64arr_store_ok asegs mm B _ (4 * p + 3) (wa (B + 8 * (4 * p + 3))) NAx ltac:(rewrite ?upd_length, HLn; lia) eq_refl) as SOK;
    pose proof (u64arr_write asegs mm B _ (4 * p + 3) (Z_to_bv 64 0) NAx ltac:(rewrite ?upd_length, HLn; lia)) as NA4 end.
  replace (B + 8 * (4 * p + 3)) with (B + 32 * p + 24) in SOK, NA4 by lia.
  zstep. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). clear NA3. store_done.
  zstep. zstep. zstep. zstep. zstep.
  replace (SP + -32 + 32) with SP by lia.
  release_frame FR FRS SP.
  zstep.
  rewrite (ret_pc_even RA) by (try lia; Z.div_mod_to_equations; lia).
  apply evt_done.
  do 10 eexists. eexists (upd (upd (upd (upd nws (Z.to_nat (4 * p + 1)) (Z_to_bv 64 0)) (Z.to_nat (4 * p)) (Z_to_bv 64 key))
                                 (Z.to_nat (4 * p + 2)) (Z_to_bv 64 0)) (Z.to_nat (4 * p + 3)) (Z_to_bv 64 0)).
  eexists.
  split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
  split; [exact WM|]. split; [assumption|]. split; [exact MAP|]. split; [exact NA4|].
  split.
  { rewrite rgm_upd_eq. do 2 (apply keys_rep_set_val; [| apply mod4_ne; lia]).
    replace (Z.to_nat (4 * p)) with (4 * Z.to_nat p)%nat by lia. apply keys_rep_set_key; [| lia].
    apply keys_rep_set_val; [exact KR| apply mod4_ne; lia]. }
  split.
  { rewrite nth_error_upd_other by lia. rewrite nth_error_upd_other by lia. rewrite nth_error_upd_other by lia.
    apply nth_error_upd_same. rewrite HLn. lia. }
  split; [replace (SP - 32) with (SP + -32) by lia; exact FRS| exact Hp].
Qed.
