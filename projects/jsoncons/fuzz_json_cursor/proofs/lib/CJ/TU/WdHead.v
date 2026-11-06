(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge FP.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require Import BrMem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.TU Require Import DgWalk G3Lem PbWalk G3Walk.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition dpc (len K : Z) : Z :=
  if (K <? 0)%Z then (if (0 <? len + K)%Z then (if (len + K <=? 17)%Z then 0x42aac else 0x42b80) else (if (len + K <=? -4)%Z then 0x42b80 else 0x42af8))
  else (if (len + K <=? 17)%Z then 0x42a38 else 0x42b80).

Lemma u8arr_rw : forall m A bs, u8arr rsegs m A bs -> rw_cells rsegs m A [CB (length bs) bs].
Proof.
  intros m A bs [Hb Hw]. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Ltac fix_lit8 := lazymatch goal with |- context [write_to_mem _ _ (Z_to_le_bytes 8 ?n)] => change (Z_to_le_bytes 8 n) with (le8 (Z_to_bv 64 n)) end.
Ltac lstep := step; fix_lit8; mem_after_store.

Lemma swrap32_small' : forall x, (- 2 ^ 31 <= x < 2 ^ 31)%Z -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma swrap32_mod' : forall x k, bv_swrap 32 (x + k * 2 ^ 32) = bv_swrap 32 x.
Proof.
  intros x k. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow].
  replace (x + k * 2 ^ 32 + 2 ^ 32 / 2)%Z with ((x + 2 ^ 32 / 2) + k * 2 ^ 32)%Z by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma modneg64 : forall K, (-343 <= K < 0)%Z -> (K mod 2 ^ 64 = K + 2 ^ 64)%Z.
Proof. intros K HK. symmetry. apply (Z.mod_unique K (2 ^ 64) (-1) (K + 2 ^ 64)); lia. Qed.
Lemma modpos64 : forall K, (0 <= K < 2 ^ 64)%Z -> (K mod 2 ^ 64 = K)%Z.
Proof. intros K HK. apply Z.mod_small. lia. Qed.

Lemma addw_small : forall K len, (-343 <= K <= 309)%Z -> (1 <= len <= 21)%Z -> bv_swrap 32 (K mod 2 ^ 64 + len) = (len + K)%Z.
Proof.
  intros K len HK Hl. destruct (Z_lt_ge_dec K 0) as [Hn|Hp].
  - rewrite (modneg64 K ltac:(lia)).
    replace (K + 2 ^ 64 + len)%Z with ((len + K) + 4294967296 * 2 ^ 32)%Z by lia. rewrite swrap32_mod'. apply swrap32_small'. lia.
  - rewrite Z.mod_small by lia. replace (K + len)%Z with (len + K)%Z by lia. apply swrap32_small'. lia.
Qed.
Lemma modnegL : forall K, (-343 <= K < 0)%Z -> (K mod 18446744073709551616 = K + 18446744073709551616)%Z.
Proof. intros K HK. exact (modneg64 K HK). Qed.
Lemma modposL : forall K, (0 <= K < 18446744073709551616)%Z -> (K mod 18446744073709551616 = K)%Z.
Proof. intros K HK. apply Z.mod_small. lia. Qed.
Lemma dpc_C1 : forall len K, (0 <= K)%Z -> (len + K <= 17)%Z -> dpc len K = 0x42a38%Z.
Proof. intros len K H1 H2. unfold dpc. destruct (Z.ltb_spec K 0); [lia|]. destruct (Z.leb_spec (len + K) 17); [reflexivity | lia]. Qed.
Lemma dpc_C2 : forall len K, (K < 0)%Z -> (0 < len + K <= 17)%Z -> dpc len K = 0x42aac%Z.
Proof. intros len K H1 H2. unfold dpc. destruct (Z.ltb_spec K 0); [|lia]. destruct (Z.ltb_spec 0 (len + K)); [|lia]. destruct (Z.leb_spec (len + K) 17); [reflexivity | lia]. Qed.
Lemma dpc_C3 : forall len K, (K < 0)%Z -> (-4 < len + K <= 0)%Z -> dpc len K = 0x42af8%Z.
Proof. intros len K H1 H2. unfold dpc. destruct (Z.ltb_spec K 0); [|lia]. destruct (Z.ltb_spec 0 (len + K)); [lia|]. destruct (Z.leb_spec (len + K) (-4)); [lia | reflexivity]. Qed.
Lemma dpc_C45 : forall len K, (1 <= len)%Z -> (0 <= K \/ K < 0)%Z -> (17 < len + K \/ len + K <= -4)%Z -> dpc len K = 0x42b80%Z.
Proof.
  intros len K H0 _ H. unfold dpc. destruct (Z.ltb_spec K 0); [destruct (Z.ltb_spec 0 (len + K)); [destruct (Z.leb_spec (len + K) 17); [lia | reflexivity] | destruct (Z.leb_spec (len + K) (-4)); [reflexivity | lia]] |].
  destruct (Z.leb_spec (len + K) 17); [lia | reflexivity].
Qed.

Lemma sgn64 : forall x, (- 2 ^ 63 <= x < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 x) = x.
Proof. intros x Hx. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 64 / 2)%Z with (2 ^ 63)%Z. lia. Qed.
Ltac scond0 H := unfold bv_lts in H; rewrite ?sgn64 in H by lia; first [apply Z.ltb_lt in H | apply Z.ltb_ge in H].
Ltac scond H := lazymatch type of H with
  | negb (bv_lts _ _) = true => apply Bool.negb_true_iff in H; scond0 H
  | negb (bv_lts _ _) = false => apply Bool.negb_false_iff in H; scond0 H
  | bv_lts _ _ = _ => scond0 H
  end.

Lemma fabs_pos : forall a : word, feq_d a (Z_to_bv 64 0) = false -> (1 <= bv_unsigned (fabs_d a) < 2 ^ 63)%Z.
Proof.
  intros a H. unfold fabs_d. pose proof (bv_unsigned_in_range _ a) as Ra. unfold bv_modulus in Ra. cbn -[Z.pow] in Ra.
  assert (Hl : Z.land (bv_unsigned a) (Z.ones 63) = (bv_unsigned a mod 2 ^ 63)%Z) by (apply Z.land_ones; lia).
  rewrite Hl. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned a) (2 ^ 63)); lia).
  pose proof (Z.mod_pos_bound (bv_unsigned a) (2 ^ 63) ltac:(lia)) as Rm. split; [|lia].
  destruct (Z.eq_dec (bv_unsigned a mod 2 ^ 63) 0) as [E|E]; [|lia]. exfalso.
  assert (Ha : bv_unsigned a = 0%Z \/ bv_unsigned a = (2 ^ 63)%Z).
  { pose proof (Z.div_mod (bv_unsigned a) (2 ^ 63) ltac:(lia)) as D. rewrite E in D.
    assert (Q : (0 <= bv_unsigned a / 2 ^ 63 < 2)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). nia. }
  assert (Ea : a = Z_to_bv 64 (bv_unsigned a)) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct Ha as [Ha|Ha]; rewrite Ea, Ha in H; vm_compute in H; discriminate H.
Qed.
Lemma cb4_c4 : forall m A bs, rw_cells rsegs m A [CB 4 bs] -> exists w, rw_cells rsegs m A [C4 w].
Proof.
  intros m A bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hn _].
  destruct bs as [|b0 [|b1 [|b2 [|b3 [|? ?]]]]]; cbn in Hn; try lia.
  destruct (le4_of_bytes b0 b1 b2 b3) as (w & Hw4). exists w. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite Hw4. exact Hb.
  - exact Hw.
Qed.
Ltac peel H := lazymatch type of H with rw_cells _ ?m ?A (?c :: ?rest) =>
  let H1 := fresh "PC" in
  change (c :: rest) with ([c] ++ rest) in H; apply (proj1 (rw_cells_app m A [c] rest)) in H; destruct H as [H1 H]; cbn [cells_size csize Nat.add] in H end.
Lemma rw_glue : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 -> B = (A + Z.of_nat (cells_size cs1))%Z ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 H1 H2 ->. apply rw_cells_app. split; assumption. Qed.
Ltac exs := repeat (lazymatch goal with |- ex _ => eexists end).
Ltac mods := repeat match goal with
  | H : context [bv_signed (Z_to_bv 64 ?x)] |- _ => rewrite (sgn64 x) in H by lia
  | H : context [(?x mod 18446744073709551616)%Z] |- _ => first [rewrite (modposL x) in H by lia | rewrite (modnegL x) in H by lia]
  end.

Section WH.

Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable SP : Z.
Variables wd o dp : Z.
Variable m0 : word -> option byte.
Definition SPB : Z := (SP - 400)%Z.
Hypothesis SPR : (2 ^ 41 + 9600 <= SP /\ SP <= 2 ^ 47)%Z.
Hypothesis ORNG : (SP <= o /\ o + 24 <= 2 ^ 47)%Z.
Hypothesis DPR : (0 <= dp < 256)%Z.
Definition WH_W : list (Z * Z) := [(SP - 9600, SP); (o, o + 24)]%Z.

Definition FRC (j1 j2 dig j3 : list byte) (K len : Z) (fs0w : word) : list cell :=
  [CB 8 j1; C8 s5; C8 s4; C8 s3; C8 s2; C8 (Z_to_bv 64 dp); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 0x433a4);
   CB 4 j2; CB 100 dig; C4 (Z_to_bv 64 K); C4 (Z_to_bv 64 len); C8 fs0w; C8 (Z_to_bv 64 wd); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 0x41e84);
   CB 232 j3; C8 s1; C8 s0; C8 ra].

Definition FRD (j2 dig j3 : list byte) (kw lw : word) (fs0w : word) : list cell :=
  [CB 4 j2; CB 100 dig; C4 kw; C4 lw; C8 fs0w; C8 (Z_to_bv 64 wd); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 0x41e84);
   CB 232 j3; C8 s1; C8 s0; C8 ra].

Definition wpC : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a6' a7' t3' t4' t5' t6' F' fc' m' (len K n0 : Z) fs0w (j1 j2 dig j3 bs : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x433a4) (Z_to_bv 64 (SPB - 64)) gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 len)
                  (Z_to_bv 64 (SPB + 4)) (Z_to_bv 64 len) (Z_to_bv 64 K) (Z_to_bv 64 (-4)) (Z_to_bv 64 17) (Z_to_bv 64 o) a6' a7'
                  (Z_to_bv 64 (SPB + 4)) (Z_to_bv 64 K) (Z_to_bv 64 (len + K)) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 (dpc len K)) fc' None m' (seg_rom rsegs)
    /\ (1 <= len <= 21)%Z /\ (-343 <= K <= 309)%Z /\ frm0 fc'
    /\ rw_cells rsegs m' (SPB - 64) (FRC j1 j2 dig j3 K len fs0w)
    /\ u8arr rsegs m' o bs /\ length bs = 24%nat /\ nth_error bs 0 = Some (Z_to_bv 8 (2 * n0)) /\ (n0 = 0 \/ n0 = 1)%Z
    /\ stk rsegs m' (SP - 9600) (SPB - 64)
    /\ munch WH_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'.

Definition FRF (jf txt : list byte) (fs0b : word) (j2 dig j3 : list byte) (kw lw fs0w : word) : list cell :=
  [CB 12 jf; CB 100 txt; C8 fs0b; C8 s3; C8 s2; C8 (Z_to_bv 64 dp); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 0x433d4)] ++ FRD j2 dig j3 kw lw fs0w.

Definition estr (bs : list byte) : Prop := length bs = 24%nat /\ nth_error bs 0 = Some (Z_to_bv 8 0) /\ nth_error bs 1 = Some (Z_to_bv 8 0).

Definition wpA2 : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' fs0b fs0w kw lw (jf txt j2 dig j3 bs : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x433d4) (Z_to_bv 64 (SPB - 160)) gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 dp)
                  (Z_to_bv 64 dp) (Z_to_bv 64 1) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 0x43404) fc' None m' (seg_rom rsegs)
    /\ frm0 fc' /\ rw_cells rsegs m' (SPB - 160) (FRF jf txt fs0b j2 dig j3 kw lw fs0w)
    /\ u8arr rsegs m' o bs /\ estr bs /\ stk rsegs m' (SP - 9600) (SPB - 160)
    /\ munch WH_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'.

Definition wpSN : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F' fc' m' fs0b fs0w kw lw bits (jf txt j2 dig j3 bs : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x43458) (Z_to_bv 64 (SPB - 160)) gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 dp)
                  (Z_to_bv 64 (SPB - 148)) (Z_to_bv 64 100) (Z_to_bv 64 0x130d8) (Z_to_bv 64 15) bits a5' a6' a7'
                  bits s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 0xaaeb4) fc' None m' (seg_rom rsegs)
    /\ frm0 fc' /\ rw_cells rsegs m' (SPB - 160) (FRF jf txt fs0b j2 dig j3 kw lw fs0w)
    /\ u8arr rsegs m' o bs /\ estr bs /\ stk rsegs m' (SP - 9600) (SPB - 160)
    /\ munch WH_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'.

Lemma wh_false : forall rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (m : word -> option byte) kw lw fs0w (j2 dig j3 bs : list byte),
  frm0 fc -> rw_cells rsegs m SPB (FRD j2 dig j3 kw lw fs0w) -> u8arr rsegs m o bs -> estr bs ->
  stk rsegs m (SP - 9600) SPB -> munch WH_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs (fun ms => wpA2 ms \/ wpSN ms)
            (MS (mkR rav (Z_to_bv 64 SPB) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 dp) a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x433c0) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros FRM FR BU ES ST MU WM MI.
  unfold SPB in *. unfold WH_W in MU. unfold FRD in FR.
  do 5 zstep.
  carve_frame 160%nat ST.
  replace (SP + -400 + -160)%Z with (SP + -560)%Z in ST, FR0 by lia.
  zstep. lstep.
  do 5 zstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (FRF_ok : forall jj fb, rw_cells rsegs mm (SP + -560) (CB 112 jj :: [C8 fb; C8 s3; C8 s2; C8 (Z_to_bv 64 dp); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 275412)]) ->
                          rw_cells rsegs mm (SPB - 160) (FRF (firstn 12 jj) (firstn 100 (skipn 12 jj)) fb j2 dig j3 kw lw fs0w));
  [ intros jj fb H1; unfold FRF, FRD, SPB; replace (SP - 400 - 160)%Z with (SP + -560)%Z by lia;
    apply rw_cells_app; split;
    [ apply (rw_cells_split_CB rsegs mm (SP + -560) [] 112 jj _ [12; 100]%nat) in H1; [exact H1 | reflexivity]
    | cbn [cells_size csize Nat.add]; replace (SP + -560 + Z.of_nat 160)%Z with (SP + -400)%Z by lia; exact FR ] | ];
  assert (ST1 : stk rsegs mm (SP - 9600) (SPB - 160)) by (unfold SPB; replace (SP - 400 - 160)%Z with (SP + -560)%Z by lia; exact ST)
  end.
  lazymatch goal with FR0 : rw_cells _ _ _ (CB 112 ?j :: C8 ?fb :: _) |- _ => pose proof (FRF_ok j fb FR0) as FRF1; clear FR0 end.
  clear FRF_ok FR ST.
  do 3 zstep.
  zstep. destruct (feq_d (reg_get F 8) (Z_to_bv 64 0)) eqn:FQ; cbn [bword] in *.
  -
    if_cases K1; [vm_compute in K1; discriminate|].
    replace (Z_to_bv 64 (SP + -560)) with (Z_to_bv 64 (SPB - 160)) by (unfold SPB; f_equal; lia).
    apply evt_done. left. unfold wpA2. exs. split; [reflexivity|].
    split; [exact FRM|]. split; [exact FRF1|]. split; [exact BU|]. split; [exact ES|]. split; [exact ST1|].
    split; [unfold WH_W; exact MU|]. split; [exact WM | exact MI].
  -
    if_cases K1; [|vm_compute in K1; discriminate].
    do 10 zstep.
    replace (Z_to_bv 64 (SP + -560)) with (Z_to_bv 64 (SPB - 160)) by (unfold SPB; f_equal; lia).
    replace (Z_to_bv 64 (SP + -548)) with (Z_to_bv 64 (SPB - 148)) by (unfold SPB; f_equal; lia).
    apply evt_done. right. unfold wpSN. exs. split; [reflexivity|].
    split; [exact FRM|]. split; [exact FRF1|]. split; [exact BU|]. split; [exact ES|]. split; [exact ST1|].
    split; [unfold WH_W; exact MU|]. split; [exact WM | exact MI].
Qed.

Lemma wh_pret : forall rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (m : word -> option byte) (len K n0 : Z) fs0w (j2 dig j3 bs : list byte),
  frm0 fc -> (1 <= len <= 21)%Z -> (-343 <= K <= 309)%Z -> (n0 = 0 \/ n0 = 1)%Z ->
  rw_cells rsegs m SPB (FRD j2 dig j3 (Z_to_bv 64 K) (Z_to_bv 64 len) fs0w) ->
  u8arr rsegs m o bs -> length bs = 24%nat -> nth_error bs 0 = Some (Z_to_bv 8 (2 * n0)) ->
  stk rsegs m (SP - 9600) SPB ->
  munch WH_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs wpC (MS (mkR rav (Z_to_bv 64 SPB) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 dp) a0 a1 a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x43388) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros FRM Hlen HK Hn0 FR BU BL B0 ST MU WM MI.
  unfold SPB in *. unfold WH_W in MU. unfold FRD in FR.

  zstep. zstep.
  rewrite !sx32_small by lia.
  do 5 zstep.
  carve_frame 64%nat ST.
  replace (SP + -400 + -64)%Z with (SP + -464)%Z in ST, FR0 by lia.
  zstep. lstep.
  do 6 zstep.
  do 5 zstep.
  replace (bv_swrap 32 (K mod 18446744073709551616 + len)) with (len + K)%Z by (symmetry; exact (addw_small K len HK Hlen)).
  assert (FRC_ok : forall j1, rw_cells rsegs m1 (SP + -464) (CB 8 j1 :: [C8 s5; C8 s4; C8 s3; C8 s2; C8 (Z_to_bv 64 dp); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 275364)]) ->
                          rw_cells rsegs m1 (SPB - 64) (FRC j1 j2 dig j3 K len fs0w)).
  { intros j1 H1. unfold FRC, SPB. replace (SP - 400 - 64)%Z with (SP + -464)%Z by lia.
    change (CB 8 j1 :: [C8 s5; C8 s4; C8 s3; C8 s2; C8 (Z_to_bv 64 dp); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 275364);
            CB 4 j2; CB 100 dig; C4 (Z_to_bv 64 K); C4 (Z_to_bv 64 len); C8 fs0w; C8 (Z_to_bv 64 wd); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 269956);
            CB 232 j3; C8 s1; C8 s0; C8 ra])
      with ((CB 8 j1 :: [C8 s5; C8 s4; C8 s3; C8 s2; C8 (Z_to_bv 64 dp); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 275364)])
            ++ [CB 4 j2; CB 100 dig; C4 (Z_to_bv 64 K); C4 (Z_to_bv 64 len); C8 fs0w; C8 (Z_to_bv 64 wd); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 269956);
                CB 232 j3; C8 s1; C8 s0; C8 ra]).
    apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. replace (SP + -464 + Z.of_nat 64)%Z with (SP + -400)%Z by lia. exact FR. }
  lazymatch type of FR0 with rw_cells _ _ _ (CB 8 ?j :: _) => pose proof (FRC_ok j FR0) as FRC1 end.
  clear FRC_ok FR FR0.
  assert (ST1 : stk rsegs m1 (SP - 9600) (SPB - 64)) by (unfold SPB; replace (SP - 400 - 64)%Z with (SP + -464)%Z by lia; exact ST). clear ST.
  Ltac fin_c FRC1 ST1 := try replace (Z_to_bv 64 (SP + -464)) with (Z_to_bv 64 (SPB - 64)) by (unfold SPB; f_equal; lia);
    try replace (Z_to_bv 64 (SP + -396)) with (Z_to_bv 64 (SPB + 4)) by (unfold SPB; f_equal; lia);
    finish; try unfold WH_W in *;
    match goal with
    | H : u8arr _ ?m ?a _ |- u8arr _ ?m ?a _ => exact H
    | H : length _ = _ |- length _ = _ => exact H
    | H : nth_error _ 0 = _ |- nth_error _ 0 = _ => exact H
    | H : rw_cells _ _ _ _ |- rw_cells _ _ _ _ => exact H
    | H : stk _ _ _ _ |- stk _ _ _ _ => exact H
    | H : ?P |- ?P => exact H
    | |- _ => lia
    end.
  zstep. if_cases K1; scond K1.
  -
    zstep. if_cases K2; scond K2.
    +
      zstep. if_cases K3; scond K3.
      *
        replace (Z_to_bv 64 273280) with (Z_to_bv 64 (dpc len K)) by (rewrite dpc_C45 by lia; reflexivity).
        fin_c FRC1 ST1.
      * zstep. if_cases K4; scond K4; [exfalso; lia|].
        replace (Z_to_bv 64 273144) with (Z_to_bv 64 (dpc len K)) by (rewrite dpc_C3 by lia; reflexivity).
        fin_c FRC1 ST1.
    +
      zstep. if_cases K3; scond K3.
      *
        zstep. if_cases K4; scond K4; [exfalso; lia|].
        zstep. if_cases K5; scond K5; [|exfalso; lia].
        replace (Z_to_bv 64 273280) with (Z_to_bv 64 (dpc len K)) by (rewrite dpc_C45 by lia; reflexivity).
        fin_c FRC1 ST1.
      * replace (Z_to_bv 64 273068) with (Z_to_bv 64 (dpc len K)) by (rewrite dpc_C2 by lia; reflexivity).
        fin_c FRC1 ST1.
  -
    zstep. if_cases K2; scond K2.
    +
      zstep. if_cases K3; scond K3; [exfalso; lia|].
      zstep. if_cases K4; scond K4; [|exfalso; lia].
      zstep. if_cases K5; scond K5; [exfalso; lia|].
      zstep. if_cases K6; scond K6; [|exfalso; lia].
      replace (Z_to_bv 64 273280) with (Z_to_bv 64 (dpc len K)) by (rewrite dpc_C45 by lia; reflexivity).
      fin_c FRC1 ST1.
    + replace (Z_to_bv 64 272952) with (Z_to_bv 64 (dpc len K)) by (rewrite dpc_C1 by lia; reflexivity).
      fin_c FRC1 ST1.
Qed.

Lemma wh_sign : forall rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (m : word -> option byte) (len K : Z) fs0w (j2 dig j3 bs : list byte),
  frm0 fc -> (1 <= len <= 21)%Z -> (-343 <= K <= 309)%Z ->
  rw_cells rsegs m SPB (FRD j2 dig j3 (Z_to_bv 64 K) (Z_to_bv 64 len) fs0w) -> u8arr rsegs m o bs -> estr bs ->
  stk rsegs m (SP - 9600) SPB -> munch WH_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs wpC (MS (mkR rav (Z_to_bv 64 SPB) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 dp) a0 a1 a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x43374) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros FRM Hlen HK FR BU [BL [B0 _]] ST MU WM MI.
  do 2 zstep. if_cases K1.
  -
    eapply (wh_pret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m len K 0 fs0w j2 dig j3 bs); try eassumption; try lia.
  -
    do 3 zstep.
    assert (SPBr : (bv_unsigned (Z_to_bv 64 SPB) = SPB)%Z) by (unfold SPB; apply unsigned_lit; lia).
    destruct (stk_split rsegs m (SP - 9600) (SPB - 64) SPB ST ltac:(unfold SPB; lia)) as [STlo SThi].
    eapply evt_cut.
    { eapply (pb_inplace (Z_to_bv 64 0x43388) (Z_to_bv 64 SPB) gp tp (Z_to_bv 64 o) (Z_to_bv 64 dp) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m o)
        with (n := 0%Z) (c := Z_to_bv 8 45) (bs := bs);
        unfold PSP; rewrite ?SPBr; try (unfold SPB; lia); try eassumption; try reflexivity. }
    cbv beta. intros ms' P. unfold pb_post, PB_W, PSP in P. rewrite SPBr in P.
    destruct P as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & BU2).
    replace (ret_pc (Z_to_bv 64 0x43388)) with (Z_to_bv 64 0x43388) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    clear ST BU. unfold WH_W in MU. unfold FRD in FR. unfold SPB in *.
    transport_after_call rsegs m m2 MUc WMc. clear MUc WMc. fold SPB in *.
    assert (ST3 : stk rsegs m2 (SP - 9600) SPB) by (apply (stk_merge rsegs m2 (SP - 9600) (SPB - 64) SPB); [assumption | exact ST2 | unfold SPB; lia]).
    clear ST2.
    lazymatch type of BU2 with u8arr _ _ _ ?bs2 =>
      assert (BL2 : length bs2 = 24%nat) by (rewrite !upd_length; exact BL);
      assert (B02 : nth_error bs2 0 = Some (Z_to_bv 8 (2 * 1))) by
        (rewrite nth_error_upd_other by (cbn; lia); rewrite nth_error_upd_other by (cbn; lia); rewrite nth_error_upd_same by lia; reflexivity)
    end.
    replace (Z_to_bv 64 (SP - 400)) with (Z_to_bv 64 SPB) by reflexivity.
    eapply (wh_pret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 len K 1 fs0w j2 dig j3); try eassumption; try lia.
    all: unfold WH_W, FRD, SPB; try assumption.
Qed.

Definition FRA (ja : list byte) (fs0w : word) (j3 : list byte) : list cell :=
  [CB 112 ja; C8 fs0w; C8 (Z_to_bv 64 wd); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 0x41e84); CB 232 j3; C8 s1; C8 s0; C8 ra].
Definition wpA : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' fs0w (ja j3 bs : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x41e84) (Z_to_bv 64 SPB) gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 wd)
                  (Z_to_bv 64 dp) (Z_to_bv 64 1) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 0x43328) fc' None m' (seg_rom rsegs)
    /\ frm0 fc' /\ rw_cells rsegs m' SPB (FRA ja fs0w j3)
    /\ u8arr rsegs m' o bs /\ estr bs /\ stk rsegs m' (SP - 9600) SPB
    /\ munch WH_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'.
Definition wpost (ms : machine_state) : Prop := wpA ms \/ wpA2 ms \/ wpC ms \/ wpSN ms.

Lemma wh_g3ret : forall rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (m : word -> option byte) (res len K : Z) fs0w (j2 dig j3 bs : list byte),
  frm0 fc -> (res = 0 \/ res = 1)%Z -> (1 <= len <= 21)%Z -> (-343 <= K <= 309)%Z ->
  rw_cells rsegs m SPB (FRD j2 dig j3 (Z_to_bv 64 K) (Z_to_bv 64 len) fs0w) -> u8arr rsegs m o bs -> estr bs ->
  stk rsegs m (SP - 9600) SPB -> munch WH_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs wpost (MS (mkR rav (Z_to_bv 64 SPB) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 dp) (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x43370) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros FRM Hres Hlen HK FR BU ES ST MU WM MI.
  zstep. if_cases K1.
  -
    assert (res = 0)%Z by (destruct Hres as [->| ->]; [reflexivity | vm_compute in K1; discriminate]). subst res.
    eapply evt_mono; [eapply (wh_false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m); eassumption|].
    intros ms' [P|P]; unfold wpost; [right; left; exact P | right; right; right; exact P].
  - assert (res = 1)%Z by (destruct Hres as [->| ->]; [vm_compute in K1; discriminate | reflexivity]). subst res.
    eapply evt_mono; [eapply (wh_sign _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m len K); eassumption|].
    intros ms' P; unfold wpost; right; right; left; exact P.
Qed.

Lemma wh_true : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (m : word -> option byte) (j3 bs : list byte),
  frm0 fc -> rw_cells rsegs m (SP - 256) [CB 232 j3; C8 s1; C8 s0; C8 ra] -> u8arr rsegs m o bs -> estr bs ->
  stk rsegs m (SP - 9600) (SP - 256) -> munch WH_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs wpost (MS (mkR (Z_to_bv 64 0x41e84) (Z_to_bv 64 (SP - 256)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 wd)
                           (Z_to_bv 64 dp) (Z_to_bv 64 o) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x43304) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros FRM FW BU ES ST MU WM MI.
  unfold WH_W in MU.
  carve_frame 144%nat ST.
  replace (SP + -256 + -144)%Z with (SP + -400)%Z in ST, FR by lia.
  zstep. lstep.
  do 3 zstep.
  do 3 zstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of FR with rw_cells _ _ _ (CB 112 ?jj :: C8 ?fw :: _) =>
      assert (FRA1 : rw_cells rsegs mm SPB (FRA jj fw j3));
      [ unfold FRA, SPB; replace (SP - 400)%Z with (SP + -400)%Z by lia;
        change (CB 112 jj :: [C8 fw; C8 (Z_to_bv 64 wd); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 0x41e84); CB 232 j3; C8 s1; C8 s0; C8 ra])
          with ([CB 112 jj; C8 fw; C8 (Z_to_bv 64 wd); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 0x41e84)] ++ [CB 232 j3; C8 s1; C8 s0; C8 ra]);
        apply rw_cells_app; split; [exact FR | cbn [cells_size csize Nat.add]; replace (SP + -400 + Z.of_nat 144)%Z with (SP + -256)%Z by lia; exact FW]
      | ] end end.
  zstep. destruct (feq_d (reg_get F 10) (Z_to_bv 64 0)) eqn:FQ; cbn [bword] in *.
  -
    if_cases K1; [vm_compute in K1; discriminate|].
    replace (Z_to_bv 64 (SP + -400)) with (Z_to_bv 64 SPB) by (unfold SPB; f_equal; lia).
    apply evt_done. left. unfold wpA. exs. split; [reflexivity|].
    split; [eassumption|]. split; [exact FRA1|]. split; [exact BU|]. split; [exact ES|].
    split; [unfold SPB; replace (SP - 400)%Z with (SP + -400)%Z by lia; exact ST|].
    split; [unfold WH_W; exact MU|]. split; [exact WM | exact MI].
  - if_cases K1; [|vm_compute in K1; discriminate].
    do 2 zstep. step.
    do 5 zstep.

    apply (rw_cells_split_CB rsegs _ (SP + -400) [] 108 _ _ [4; 22; 78; 4]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    peel FR. peel FR. peel FR. peel FR. peel FR.
    replace (SP + -400 + Z.of_nat 4)%Z with (SP + -396)%Z in PC0 by lia.
    replace (SP + -400 + Z.of_nat 4 + Z.of_nat 22)%Z with (SP + -374)%Z in PC1 by lia.
    replace (SP + -400 + Z.of_nat 4 + Z.of_nat 22 + Z.of_nat 78)%Z with (SP + -296)%Z in PC2 by lia.
    replace (SP + -400 + Z.of_nat 4 + Z.of_nat 22 + Z.of_nat 78 + Z.of_nat 4)%Z with (SP + -292)%Z in PC3 by lia.
    replace (SP + -400 + Z.of_nat 4 + Z.of_nat 22 + Z.of_nat 78 + Z.of_nat 4 + Z.of_nat 4)%Z with (SP + -288)%Z in FR by lia.
    destruct (cb4_c4 _ _ _ PC2) as (kj & KC). clear PC2.
    assert (L22 : length (match PC0 with _ => ltac:(lazymatch type of PC0 with rw_cells _ _ _ [CB _ ?l] => exact l end) end) = 22%nat) by (destruct PC0 as [[W _] _]; cbn in W; tauto).
    apply u8arr_of_rw_cells in PC0 as BU0.
    destruct (stk_split rsegs _ (SP - 9600) (SP + -528) (SP + -400) ST ltac:(lia)) as [STlo SThi]. clear ST.
    pose proof (fabs_pos _ FQ) as Hb.
    assert (USP : bv_unsigned (Z_to_bv 64 (SP + -400)) = (SP + -400)%Z) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (g3_spec (Z_to_bv 64 0x43370) (Z_to_bv 64 (SP + -400)) gp tp (Z_to_bv 64 o) (Z_to_bv 64 dp) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ (SP + -396) (SP + -292) (SP + -296)).
      all: unfold GSP; rewrite ?USP.
      all: try lia.
      - reflexivity.
      - rewrite freg_get_other by reflexivity. rewrite freg_get_same by reflexivity. exact Hb.
      - eassumption.
      - replace (SP + -400 - 128)%Z with (SP + -528)%Z by lia. exact SThi.
      - exact BU0.
      - exact L22.
      - exact PC3.
      - exact KC.
      - eassumption.
      - reflexivity. }
    cbv beta. intros ms' P. unfold g3_post, G3_W, GSP in P. rewrite USP in P.
    destruct P as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & res & len & K & bs2 & -> & MUc & WMc & MI2 & FRM2 & ST2 & BU2 & BL2 & _ & LE2 & Hlen & KC2 & HK & Hres).
    replace (ret_pc (Z_to_bv 64 275312)) with (Z_to_bv 64 0x43370) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    clear BU0 L22 KC PC3 SThi PC0.
    change G3Pure.rsegs with rsegs in *.
    transport_after_call rsegs m1 m2 MUc WMc. clear MUc WMc.

    pose proof (u8arr_rw _ _ _ BU2) as DG. rewrite BL2 in DG.
    lazymatch goal with
    | H0 : rw_cells _ m2 (SP + -400) [CB 4 ?j2], H1 : rw_cells _ m2 (SP + -374) [CB 78 ?x],
      H2 : rw_cells _ m2 (SP + -288) ?cs8, H3 : rw_cells _ m2 (SP + -256) ?csw |- _ =>
      pose proof (rw_glue _ _ _ _ _ H0 (rw_glue _ _ _ _ _ DG (rw_glue _ _ _ _ _ H1 (rw_glue _ _ _ _ _ KC2 (rw_glue _ _ _ _ _ LE2 (rw_glue _ _ _ _ _ H2 H3 ltac:(cbn; lia))
                   ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) ltac:(cbn; lia)) as FRD0;
      clear H0 H1 H2 H3 DG KC2 LE2
    end.
    cbn [app] in FRD0.
    apply (rw_cells_merge rsegs m2 (SP + -400) [_] [_; _] _) in FRD0. cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRD0.
    assert (ST3 : stk rsegs m2 (SP - 9600) SPB)
      by (unfold SPB; apply (stk_merge rsegs m2 (SP - 9600) (SP + -528) (SP - 400)); [exact STlo | replace (SP - 400)%Z with (SP + -400)%Z by lia; replace (SP + -528)%Z with (SP + -400 - 128)%Z by lia; exact ST2 | lia]).
    replace (Z_to_bv 64 (SP + -400)) with (Z_to_bv 64 SPB) by (unfold SPB; f_equal; lia).
    eapply (wh_g3ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m2 res len K); try eassumption.
Qed.

Hypothesis WDR : (SP <= wd /\ wd + 9 <= 2 ^ 47)%Z.
Lemma wh_entry : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (m : word -> option byte) (bs : list byte),
  frm0 fc -> ro_cells rsegs m wd [C1 (Z_to_bv 8 0)] -> ro_cells rsegs m (wd + 4) [C4 (Z_to_bv 64 0)] -> ro_cells rsegs m (wd + 8) [C1 (Z_to_bv 8 dp)] ->
  u8arr rsegs m o bs -> estr bs ->
  stk rsegs m (SP - 9600) SP -> mem_inv rsegs m -> m = m0 ->
  evt rsegs wpost (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 wd) (Z_to_bv 64 o) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x41cd0) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros FRM WD0 WD4 WD8 BU ES ST MI ->.
  pose proof (munch_refl WH_W m0) as MU. pose proof (wmono_refl rsegs m0) as WM. unfold WH_W in MU.
  carve_frame 256%nat ST.
  do 4 zstep.
  do 3 zstep.
  zstep. if_cases K1; [|vm_compute in K1; discriminate].
  zstep. zstep. if_cases K2; [|vm_compute in K2; discriminate].
  zstep. cbv beta in *.
  replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 dp))) with (Z_to_bv 64 dp) by (f_equal; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn -[Z.pow]; rewrite Z.mod_small; lia).
  do 3 zstep.
  replace (Z_to_bv 64 (SP + -256)) with (Z_to_bv 64 (SP - 256)) by (f_equal; lia).
  replace (SP + -256)%Z with (SP - 256)%Z in ST, FR by lia.
  eapply (wh_true _ _ _ _ _ _ _ _ _ _ _ _ F fc); try eassumption.
Qed.

End WH.
