(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs F_memset R_setshadow R_poison R_tlsgetaddr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition ann_entry : Z := 0x850e0.
Definition g_got_flags : Z := 0x16a228.
Definition g_flags : Z := 0x171438.
Definition g_detect_container_overflow : Z := 0x171498.

Definition ann_cells (m : mem) : Prop :=
  rw_cells asegs m g_got_flags [C8 (Z_to_bv 64 g_flags)]
  /\ ro_cells asegs m g_detect_container_overflow [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m g_got_verbosity [C8 (Z_to_bv 64 g_current_verbosity)]
  /\ rw_cells asegs m g_current_verbosity [C4 (Z_to_bv 64 0)].

Definition ann_rng_ok (p n : Z) : Prop :=
  ((0 <= p /\ p + n <= kLowMemEnd + 1) \/ (kHighShadowEnd < p /\ p + n <= kHighMemEnd + 1))%Z.

Definition annotate_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a len val lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(shad a, shad a + len / 8); (bv_unsigned sp - 2192, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ ((0 < len)%Z -> rw_cells asegs m' (shad a) [CB (Z.to_nat (len / 8)) (repeat (Z_to_bv 8 val) (Z.to_nat (len / 8)))])
    /\ stk asegs m' lo (bv_unsigned sp).

Local Definition boxed (P : Prop) : Prop := P.
Local Lemma box : forall P : Prop, P -> boxed P. Proof. intros P H. exact H. Qed.
Local Lemma unbox : forall P : Prop, boxed P -> P. Proof. intros P H. exact H. Qed.

Local Ltac amem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Lemma land_m8_ann : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551608 = (8 * (x / 8))%Z.
Proof.
  intros x Hx. change 18446744073709551608%Z with (Z.ldiff (Z.ones 64) (Z.ones 3)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^3)%Z with 8%Z. lia.
Qed.

Lemma annotate_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p n v v' lo : Z) (shj : list byte),
  (0 <= v <= n)%Z -> (0 <= v' <= n)%Z -> (v mod 8 = 0)%Z -> (v' mod 8 = 0)%Z -> (p mod 8 = 0)%Z -> (n mod 8 = 0)%Z -> (1 <= n <= 2^40)%Z ->
  ann_rng_ok p n ->
  (v <> v' -> rw_cells asegs m (shad (p + Z.min v v')) [CB (Z.to_nat ((Z.max v v' - Z.min v v') / 8)) shj]) ->
  ann_cells m -> ps_cells m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2192)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  mem_inv asegs m ->
  evt asegs (annotate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (p + Z.min v v') (Z.max v v' - Z.min v v')
               (if (v <? v')%Z then 0 else 252) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (p + n)) (Z_to_bv 64 (p + v)) (Z_to_bv 64 (p + v')) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ann_entry) fc None m (seg_rom asegs)).
Proof.
  intros until shj. intros Hv Hv' V8 V8' P8 N8 Hn HR SH AC PS ST HLO HLOH MI.
  destruct AC as (GF & DCO & GV & CV).
  unfold ann_entry, g_got_flags, g_flags, g_detect_container_overflow, g_got_verbosity, g_current_verbosity in *.
  unfold ann_rng_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd in *.
  assert (HPR : (0 <= p /\ p + n <= 2^47)%Z) by lia.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (wmono_refl asegs m) as WM.
  apply box in PS.
  move GF at bottom. move DCO at bottom. move GV at bottom. move CV at bottom.
  destruct (Z.eq_dec v v') as [EQ|NE]; [| destruct (Z_lt_le_dec v v') as [LT|GE]].
  -
    subst v'. clear SH. rewrite Z.min_id, Z.max_id, Z.sub_diag. cbn [Z.div].
    pose proof (munch_refl [(shad (p + v), shad (p + v) + 0); (bv_unsigned sp - 2192, bv_unsigned sp)]%Z m) as MU.
    carve_frame 2128%nat ST.
    do 10 zstep.
    do 5 zstep. ifF.
    do 8 zstep. ifF.
    zstep. ifT. zstep. ifF. zstep. ifF. zstep. ifF.
    do 4 zstep. zstep. ifF.
    zstep. ifT.
    do 8 zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    apply evt_done. unfold annotate_post. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [intros; lia| exact ST].
  -
    rewrite (Z.min_l v v'), (Z.max_r v v') in * by lia. rewrite (proj2 (Z.ltb_lt v v') LT).
    specialize (SH ltac:(lia)).
    assert (PA : ps_args_ok (p + v) (v' - v)) by (unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd; split; [Z.div_mod_to_equations; lia | lia]).
    pose proof (ps_shad_range _ _ PA) as (SR1 & SR2 & SR3 & SR4). unfold kHighShadowEnd in SR2.
    pose proof (munch_refl [(shad (p + v), shad (p + v) + (v' - v) / 8); (bv_unsigned sp - 2192, bv_unsigned sp)]%Z m) as MU.
    carve_frame 2128%nat ST.
    do 10 zstep.
    do 5 zstep. ifF.
    do 8 zstep. ifF.
    zstep. ifT. zstep. ifF. zstep. ifF. zstep. ifF.
    do 4 zstep. zstep. ifF.
    zstep. ifF.

    zstep. rewrite land7_ps by lia. zstep. ifF.
    do 3 zstep. zstep. rewrite land7_ps by lia. zstep. ifF.
    do 2 zstep. zstep. ifT.
    zstep. rewrite land_m8_ann by lia. zstep. ifF.
    zstep. zstep. rewrite land_m8_ann by lia. zstep. zstep. rewrite land_m8_ann by lia.
    zstep. ifT.
    do 3 zstep.
    replace (8 * ((p + v) / 8))%Z with (p + v)%Z by lia.
    replace (8 * ((p + v' + 7) / 8))%Z with (p + v')%Z by lia.
    replace (8 * ((p + v') / 8))%Z with (p + v')%Z by lia.
    replace (p + v' - (p + v))%Z with (v' - v)%Z by lia.
    let mm := amem in
    pose proof (ps_cells_framed m mm _ (unbox _ PS) MU WM ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)) as PSm.
    clear PS. sp_facts.
    zstep.
    call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (p + v)%Z (v' - v)%Z 0 lo shj).
    all: rewrite ?Esp in *; try lia; try eassumption.
    clear PSm. zstep. ifT.
    do 8 zstep. zstep.
    release_frame FR POST (bv_unsigned sp).
    zstep.
    apply evt_done. unfold annotate_post. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [intros _; exact PC| exact POST].
  -
    rewrite (Z.min_r v v'), (Z.max_l v v') in * by lia. rewrite (proj2 (Z.ltb_ge v v') GE).
    specialize (SH ltac:(lia)).
    assert (PA : ps_args_ok (p + v') (v - v')) by (unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd; split; [Z.div_mod_to_equations; lia | lia]).
    pose proof (ps_shad_range _ _ PA) as (SR1 & SR2 & SR3 & SR4). unfold kHighShadowEnd in SR2.
    pose proof (munch_refl [(shad (p + v'), shad (p + v') + (v - v') / 8); (bv_unsigned sp - 2192, bv_unsigned sp)]%Z m) as MU.
    carve_frame 2128%nat ST.
    do 10 zstep.
    do 5 zstep. ifF.
    do 8 zstep. ifF.
    zstep. ifT. zstep. ifF. zstep. ifF. zstep. ifF.
    do 4 zstep. zstep. ifF.
    zstep. ifF.

    zstep. rewrite land7_ps by lia. zstep. ifF.
    do 3 zstep. zstep. rewrite land7_ps by lia. zstep. ifF.
    do 2 zstep. zstep. ifF.
    zstep. rewrite land_m8_ann by lia. zstep. ifF.
    zstep. rewrite land_m8_ann by lia. zstep. zstep. rewrite land_m8_ann by lia.
    zstep. ifT.
    zstep. zstep. rewrite land_m8_ann by lia. zstep. ifF.
    do 3 zstep.
    replace (8 * ((p + v' + 7) / 8))%Z with (p + v')%Z by lia.
    replace (8 * ((p + v + 7) / 8))%Z with (p + v)%Z by lia.
    replace (8 * ((p + v') / 8))%Z with (p + v')%Z by lia.
    replace (p + v - (p + v'))%Z with (v - v')%Z by lia.
    let mm := amem in
    pose proof (ps_cells_framed m mm _ (unbox _ PS) MU WM ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)) as PSm.
    clear PS. sp_facts.
    zstep.
    call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (p + v')%Z (v - v')%Z 252 lo shj).
    all: rewrite ?Esp in *; try lia; try eassumption.
    clear PSm. zstep. ifT.
    do 8 zstep. zstep.
    release_frame FR POST (bv_unsigned sp).
    zstep.
    apply evt_done. unfold annotate_post. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [intros _; exact PC| exact POST].
Qed.
