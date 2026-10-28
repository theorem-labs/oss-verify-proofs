(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs F_memset R_setshadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Local Ltac zidle_begin_rw sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
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
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition ps_entry : Z := 0x81d40.
Definition g_can_poison : Z := 0x17741c.
Definition g_got_common_flags : Z := 0x16e760.
Definition g_cf_clear_shadow_mmap_threshold : Z := 0x209760.

Definition ps_cells (m : mem) : Prop :=
  rw_cells bsegs m g_got_common_flags [C8 (Z_to_bv 64 0x2096e8)]
  /\ m2s_cells m /\ setshadow_cells m
  /\ rw_cells bsegs m g_can_poison [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m g_cf_clear_shadow_mmap_threshold [C8 (Z_to_bv 64 0xffffffffffffffff)].

Definition ps_args_ok (a n : Z) : Prop :=
  (a mod 8 = 0 /\ n mod 8 = 0 /\ 0 < n)%Z /\
  ((0 <= a /\ a + n <= kLowMemEnd + 1) \/ (kHighShadowEnd < a /\ a + n <= kHighMemEnd + 1))%Z.

Definition poison_small_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a n v lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(shad a, shad a + n / 8); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (shad a) [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 v) (Z.to_nat (n / 8)))]
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma land7_ps : forall x, (0 <= x)%Z -> Z.land x 7 = (x mod 8)%Z.
Proof. intros x Hx. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma ps_shad_range : forall a n, ps_args_ok a n ->
  (0x7fff8000 <= shad a /\ shad a + n / 8 <= kHighShadowEnd + 1 /\ 8 * (n / 8) = n /\ 0 < n / 8)%Z.
Proof.
  intros a n ((Ha & Hn & Hn0) & HR). unfold shad, SHB, kLowMemEnd, kHighShadowEnd, kHighMemEnd in *.
  pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)).
  assert (shad ((a + n)) = (a + n) / 8 + SHB)%Z by reflexivity.
  assert (E : ((a + n) / 8 = a / 8 + n / 8)%Z).
  { replace (a + n)%Z with ((a / 8 + n / 8) * 8)%Z by lia. rewrite Z.div_mul by lia. reflexivity. }
  pose proof (Z.div_le_upper_bound (a + n) 8 (2^44) ltac:(lia) ltac:(lia)).
  split; [pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)); lia|]. split; [lia|]. split; lia.
Qed.

Lemma ps_tail : forall ra sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m0 m : mem) (a n v lo : Z) (shj : list byte),
  ps_args_ok a n -> (0 <= v < 256)%Z ->
  rw_cells bsegs m (shad a) [CB (Z.to_nat (n / 8)) shj] ->
  stk bsegs m lo (bv_unsigned sp) -> (kHighShadowEnd + 8 <= lo)%Z ->
  munch [(shad a, shad a + n / 8); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  evt bsegs (poison_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a n v lo m0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (shad a)) (Z_to_bv 64 v) (Z_to_bv 64 (n / 8)) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x161214) fc None m (seg_rom bsegs)).
Proof.
  intros until shj. intros HA Hv SH ST HLOH MU WM MI.
  pose proof (ps_shad_range a n HA) as (SR1 & SR2 & SR3 & SR4). unfold kHighShadowEnd in *.
  eapply evt_mono; [eapply memset_callZ with (junk := shj); [exact SH| exact MI| lia| lia| lia| lia] |].
  intros ms' PO. unfold memset_postZ in PO.
  destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU2 & WM2 & MI2 & RW).
  subst ms'. unfold poison_small_post.
  do 16 eexists. split; [reflexivity|].
  split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia]|].
  split; [eapply wmono_trans; eassumption|].
  split; [exact MI2|].
  split; [rewrite Z.mod_small in RW by lia; exact RW|].
  eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2|]. cbn [disjoint_from]. destruct ST as [? _]. split; [right; lia| exact I].
Qed.

Lemma ps_j54ad0 : forall ra ra' sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m0 m : mem) (s0o s1o s2o s3o s4o s5o : word) (a n v lo : Z) (shj junk : list byte),
  ps_args_ok a n -> (0 <= v < 256)%Z -> (v <> 0 \/ n / 8 < 0xffffffffffffffff)%Z ->
  rw_cells bsegs m (shad a) [CB (Z.to_nat (n / 8)) shj] ->
  ps_cells m ->
  rw_cells bsegs m (bv_unsigned sp - 64) [CB 8 junk; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
  stk bsegs m lo (bv_unsigned sp - 64) -> (lo <= bv_unsigned sp - 64)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  munch [(shad a, shad a + n / 8); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  evt bsegs (poison_small_post ra sp gp tp s0o s1o s2o s3o s4o s5o s6 s7 s8 s9 s10 s11 F fc a n v lo m0)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 2147450880) (Z_to_bv 64 a)
             (Z_to_bv 64 (a + n - 8)) (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81fc4) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros HA Hv Hsmall SH PS FR ST HLO HLOH MU WM MI.
  pose proof (ps_shad_range a n HA) as (SR1 & SR2 & SR3 & SR4). pose proof HA as HA0.
  destruct HA as ((Ha & Hn & Hn0) & HR).
  destruct PS as (CF & (GOT & SHB0 & HM) & (GRM & RM) & CP & THR).
  unfold g_got_common_flags, g_can_poison, g_cf_clear_shadow_mmap_threshold, g_got_real_memset, g_real_memset,
    musl_memset_entry, kLowMemEnd, kHighShadowEnd, kHighMemEnd, SHB in *.
  move CF at bottom. move GOT at bottom. move GRM at bottom. move RM at bottom. move CP at bottom. move SHB0 at bottom.
  move HM at bottom. move THR at bottom.
  do 4 zstep. ifF.
  do 5 zstep.
  pose proof (Z.div_mod a 8 ltac:(lia)) as D1. pose proof (Z.div_mod n 8 ltac:(lia)) as D2.
  assert (E1 : (2147450880 + a ≫ 3)%Z = shad a) by (unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; cbn; lia).
  assert (E2 : (((a + n - 8) ≫ 3 + 1) mod 18446744073709551616 - a ≫ 3)%Z = (n / 8)%Z).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
    replace (a + n - 8)%Z with ((a / 8 + n / 8 - 1) * 8)%Z by lia. rewrite Z.div_mul by lia.
    rewrite Z.mod_small by (pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)); lia). lia. }
  rewrite E1, E2.
  destruct (Z.eq_dec v 0) as [V0|V0].
  - subst v. zstep. ifF.
    do 4 zstep. ifT.
    do 11 zstep.
    replace (bv_unsigned sp - 64 + 64)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    eapply ps_tail; try eassumption; lia.
  - zstep. ifT.
    do 11 zstep.
    replace (bv_unsigned sp - 64 + 64)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    eapply ps_tail; try eassumption; lia.
Qed.

Lemma disjoint_from_sub : forall W L n A k, disjoint_from W L n -> (L <= A)%Z -> (0 <= k)%Z -> (A + k <= L + n)%Z ->
  disjoint_from W A k.
Proof.
  induction W as [|[lo hi] W IH]; intros L n A k H H1 H2 H3; cbn in *; [exact I|].
  destruct H as [H4 H5]. split; [lia| eapply IH; eauto].
Qed.

Ltac tr_hull MU WM HD H :=
  apply (rw_cells_transport bsegs _ _ _ _ _ H MU WM); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  eapply disjoint_from_sub; [exact HD| unfold img_hull_lo; lia| lia| unfold img_hull_lo, img_hull_hi; lia].

Lemma ps_cells_framed : forall (m m' : mem) W, ps_cells m -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W img_hull_lo (img_hull_hi - img_hull_lo) -> ps_cells m'.
Proof.
  intros m m' W PS MU WM HD.
  destruct PS as (CF & (GOT & SHB0 & HM) & (GRM & RM) & CP & THR).
  unfold g_got_common_flags, g_can_poison, g_cf_clear_shadow_mmap_threshold, g_got_real_memset, g_real_memset in *.
  refine (conj _ (conj (conj _ (conj _ _)) (conj (conj _ _) (conj _ _)))).
  - tr_hull MU WM HD CF.
  - tr_hull MU WM HD GOT.
  - tr_hull MU WM HD SHB0.
  - tr_hull MU WM HD HM.
  - tr_hull MU WM HD GRM.
  - tr_hull MU WM HD RM.
  - tr_hull MU WM HD CP.
  - tr_hull MU WM HD THR.
Qed.

Definition ps_K54ad0 (Q : machine_state -> Prop) (ra' sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (a n v : Z) : Prop :=
  forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    evt bsegs Q
      (MS (mkR ra' sp gp tp t0 t1 t2 s0 (Z_to_bv 64 2147450880) (Z_to_bv 64 a) (Z_to_bv 64 (a + n - 8)) (Z_to_bv 64 v)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81fc4) fc None m (seg_rom bsegs)).

Ltac ps_cells_destr PS :=
  let CF := fresh "CF" in let GOT := fresh "GOT" in let SHB0 := fresh "SHB0" in let HM := fresh "HM" in
  let GRM := fresh "GRM" in let RM := fresh "RM" in let CP := fresh "CP" in let THR := fresh "THR" in
  destruct PS as (CF & (GOT & SHB0 & HM) & (GRM & RM) & CP & THR);
  unfold g_got_common_flags, g_can_poison, g_cf_clear_shadow_mmap_threshold, g_got_real_memset, g_real_memset,
    musl_memset_entry, kLowMemEnd, kHighShadowEnd, kHighMemEnd, SHB in *;
  move CF at bottom; move GOT at bottom; move GRM at bottom; move RM at bottom; move CP at bottom; move SHB0 at bottom;
  move HM at bottom; move THR at bottom.

Lemma ps_j54a7c_k : forall (Q : machine_state -> Prop) ra' sp gp tp t0 t1 t2 a3 a5 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (a n v : Z),
  ps_args_ok a n -> ps_cells m -> mem_inv bsegs m ->
  ps_K54ad0 Q ra' sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a n v ->
  evt bsegs Q
    (MS (mkR ra' sp gp tp t0 t1 t2 s0 (Z_to_bv 64 2147450880) (Z_to_bv 64 a)
             (Z_to_bv 64 n) (Z_to_bv 64 v) a3 (Z_to_bv 64 2147450879) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81f70) fc None m (seg_rom bsegs)).
Proof.
  intros until v. intros HA PS MI K.
  destruct HA as ((Ha & Hn & Hn0) & HR).
  ps_cells_destr PS.
  zstep. rewrite land7_ps by lia. zstep. ifF.
  do 2 zstep.
  replace (a + n + -8)%Z with (a + n - 8)%Z by lia.
  zstep.
  destruct HR as [HL|HH].
  - ifT. apply K.
  - ifF.
    do 8 zstep.
    assert (C1 : negb (bv_ltu (Z_to_bv 64 (-1)) (Z_to_bv 64 (a + n - 8))) = true).
    { unfold bv_ltu. rewrite (unsigned_lit_wrap (-1)), (unsigned_lit (a + n - 8)) by lia.
      change ((-1) mod 2^64)%Z with 18446744073709551615%Z. apply negb_true_iff, Z.ltb_ge. lia. }
    rewrite C1; cbv iota.
    do 5 zstep.
    zstep. ifF. zstep. ifF.
    apply K.
Qed.

Lemma ps_j54880_k : forall (Q : machine_state -> Prop) ra' sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
    s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (a n v : Z),
  ps_args_ok a n -> ps_cells m -> mem_inv bsegs m ->
  ps_K54ad0 Q ra' sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a n v ->
  evt bsegs Q
    (MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 n) (Z_to_bv 64 v)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81d74) fc None m (seg_rom bsegs)).
Proof.
  intros until v. intros HA PS MI K.
  pose proof HA as HA0. pose proof PS as PS0.
  destruct HA as ((Ha & Hn & Hn0) & HR).
  ps_cells_destr PS.
  zstep. rewrite land7_ps by lia. zstep. ifF.
  do 8 zstep.
  replace (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879)%Z with 2147450879%Z
    by reflexivity.
  destruct HR as [HL|HH].
  - ifT. eapply ps_j54a7c_k; eassumption.
  - ifF.
    do 8 zstep.
    assert (C1 : negb (bv_ltu (Z_to_bv 64 (-1)) (Z_to_bv 64 a)) = true).
    { unfold bv_ltu. rewrite (unsigned_lit_wrap (-1)), (unsigned_lit a) by lia.
      change ((-1) mod 2^64)%Z with 18446744073709551615%Z. apply negb_true_iff, Z.ltb_ge. lia. }
    rewrite C1; cbv iota.
    do 5 zstep.
    zstep. ifF. zstep. ifT.
    do 3 zstep.
    zstep. ifF. zstep. ifT.
    eapply ps_j54a7c_k; eassumption.
Qed.

Lemma ps_entry_k : forall (Q : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
    s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (a n v lo : Z),
  ps_args_ok a n -> (0 <= v < 256)%Z -> ps_cells m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> mem_inv bsegs m ->
  (forall (m1 : mem) (junk : list byte),
     rw_cells bsegs m1 (bv_unsigned sp - 64) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     stk bsegs m1 lo (bv_unsigned sp - 64) ->
     munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
     ps_K54ad0 Q ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 a n v) ->
  evt bsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 n) (Z_to_bv 64 v) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ps_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros HA Hv PS ST HLO HLOH MI K.
  pose proof HA as HA0. pose proof PS as PS0. unfold ps_entry.
  pose proof (ps_shad_range a n HA) as (SR1 & SR2 & SR3 & SR4).
  destruct HA as ((Ha & Hn & Hn0) & HR).
  ps_cells_destr PS.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 64%nat ST.
  zidle_begin_rw sp 64%Z MUz WMz.
  do 8 zstep.
  do 1 zstep.
  zidle_end MUz WMz.
  replace (bv_unsigned sp + -64)%Z with (bv_unsigned sp - 64)%Z in * by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (PSm : ps_cells mm) by (unfold ps_cells, m2s_cells, setshadow_cells, g_got_common_flags, g_can_poison,
      g_cf_clear_shadow_mmap_threshold, g_got_real_memset, g_real_memset, musl_memset_entry, SHB, kHighMemEnd;
      refine (conj _ (conj (conj _ (conj _ _)) (conj (conj _ _) (conj _ _)))); assumption) end.
  clear PS0.
  destruct (Z.eq_dec v 0) as [V0|V0].
  - ifT. eapply ps_j54880_k; try eassumption. eapply K; eassumption.
  - ifF. do 4 zstep. ifF. eapply ps_j54880_k; try eassumption. eapply K; eassumption.
Qed.

Lemma poison_small_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (a n v lo : Z) (shj : list byte),
  ps_args_ok a n -> (0 <= v < 256)%Z -> (v <> 0 \/ n / 8 < 0xffffffffffffffff)%Z ->
  rw_cells bsegs m (shad a) [CB (Z.to_nat (n / 8)) shj] ->
  ps_cells m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  mem_inv bsegs m ->
  evt bsegs (poison_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a n v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 n) (Z_to_bv 64 v) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ps_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until shj. intros HA Hv Hsmall SH PS ST HLO HLOH MI.
  pose proof (ps_shad_range a n HA) as (SR1 & SR2 & SR3 & SR4).
  unfold kHighShadowEnd in *.
  eapply ps_entry_k; try eassumption.
  intros m1 junk FR ST1 MU1 WM1 MI1 t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6'.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ SH MU1 WM1 ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as SH1.
  pose proof (ps_cells_framed m m1 _ PS MU1 WM1 ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)) as PS1.
  eapply ps_j54ad0; try eassumption.
  eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
Qed.
