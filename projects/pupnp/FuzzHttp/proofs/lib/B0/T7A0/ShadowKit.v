(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Walk.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts IcptA0.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition SH_LO : Z := 0x7fff7000.
Definition SH_HI : Z := 0x10007fff8000.
Definition shband (a : Z) : Prop := SH_LO <= a < SH_HI.

Definition win_ok (A n : Z) : Prop :=
  0 <= n /\ ((4096 <= A /\ A + n <= 0x7fff7000) \/ (0x10007fff8000 <= A /\ A + n <= 2^47)).

Lemma win_ok_sub : forall A n A' n', win_ok A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> win_ok A' n'.
Proof. intros A n A' n' [Hn W] H1 H2 H3. split; [lia|]. lia. Qed.

Lemma div8_bounds : forall a, 8 * (a / 8) <= a < 8 * (a / 8) + 8.
Proof. intros a. pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). lia. Qed.

Lemma sh_mono : forall a b, a <= b -> sh a <= sh b.
Proof. intros a b H. unfold sh. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

Lemma sh_readable_range_slack : forall A n a, 0 <= n ->
  sh A - sh A mod 8 <= a < sh (A + n - 1) - sh (A + n - 1) mod 8 + 8 -> sh A - 8 <= a < sh (A + n) + 8.
Proof.
  intros A n a Hn Ha. pose proof (div8_bounds (sh A)). pose proof (div8_bounds (sh (A + n - 1))).
  pose proof (Z.mod_pos_bound (sh A) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sh (A + n - 1)) 8 ltac:(lia)).
  pose proof (sh_mono (A + n - 1) (A + n) ltac:(lia)). lia.
Qed.

Lemma win_ok_words_band : forall A n a, win_ok A n -> 0 < n ->
  sh A - sh A mod 8 <= a < sh (A + n - 1) - sh (A + n - 1) mod 8 + 8 -> shband a.
Proof.
  intros A n a [Hn W] Hp Ha; unfold shband, SH_LO, SH_HI, sh, SHADOW_OFF in *.
  pose proof (div8_bounds A). pose proof (div8_bounds (A + n - 1)).
  pose proof (Z.mod_pos_bound (A / 8 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound ((A + n - 1) / 8 + 2147450880) 8 ltac:(lia)).
  pose proof (Z.div_mod (A / 8 + 2147450880) 8 ltac:(lia)). pose proof (Z.div_mod ((A + n - 1) / 8 + 2147450880) 8 ltac:(lia)).
  lia.
Qed.

Lemma win_ok_sh_band : forall A n a, win_ok A n -> A <= a < A + n -> shband (sh a).
Proof.
  intros A n a [Hn W] Ha; unfold shband, SH_LO, SH_HI, sh, SHADOW_OFF in *. pose proof (div8_bounds a). lia.
Qed.

Definition app_iv (iv : Z * Z) : Prop := (0 <= fst iv /\ snd iv <= 0x7fff7000) \/ SH_HI <= fst iv.
Definition app_ivs (W : list (Z * Z)) : Prop := Forall app_iv W.

Lemma app_ivs_disjoint : forall W a, app_ivs W -> shband a -> disjoint_from W a 1.
Proof.
  intros W a H Ha. unfold shband, SH_LO, SH_HI in Ha. induction H as [|[lo hi] W Hiv _ IH]; cbn; [exact I|].
  split; [| exact IH]. unfold app_iv, SH_HI in Hiv. cbn in Hiv. lia.
Qed.

Lemma app_ivs_outside : forall W a, app_ivs W -> shband a -> outside W a.
Proof. intros W a H Ha. eapply disjoint_outside; [apply app_ivs_disjoint; eassumption | lia]. Qed.

Lemma app_iv_stack {HC : HasCeiling} : forall lo hi, alloc_ceiling <= lo -> app_iv (lo, hi).
Proof. intros lo hi H. right. cbn. pose proof alloc_ceiling_bounds. unfold SH_HI. lia. Qed.
Lemma app_iv_low : forall lo hi, 0 <= lo -> hi <= 0x7fff7000 -> app_iv (lo, hi).
Proof. intros lo hi H1 H2. left. cbn. lia. Qed.
Lemma app_iv_high : forall lo hi, 0x10007fff8000 <= lo -> app_iv (lo, hi).
Proof. intros lo hi H. right. cbn. unfold SH_HI. lia. Qed.
Lemma app_iv_sub : forall lo hi lo' hi', app_iv (lo, hi) -> lo <= lo' -> hi' <= hi -> app_iv (lo', hi').
Proof. intros lo hi lo' hi' H H1 H2. unfold app_iv in *. cbn in *. lia. Qed.

Lemma app_iv_of_win_ok : forall A n lo hi, win_ok A n -> A <= lo -> hi <= A + n -> app_iv (lo, hi).
Proof. intros A n lo hi [Hn W] H1 H2. unfold app_iv, SH_HI. cbn [fst snd]. lia. Qed.
Lemma win_ok_of_range {HC : HasCeiling} : forall A n,
  4096 <= A -> 0 <= n -> A + n <= alloc_ceiling -> (A + n <= 0x7fff7000 \/ 0x10007fff8000 <= A) -> win_ok A n.
Proof. intros A n H1 H2 H3 H4. pose proof alloc_ceiling_bounds. unfold alloc_floor, alloc_ceiling_max in *. unfold win_ok. lia. Qed.

Definition shz (m : mem) (lo hi : Z) : Prop :=
  forall a, lo <= a < hi -> mrd asegs m (wa a) = Some (Z_to_bv 8 0).

Definition shw (m : mem) (A n : Z) : Prop := accessible m A n /\ sh_readable m A n /\ win_ok A n.

Lemma shz_sub : forall m lo hi lo' hi', shz m lo hi -> lo <= lo' -> hi' <= hi -> shz m lo' hi'.
Proof. intros m lo hi lo' hi' H H1 H2 a Ha. apply H. lia. Qed.

Lemma shw_sub : forall m A n A' n', shw m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> shw m A' n'.
Proof.
  intros m A n A' n' (AC & RD & W) H1 H2 H3. split; [|split].
  - eapply accessible_sub; eauto.
  - eapply sh_readable_sub; eauto.
  - eapply win_ok_sub; eauto.
Qed.

Lemma shw_win_ok : forall m A n, shw m A n -> win_ok A n.
Proof. intros m A n (_ & _ & W); exact W. Qed.

Lemma shw_of_shz : forall m lo hi A n,
  shz m lo hi -> win_ok A n -> lo <= sh A - 8 -> sh (A + n) + 8 <= hi -> shw m A n.
Proof.
  intros m lo hi A n Z W H1 H2. split; [|split; [|exact W]].
  - intros a Ha. exists 0. split; [|left; reflexivity].
    pose proof (win_ok_sh_band A n a W Ha) as B. unfold shband, SH_LO, SH_HI in B.
    split; [lia|]. split; [cbn; lia|].
    intros i Hi. cbn in Hi. destruct i; [|lia]. cbn. rewrite Z.add_0_r. apply Z.
    pose proof (sh_mono A a ltac:(lia)). pose proof (sh_mono a (A + n) ltac:(lia)). lia.
  - intros Hn a Ha. exists (Z_to_bv 8 0). apply Z. pose proof (sh_readable_range_slack A n a (proj1 W) Ha). lia.
Qed.

Definition shr (m : mem) (lo hi : Z) : Prop :=
  forall a, lo <= a < hi -> exists v, mrd asegs m (wa a) = Some v.

Lemma shr_of_shz : forall m lo hi, shz m lo hi -> shr m lo hi.
Proof. intros m lo hi Z a Ha. exists (Z_to_bv 8 0). apply Z. exact Ha. Qed.

Lemma shr_sub : forall m lo hi lo' hi', shr m lo hi -> lo <= lo' -> hi' <= hi -> shr m lo' hi'.
Proof. intros m lo hi lo' hi' R H1 H2 a Ha. apply R. lia. Qed.

Lemma shw_of_shz_shr : forall m zlo zhi rlo rhi A n,
  shz m zlo zhi -> shr m rlo rhi -> win_ok A n ->
  zlo <= sh A -> sh (A + n - 1) + 1 <= zhi ->
  rlo <= sh A - sh A mod 8 -> sh (A + n - 1) - sh (A + n - 1) mod 8 + 8 <= rhi ->
  shw m A n.
Proof.
  intros m zlo zhi rlo rhi A n Z R W Z1 Z2 R1 R2. split; [|split; [|exact W]].
  - intros a Ha. exists 0. split; [|left; reflexivity].
    pose proof (win_ok_sh_band A n a W Ha) as B. unfold shband, SH_LO, SH_HI in B.
    split; [lia|]. split; [cbn; lia|].
    intros i Hi. cbn in Hi. destruct i; [|lia]. cbn. rewrite Z.add_0_r. apply Z.
    pose proof (sh_mono A a ltac:(lia)). pose proof (sh_mono a (A + n - 1) ltac:(lia)). lia.
  - intros Hn a Ha. apply R. lia.
Qed.

Lemma shw_of_shz' : forall m lo hi A n,
  shz m lo hi -> win_ok A n -> lo <= sh A - 8 -> sh (A + n - 1) - sh (A + n - 1) mod 8 + 8 <= hi -> shw m A n.
Proof.
  intros m lo hi A n Z W H1 H2. split; [|split; [|exact W]].
  - intros a Ha. exists 0. split; [|left; reflexivity].
    pose proof (win_ok_sh_band A n a W Ha) as B. unfold shband, SH_LO, SH_HI in B.
    split; [lia|]. split; [cbn; lia|].
    intros i Hi. cbn in Hi. destruct i; [|lia]. cbn. rewrite Z.add_0_r. apply Z.
    pose proof (sh_mono A a ltac:(lia)). pose proof (sh_mono a (A + n - 1) ltac:(lia)).
    pose proof (Z.mod_pos_bound (sh (A + n - 1)) 8 ltac:(lia)). lia.
  - intros Hn a Ha. exists (Z_to_bv 8 0). apply Z. pose proof (Z.mod_pos_bound (sh A) 8 ltac:(lia)). lia.
Qed.

Lemma cells_bytes_shadow : forall ks, cells_bytes (shadow_cells ks) = map (fun k => Z_to_bv 8 k) ks.
Proof. induction ks as [|k ks IH]; cbn; [reflexivity|]. unfold shadow_cells in IH. rewrite IH. reflexivity. Qed.

Lemma shadow_chunk_read : forall m A0 ks i,
  rw_cells asegs m (sh A0) (shadow_cells ks) -> (i < length ks)%nat ->
  mrd asegs m (wa (sh A0 + Z.of_nat i)) = Some (Z_to_bv 8 (nth i ks 0)).
Proof.
  intros m A0 ks i [[Hwf (_ & _ & HB)] _] Hi. rewrite cells_bytes_shadow in HB.
  rewrite (HB i) by (rewrite length_map; exact Hi). rewrite nth_error_map.
  rewrite (nth_error_nth' ks 0 Hi). reflexivity.
Qed.

Lemma shadow_chunk_bound : forall m A0 ks,
  rw_cells asegs m (sh A0) (shadow_cells ks) -> 0 <= sh A0 /\ sh A0 + Z.of_nat (length ks) <= 2^64.
Proof.
  intros m A0 ks [[Hwf (B0 & B1 & _)] _]. rewrite cells_bytes_shadow, length_map in B1. lia.
Qed.

Lemma sh_in_chunk : forall A0 a, A0 mod 8 = 0 -> A0 <= a -> sh a = sh A0 + Z.of_nat (Z.to_nat ((a - A0) / 8)).
Proof.
  intros A0 a AL Ha. rewrite Z2Nat.id by (apply Z.div_pos; lia). unfold sh.
  replace a with (A0 + (a - A0)) at 1 by lia.
  rewrite (Z.div_mod A0 8) at 1 by lia. rewrite AL, Z.add_0_r.
  rewrite Z.mul_comm, Z.div_add_l by lia. lia.
Qed.

Lemma acc_of_chunk : forall m A0 ks a, let i := Z.to_nat ((a - A0) / 8) in
  rw_cells asegs m (sh A0) (shadow_cells ks) -> A0 mod 8 = 0 ->
  A0 <= a -> (i < length ks)%nat ->
  (nth i ks 0 = 0 \/ (0 < nth i ks 0 < 8 /\ a mod 8 < nth i ks 0)) ->
  acc m a.
Proof.
  intros m A0 ks a i SH AL Ha Hi Hk. exists (nth i ks 0). split; [|exact Hk].
  pose proof (sh_in_chunk A0 a AL Ha) as E. fold i in E. pose proof (shadow_chunk_bound m A0 ks SH) as [B0 B1].
  split; [rewrite E; lia|]. split; [cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite E; lia|].
  intros j Hj. cbn in Hj. destruct j; [|lia]. cbn. rewrite Z.add_0_r, E. apply (shadow_chunk_read m A0 ks i SH Hi).
Qed.

Lemma accessible_of_chunk : forall m A0 ks A n,
  rw_cells asegs m (sh A0) (shadow_cells ks) -> A0 mod 8 = 0 ->
  A0 <= A -> A + n <= A0 + 8 * Z.of_nat (length ks) ->
  (forall i, (i < length ks)%nat -> A <= A0 + 8 * Z.of_nat i + 7 -> A0 + 8 * Z.of_nat i < A + n -> nth i ks 0 = 0) ->
  accessible m A n.
Proof.
  intros m A0 ks A n SH AL H1 H2 ZERO a Ha.
  assert (Hi : (Z.to_nat ((a - A0) / 8) < length ks)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia). apply Z.div_lt_upper_bound; lia. }
  apply (acc_of_chunk m A0 ks a SH AL ltac:(lia) Hi). left. apply ZERO; [exact Hi| |];
    rewrite Z2Nat.id by (apply Z.div_pos; lia); pose proof (div8_bounds (a - A0)); lia.
Qed.

Lemma nth_block_shadow_zero : forall n i, 0 <= n -> (Z.of_nat i < n / 8) ->
  nth i (repeat 0 (Z.to_nat (n / 8)) ++ (if n mod 8 =? 0 then [] else [n mod 8])) 0 = 0.
Proof.
  intros n i Hn Hi. rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat.
Qed.
Lemma nth_block_shadow_last : forall n, 0 <= n -> n mod 8 <> 0 ->
  nth (Z.to_nat (n / 8)) (repeat 0 (Z.to_nat (n / 8)) ++ (if n mod 8 =? 0 then [] else [n mod 8])) 0 = n mod 8.
Proof.
  intros n Hn Hm. rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length, Nat.sub_diag.
  destruct (Z.eqb_spec (n mod 8) 0); [lia|]. reflexivity.
Qed.
Lemma accessible_of_block_shadow : forall m B n ks A k,
  rw_cells asegs m (sh B) (shadow_cells ks) -> B mod 8 = 0 -> 0 <= n ->
  ks = repeat 0 (Z.to_nat (n / 8)) ++ (if n mod 8 =? 0 then [] else [n mod 8]) ->
  B <= A -> A + k <= B + n -> accessible m A k.
Proof.
  intros m B n ks A k SH AL Hn Hks H1 H2 a Ha.
  pose proof (div8_bounds n) as Dn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Mn. pose proof (Z.div_mod n 8 ltac:(lia)) as DMn.
  pose proof (div8_bounds (a - B)) as Da. pose proof (Z.div_mod (a - B) 8 ltac:(lia)) as DMa. pose proof (Z.mod_pos_bound (a - B) 8 ltac:(lia)) as Ma.
  assert (L : length ks = (Z.to_nat (n / 8) + (if (n mod 8 =? 0)%Z then 0 else 1))%nat).
  { rewrite Hks, length_app, repeat_length. destruct (n mod 8 =? 0); reflexivity. }
  assert (Hi0 : 0 <= (a - B) / 8) by (apply Z.div_pos; lia).
  assert (AM : a mod 8 = (a - B) mod 8).
  { replace a with ((a - B) + B) at 1 by lia. rewrite Z.add_mod, AL, Z.add_0_r, Z.mod_mod by lia. reflexivity. }
  destruct (Z.lt_ge_cases ((a - B) / 8) (n / 8)) as [LT | GE].
  - apply (acc_of_chunk m B ks a SH AL ltac:(lia)); [rewrite L; lia|].
    left. rewrite Hks. apply nth_block_shadow_zero; [lia|]. rewrite Z2Nat.id by lia. exact LT.
  -
    assert (E : (a - B) / 8 = n / 8) by (pose proof (Z.div_le_mono (a - B) (n - 1) 8 ltac:(lia) ltac:(lia)); pose proof (div8_bounds (n-1)); lia).
    assert (NZ : n mod 8 <> 0) by lia.
    apply (acc_of_chunk m B ks a SH AL ltac:(lia)); [rewrite L, E; destruct (Z.eqb_spec (n mod 8) 0); [lia|]; lia|].
    right. rewrite E, Hks, nth_block_shadow_last by lia. rewrite AM. lia.
Qed.

Lemma sh_readable_of_chunk : forall m A0 ks A n,
  rw_cells asegs m (sh A0) (shadow_cells ks) ->
  sh A0 <= sh A - sh A mod 8 -> sh (A + n - 1) - sh (A + n - 1) mod 8 + 8 <= sh A0 + Z.of_nat (length ks) ->
  sh_readable m A n.
Proof.
  intros m A0 ks A n SH H1 H2 Hn a Ha. exists (Z_to_bv 8 (nth (Z.to_nat (a - sh A0)) ks 0)).
  replace a with (sh A0 + Z.of_nat (Z.to_nat (a - sh A0))) at 1 by lia. apply shadow_chunk_read; [exact SH| lia].
Qed.

Lemma mrd_munch : forall W m m' a, munch W m m' -> outside W a -> 0 <= a < 2^64 -> mrd asegs m' (wa a) = mrd asegs m (wa a).
Proof. intros W m m' a MU OUT Ha. unfold mrd. rewrite MU; [reflexivity|]. rewrite wa_unsigned by lia. exact OUT. Qed.

Lemma shband_range : forall a, shband a -> 0 <= a < 2^64.
Proof. intros a H. unfold shband, SH_LO, SH_HI in H. lia. Qed.

Lemma shz_frame : forall W m m' lo hi,
  shz m lo hi -> SH_LO <= lo -> hi <= SH_HI -> munch W m m' -> app_ivs W -> shz m' lo hi.
Proof.
  intros W m m' lo hi Z H1 H2 MU AW a Ha.
  assert (B : shband a) by (unfold shband; lia).
  rewrite (mrd_munch W m m' a MU (app_ivs_outside W a AW B) (shband_range a B)). apply Z. exact Ha.
Qed.

Lemma shr_frame : forall W m m' lo hi,
  shr m lo hi -> SH_LO <= lo -> hi <= SH_HI -> munch W m m' -> app_ivs W -> shr m' lo hi.
Proof.
  intros W m m' lo hi R H1 H2 MU AW a Ha.
  assert (B : shband a) by (unfold shband; lia).
  rewrite (mrd_munch W m m' a MU (app_ivs_outside W a AW B) (shband_range a B)). apply R. exact Ha.
Qed.

Lemma accessible_frame : forall W m m' A n,
  accessible m A n -> win_ok A n -> munch W m m' -> app_ivs W -> accessible m' A n.
Proof.
  intros W m m' A n AC WK MU AW a Ha. destruct (AC a Ha) as (k & BA & Hk). exists k. split; [|exact Hk].
  eapply bytes_at_transport; [exact BA | exact MU |]. cbn [length Z.of_nat Pos.of_succ_nat].
  apply app_ivs_disjoint; [exact AW|]. eapply win_ok_sh_band; eauto.
Qed.

Lemma sh_readable_frame : forall W m m' A n,
  sh_readable m A n -> win_ok A n -> munch W m m' -> app_ivs W -> sh_readable m' A n.
Proof.
  intros W m m' A n RD WK MU AW Hn a Ha. destruct (RD Hn a Ha) as (v & Hv). exists v.
  pose proof (win_ok_words_band A n a WK Hn Ha) as B.
  rewrite (mrd_munch W m m' a MU (app_ivs_outside W a AW B) (shband_range a B)). exact Hv.
Qed.

Lemma shw_frame : forall W m m' A n, shw m A n -> munch W m m' -> app_ivs W -> shw m' A n.
Proof.
  intros W m m' A n (AC & RD & WK) MU AW. split; [|split; [|exact WK]].
  - eapply accessible_frame; eauto.
  - eapply sh_readable_frame; eauto.
Qed.

Lemma munch_write1 : forall m a (bs : list byte), 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  munch [(a, a + Z.of_nat (length bs))] m (write_to_mem m (wa a) bs).
Proof. intros m a bs Ha Hb. apply munch_write; [apply munch_refl | lia | lia | cbn; lia]. Qed.

Lemma shw_store : forall m A n a (bs : list byte),
  shw m A n -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> app_iv (a, a + Z.of_nat (length bs)) ->
  shw (write_to_mem m (wa a) bs) A n.
Proof.
  intros m A n a bs H Ha Hb AW. eapply shw_frame; [exact H | apply munch_write1; lia | constructor; [exact AW | constructor]].
Qed.

Lemma shz_store : forall m lo hi a (bs : list byte),
  shz m lo hi -> SH_LO <= lo -> hi <= SH_HI -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> app_iv (a, a + Z.of_nat (length bs)) ->
  shz (write_to_mem m (wa a) bs) lo hi.
Proof.
  intros m lo hi a bs H H1 H2 Ha Hb AW. eapply shz_frame; [exact H | exact H1 | exact H2 | apply munch_write1; lia | constructor; [exact AW | constructor]].
Qed.

Lemma asan_env_store1 : forall m a (bs : list byte),
  asan_env asegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> env_safe [(a, a + Z.of_nat (length bs))] ->
  asan_env asegs (write_to_mem m (wa a) bs).
Proof.
  intros m a bs H Ha Hb ES. eapply asan_env_frame; [exact H | apply munch_write1; lia | apply wmono_write, wmono_refl | exact ES].
Qed.

Ltac app_iv_tac :=
  cbn [fst snd];
  first [ apply app_iv_low; lia
        | apply app_iv_stack; lia
        | apply app_iv_high; lia
        | match goal with H : app_iv _ |- _ => eapply (app_iv_sub _ _ _ _ H); cbn [fst snd]; lia end
        | match goal with H : win_ok ?X ?n |- _ => eapply (app_iv_of_win_ok X n _ _ H); lia end
        | match goal with H : shw _ ?X ?n |- _ => eapply (app_iv_of_win_ok X n _ _ (proj2 (proj2 H))); lia end
        | unfold app_iv, SH_HI in *; cbn [fst snd] in *; pose proof (@alloc_ceiling_bounds _); lia ].
Ltac app_ivs_tac := unfold app_ivs; repeat (apply Forall_cons; [ app_iv_tac | ]); apply Forall_nil.

Definition env_iv (iv : Z * Z) : Prop := env_safe [iv].
Lemma env_safe_Forall : forall W, env_safe W <-> Forall env_iv W.
Proof.
  intros W; unfold env_iv, env_safe; split; intro H.
  - induction H; constructor; [constructor; [assumption| constructor] | assumption].
  - induction H as [| x l H1 H2 IH]; constructor; [inversion H1; assumption | exact IH].
Qed.

Ltac env_band := lazymatch goal with |- _ \/ _ => first [ left; lia | right; env_band ] | |- _ => lia end.
Lemma env_iv_of : forall L a b a' b', env_safe L -> In (a, b) L -> a <= a' -> b' <= b -> env_iv (a', b').
Proof.
  intros L a b a' b' H HIn H1 H2. pose proof (proj1 (Forall_forall _ _) H _ HIn) as D.
  unfold env_iv, env_safe. constructor; [| constructor]. cbn [fst snd] in *. clear - D H1 H2.

  repeat (destruct D as [D|D]; [env_band|]); env_band.
Qed.
Ltac env_in_tac := cbn [In]; repeat (first [left; reflexivity | right]).

Ltac env_try L H :=
  lazymatch L with
  | (?a, ?b) :: ?L' => first [ eapply (env_iv_of _ a b _ _ H); [ env_in_tac | lia | lia ] | env_try L' H ]
  end.
Ltac env_iv_tac :=
  cbn [fst snd];
  first [ unfold env_iv, env_safe; apply Forall_cons;
            [ cbn [fst snd]; first [ env_band | pose proof (@alloc_ceiling_bounds _); env_band ] | apply Forall_nil ]
        | match goal with H : env_safe ?L |- _ => env_try L H end ].
Ltac env_safe_tac := apply (proj2 (env_safe_Forall _)); repeat (apply Forall_cons; [ env_iv_tac | ]); apply Forall_nil.

Ltac shadow_after_store m a bs n Hn Ha Hl :=
  repeat match goal with
  | H : shw m ?A ?k |- _ =>
      first [ apply (shw_store m A k a bs) in H; [ | exact Ha | rewrite <- Hn; exact Hl | rewrite <- Hn; app_iv_tac ]
            | idtac "note: dropping shw hypothesis (store not provably in app memory):" H; clear H ]
  | H : shz m ?lo ?hi |- _ =>
      first [ apply (shz_store m lo hi a bs) in H; [ | unfold SH_LO; lia | unfold SH_HI; lia | exact Ha | rewrite <- Hn; exact Hl | rewrite <- Hn; app_iv_tac ]
            | idtac "note: dropping shz hypothesis:" H; clear H ]
  | H : asan_env _ m |- _ =>
      first [ apply (asan_env_store1 m a bs) in H; [ | exact Ha | rewrite <- Hn; exact Hl | rewrite <- Hn; env_safe_tac ]
            | idtac "note: dropping asan_env hypothesis (store not provably env_safe):" H; clear H ]
  end.

Ltac shadow_after_call segs W m m' MU WM :=
  repeat match goal with
  | H : shw m ?A ?k |- _ =>
      first [ apply (shw_frame W m m' A k H MU) in H || (eapply (shw_frame W m m' A k) in H; [ | exact MU | app_ivs_tac ])
            | idtac "note: dropping shw hypothesis (callee footprint not provably app memory):" H; clear H ]
  | H : shz m ?lo ?hi |- _ =>
      first [ eapply (shz_frame W m m' lo hi) in H; [ | unfold SH_LO; lia | unfold SH_HI; lia | exact MU | app_ivs_tac ]
            | idtac "note: dropping shz hypothesis:" H; clear H ]
  | H : asan_env segs m |- _ =>
      first [ eapply (asan_env_frame segs m m' W) in H; [ | exact MU | exact WM | env_safe_tac ]
            | idtac "note: dropping asan_env hypothesis (callee footprint not provably env_safe):" H; clear H ]
  end.
