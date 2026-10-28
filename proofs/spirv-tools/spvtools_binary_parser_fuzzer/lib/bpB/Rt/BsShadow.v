(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition mem := word -> option byte.

Definition AHI_LO  : Z := 0x10007fff8000.
Definition AAPP_HI : Z := 2^47.
Definition ALOWSH_LO : Z := 0x7fff7000.

Definition sh (a : Z) : Z := ASHADOW_BASE + a / 8.

Lemma ASHADOW_BASE_val : ASHADOW_BASE = 0x7fff8000. Proof. reflexivity. Qed.

Lemma sh_shiftr : forall a, 0 <= a -> Z.shiftr a 3 + ASHADOW_BASE = sh a.
Proof. intros a Ha. unfold sh. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.

Lemma sh_shiftr' : forall a, 0 <= a -> ASHADOW_BASE + Z.shiftr a 3 = sh a.
Proof. intros a Ha. rewrite <- sh_shiftr by lia. lia. Qed.

Lemma sh_mono : forall a b, a <= b -> sh a <= sh b.
Proof. intros a b H. unfold sh. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.

Lemma sh_add8 : forall a k, sh (a + 8 * k) = sh a + k.
Proof. intros a k. unfold sh. rewrite Z.add_comm with (n := a). rewrite Z.mul_comm, Z.div_add_l by lia. lia. Qed.

Lemma sh_rel : forall A a, A mod 8 = 0 -> A <= a -> sh a = sh A + (a - A) / 8.
Proof. intros A a HA Hle. unfold sh. Z.div_mod_to_equations. nia. Qed.

Lemma sh_above_image : forall a, 0 <= a -> AIMG_TOP <= sh a.
Proof. intros a H. unfold sh, AIMG_TOP, ASHADOW_BASE. Z.div_mod_to_equations. lia. Qed.

Lemma sh_below_app : forall a, 0 <= a < AAPP_HI -> sh a < AHI_LO.
Proof. intros a H. unfold sh, AHI_LO, AAPP_HI, ASHADOW_BASE in *. lia. Qed.

Definition in_app_mem (lo hi : Z) : Prop :=
  (0 <= lo /\ hi + 8 <= ASHADOW_BASE) \/ (AHI_LO <= lo /\ hi + 8 <= AAPP_HI).

Lemma in_app_mem_sub : forall lo hi lo' hi', in_app_mem lo hi -> lo <= lo' -> hi' <= hi -> in_app_mem lo' hi'.
Proof. intros lo hi lo' hi' H ? ?. unfold in_app_mem in *. lia. Qed.

Definition nsh (n : Z) : Z := (n + 7) / 8.

Lemma sh_nsh_high : forall A n, 0 <= A -> 0 <= n -> A + n <= AAPP_HI -> sh A + nsh n <= AHI_LO.
Proof. intros A n HA Hn Htop. unfold sh, nsh, AHI_LO, AAPP_HI, ASHADOW_BASE in *. Z.div_mod_to_equations. lia. Qed.

Section Placement.
  Context {HCEIL : HeapCeil}.

  Definition aceil : Z := hceil - hceil mod 4096.

  Lemma aceil_facts : 0x7fff7f800000 <= aceil <= 0x7fffff800000 /\ aceil mod 4096 = 0 /\ aceil <= hceil < aceil + 4096.
  Proof. hcb. unfold aceil. Z.div_mod_to_equations. lia. Qed.

  Lemma aceil_al8 : aceil mod 8 = 0.                    Proof. pose proof aceil_facts. Z.div_mod_to_equations. lia. Qed.
  Lemma aceil_range : 0x7fff7f800000 <= aceil <= 0x7fffff800000.  Proof. pose proof aceil_facts. lia. Qed.

  Lemma grant_below_aceil : forall a len, a mod 4096 = 0 -> len mod 4096 = 0 -> a + len <= hceil -> a + len <= aceil.
  Proof. intros a len Ha Hl H. unfold aceil. Z.div_mod_to_equations. lia. Qed.

  Definition aapp_lo (A n : Z) : Prop := AIMG_TOP <= A /\ A + n <= ALOWSH_LO.
  Definition aapp_hi (A n : Z) : Prop := AHI_LO <= A /\ A + n <= aceil.
  Definition aapp (A n : Z) : Prop := aapp_lo A n \/ aapp_hi A n.

  Lemma aapp_sub : forall A n A' n', aapp A n -> A <= A' -> A' + n' <= A + n -> aapp A' n'.
  Proof. intros A n A' n' H ? ?. unfold aapp, aapp_lo, aapp_hi in *. lia. Qed.

  Lemma aapp_bounds : forall A n, aapp A n -> 0 <= n -> AIMG_TOP <= A /\ A + n <= aceil /\ A + n < AAPP_HI /\ 0 < A /\ aceil <= hceil.
  Proof. intros A n H Hn. pose proof aceil_facts. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI in *. lia. Qed.

  Lemma aapp_in_app_mem : forall A n lo hi, aapp A n -> A <= lo -> hi <= A + n -> in_app_mem lo hi.
  Proof. intros A n lo hi H ? ?. pose proof aceil_facts. unfold aapp, aapp_lo, aapp_hi, in_app_mem, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE in *. lia. Qed.

  Lemma aapp_not_shadowland : forall A n, aapp A n -> A + n <= ALOWSH_LO \/ AHI_LO <= A.
  Proof. intros A n H. unfold aapp, aapp_lo, aapp_hi in H. lia. Qed.

  Lemma sh_in_shadowland : forall a, 0 <= a < AAPP_HI -> ALOWSH_LO + 0x1000 <= sh a < AHI_LO.
  Proof. intros a H. unfold sh, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE in *. lia. Qed.

  Lemma aapp_disjoint_sh : forall B k a j, aapp B k -> 0 <= a -> a + j <= AAPP_HI -> 0 <= j ->
    sh a + nsh j <= B \/ B + k <= sh a.
  Proof.
    intros B k a j HB Ha Hj Hj0. pose proof aceil_facts. unfold nsh.
    unfold aapp, aapp_lo, aapp_hi, sh, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE in *.
    Z.div_mod_to_equations. lia.
  Qed.

  Lemma sh_below_aceil : forall a, 0 <= a < AAPP_HI -> sh a < aceil.
  Proof. intros a H. pose proof aceil_facts. unfold sh, AAPP_HI, ASHADOW_BASE in *. lia. Qed.
  Lemma aapp_below_aceil : forall A n, aapp A n -> A + n <= aceil.
  Proof. intros A n H. pose proof aceil_facts. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO in *. lia. Qed.

  Lemma aapp_above_image : forall A n, aapp A n -> AIMG_TOP <= A.
  Proof. intros A n H. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO in *. lia. Qed.
  Lemma sh_aapp_range : forall A n, aapp A n -> 0 <= n -> sh AIMG_TOP <= sh A /\ sh A + nsh n <= sh aceil /\ sh aceil < AHI_LO.
  Proof.
    intros A n H Hn. pose proof aceil_facts. unfold nsh.
    unfold aapp, aapp_lo, aapp_hi, sh, AIMG_TOP, ALOWSH_LO, AHI_LO, ASHADOW_BASE in *.
    Z.div_mod_to_equations. lia.
  Qed.

  Lemma sh_aapp_lo_range : forall A n, aapp_lo A n -> 0 <= n -> 0x800d5000 <= sh A /\ sh A + nsh n <= 0x8fff6e00.
  Proof. intros A n H Hn. unfold nsh, aapp_lo, sh, AIMG_TOP, ALOWSH_LO, ASHADOW_BASE in *. Z.div_mod_to_equations. lia. Qed.
  Lemma sh_aapp_hi_range : forall A n, aapp_hi A n -> 0 <= n -> 0x2008fff7000 <= sh A /\ sh A + nsh n <= sh aceil /\ sh aceil < AHI_LO.
  Proof. intros A n H Hn. pose proof aceil_facts. unfold nsh, aapp_hi, sh, AHI_LO, ASHADOW_BASE in *. Z.div_mod_to_equations. lia. Qed.

End Placement.

Ltac acb :=
  let K := fresh "ACEILB" in
  pose proof (aceil_facts : 0x7fff7f800000 <= aceil <= 0x7fffff800000 /\ aceil mod 4096 = 0 /\ aceil <= hceil < aceil + 4096) as K.
Ltac aapp_unfold :=
  try acb; unfold aapp, aapp_lo, aapp_hi, in_app_mem, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE in *.

Definition shadow_of (n : Z) : list byte :=
  repeat (b8 0) (Z.to_nat (n / 8)) ++ (if Z.eqb (n mod 8) 0 then [] else [b8 (n mod 8)]).

Lemma shadow_of_length : forall n, 0 <= n -> Z.of_nat (length (shadow_of n)) = nsh n.
Proof.
  intros n Hn. unfold shadow_of, nsh. rewrite length_app, repeat_length.
  destruct (Z.eqb_spec (n mod 8) 0) as [E|E]; cbn [length]; Z.div_mod_to_equations; lia.
Qed.

Lemma shadow_of_mult8 : forall n, 0 <= n -> n mod 8 = 0 -> shadow_of n = repeat (b8 0) (Z.to_nat (n / 8)).
Proof. intros n Hn E. unfold shadow_of. rewrite E. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma shadow_of_nth_full : forall n i, 0 <= n -> (Z.of_nat i < n / 8) ->
  nth_error (shadow_of n) i = Some (b8 0).
Proof.
  intros n i Hn Hi. unfold shadow_of. rewrite nth_error_app1 by (rewrite repeat_length; lia).
  apply nth_error_repeat. lia.
Qed.

Lemma shadow_of_nth_last : forall n, 0 <= n -> n mod 8 <> 0 ->
  nth_error (shadow_of n) (Z.to_nat (n / 8)) = Some (b8 (n mod 8)).
Proof.
  intros n Hn E. unfold shadow_of. rewrite nth_error_app2 by (rewrite repeat_length; lia).
  rewrite repeat_length, Nat.sub_diag. destruct (Z.eqb_spec (n mod 8) 0); [lia| reflexivity].
Qed.

Definition poison_bytes (k : nat) (v : Z) : list byte := repeat (b8 v) k.

Definition SHAD (m : mem) (A : Z) (sbs : list byte) : Prop :=
  0 <= A /\ A mod 8 = 0 /\ u8arr asegs m (sh A) sbs.

Definition addressable (m : mem) (A n : Z) : Prop := 0 <= n /\ SHAD m A (shadow_of n).

Definition poisoned (m : mem) (A : Z) (k : nat) (v : Z) : Prop := SHAD m A (poison_bytes k v).

Definition byte_ok (v : Z) (x : Z) : Prop := v = 0 \/ (x mod 8) + 1 <= v.
Definition accessible (m : mem) (a n : Z) : Prop :=
  0 <= a /\ a + n <= AAPP_HI /\
  forall x, a <= x < a + n -> exists v, 0 <= v < 8 /\ mrd asegs m (wa (sh x)) = Some (b8 v) /\ byte_ok v x.

Lemma accessible_nil : forall m a, 0 <= a <= AAPP_HI -> accessible m a 0.
Proof. intros m a H. split; [lia|]. split; [lia|]. intros x Hx. lia. Qed.

Lemma accessible_sub : forall m a n a' n', accessible m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> accessible m a' n'.
Proof.
  intros m a n a' n' (H0 & H1 & H) ? ? ?. split; [lia|]. split; [lia|]. intros x Hx. apply H. lia.
Qed.

Lemma SHAD_bound : forall m A sbs, SHAD m A sbs -> 0 <= sh A /\ sh A + Z.of_nat (length sbs) <= 2^64.
Proof. intros m A sbs (_ & _ & U). exact (u8arr_bound _ _ _ _ U). Qed.

Lemma SHAD_read : forall m A sbs (i : Z) b x,
  SHAD m A sbs -> nth_error sbs (Z.to_nat i) = Some b -> 0 <= i -> x = wa (sh A + i) ->
  ov_read_bytes asegs m x 1 = Some [b].
Proof. intros m A sbs i b x (_ & _ & U) Hn Hi ->. eapply u8arr_read; eauto. Qed.

Lemma SHAD_read_at : forall m A sbs a b x,
  SHAD m A sbs -> A <= a -> nth_error sbs (Z.to_nat ((a - A) / 8)) = Some b -> x = wa (sh a) ->
  ov_read_bytes asegs m x 1 = Some [b].
Proof.
  intros m A sbs a b x SH Hle Hn ->. pose proof SH as (_ & HA & _).
  rewrite (sh_rel A a HA Hle). eapply SHAD_read; eauto. Z.div_mod_to_equations. lia.
Qed.

Lemma SHAD_mrd_at : forall m A sbs a b,
  SHAD m A sbs -> A <= a -> nth_error sbs (Z.to_nat ((a - A) / 8)) = Some b ->
  mrd asegs m (wa (sh a)) = Some b.
Proof.
  intros m A sbs a b SH Hle Hn. pose proof SH as (A0 & HA & [(B0 & B1 & HB) _]).
  pose proof (nth_error_lt _ _ _ Hn) as L.
  rewrite (sh_rel A a HA Hle). rewrite <- Hn.
  replace ((a - A) / 8) with (Z.of_nat (Z.to_nat ((a - A) / 8))) at 1 by (Z.div_mod_to_equations; nia).
  apply HB. exact L.
Qed.

Lemma addressable_read0 : forall m A n a x,
  addressable m A n -> A <= a -> 8 * ((a - A) / 8) + 8 <= n -> x = wa (sh a) ->
  ov_read_bytes asegs m x 1 = Some [b8 0].
Proof.
  intros m A n a x [Hn SH] Hle Hfull ->. pose proof SH as (_ & HA & _).
  eapply SHAD_read_at; eauto. apply shadow_of_nth_full; [lia|]. Z.div_mod_to_equations. nia.
Qed.

Lemma addressable_read0_w : forall m A n a w x,
  addressable m A n -> A <= a -> 1 <= w -> a + w <= A + 8 * (n / 8) -> x = wa (sh a) ->
  ov_read_bytes asegs m x 1 = Some [b8 0].
Proof.
  intros m A n a w x AD Hle Hw Hhi ->. pose proof AD as [Hn (_ & HA & _)].
  eapply addressable_read0; eauto. Z.div_mod_to_equations. nia.
Qed.

Lemma land7_mod8 : forall a, 0 <= a -> Z.land a 7 = a mod 8.
Proof. intros a Ha. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma b8_signed_small : forall v, 0 <= v < 128 -> bv_signed (b8 v) = v.
Proof.
  intros v Hv. unfold b8. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [N.sub Z.of_N Z.pow_pos Pos.iter Z.mul].
  change (2 ^ 8 / 2) with 128. change (2 ^ 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.

Lemma addressable_accessible : forall m A n a k,
  addressable m A n -> A <= a -> a + k <= A + n -> A + n <= AAPP_HI ->
  accessible m a k.
Proof.
  intros m A n a k AD Hle Hhi Htop. pose proof AD as [Hn (A0 & HA & U)].
  split; [lia|]. split; [lia|]. intros x Hx.
  destruct (Z.lt_ge_cases x (A + 8 * (n / 8))) as [FULL|PART].
  - exists 0. split; [lia|]. split; [| left; reflexivity].
    eapply SHAD_mrd_at; [split; [exact A0| split; [exact HA| exact U]] | lia |].
    apply shadow_of_nth_full; [lia|]. Z.div_mod_to_equations. nia.
  - assert (Hm : n mod 8 <> 0) by (Z.div_mod_to_equations; nia).
    exists (n mod 8). split; [Z.div_mod_to_equations; lia|]. split.
    + eapply SHAD_mrd_at; [split; [exact A0| split; [exact HA| exact U]] | lia |].
      replace ((x - A) / 8) with (n / 8) by (Z.div_mod_to_equations; nia).
      apply shadow_of_nth_last; lia.
    + right. Z.div_mod_to_equations. nia.
Qed.

Lemma SHAD_aligned : forall m A sbs, SHAD m A sbs -> 0 <= A /\ A mod 8 = 0. Proof. intros m A sbs (H0 & H & _). auto. Qed.

Lemma SHAD_transport : forall W m m' A sbs,
  SHAD m A sbs -> munch W m m' -> wmono asegs m m' -> disjoint_from W (sh A) (Z.of_nat (length sbs)) ->
  SHAD m' A sbs.
Proof. intros W m m' A sbs (A0 & HA & U) MU WM D. split; [exact A0|]. split; [exact HA| eapply u8arr_transport; eauto]. Qed.

Lemma addressable_transport : forall W m m' A n,
  addressable m A n -> munch W m m' -> wmono asegs m m' -> disjoint_from W (sh A) (nsh n) ->
  addressable m' A n.
Proof.
  intros W m m' A n [Hn SH] MU WM D. split; [exact Hn|]. eapply SHAD_transport; eauto.
  rewrite shadow_of_length by lia. exact D.
Qed.

Lemma accessible_transport : forall W m m' a n,
  accessible m a n -> munch W m m' -> (forall x, a <= x < a + n -> outside W (sh x)) -> accessible m' a n.
Proof.
  intros W m m' a n (A0 & A1 & AC) MU OUT. split; [exact A0|]. split; [exact A1|].
  intros x Hx. destruct (AC x Hx) as (v & V0 & RD & OK). exists v. split; [exact V0|]. split; [| exact OK].
  unfold mrd in *. unfold wa in *. rewrite MU; [exact RD|].
  rewrite unsigned_lit; [apply OUT; exact Hx|]. unfold sh, AAPP_HI, ASHADOW_BASE in *. Z.div_mod_to_equations. lia.
Qed.

Lemma SHAD_app : forall m A s1 s2,
  SHAD m A (s1 ++ s2) <-> SHAD m A s1 /\ SHAD m (A + 8 * Z.of_nat (length s1)) s2.
Proof.
  intros m A s1 s2. unfold SHAD, u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite sh_add8.
  split.
  - intros (A0 & HA & (B1 & B2) & (W1 & W2)). split; [split; [exact A0| split; [exact HA| split; assumption]]|].
    split; [lia|]. split; [Z.div_mod_to_equations; nia|]. split; assumption.
  - intros ((A0 & HA & B1 & W1) & (_ & _ & B2 & W2)). split; [exact A0|]. split; [exact HA|]. split; split; assumption.
Qed.

Lemma addressable_split8 : forall m A n k,
  addressable m A n -> n mod 8 = 0 -> k mod 8 = 0 -> 0 <= k <= n ->
  addressable m A k /\ addressable m (A + k) (n - k).
Proof.
  intros m A n k [Hn SH] En Ek Hk.
  rewrite shadow_of_mult8 in SH by lia.
  replace (Z.to_nat (n / 8)) with (Z.to_nat (k / 8) + Z.to_nat ((n - k) / 8))%nat in SH by (Z.div_mod_to_equations; nia).
  rewrite repeat_app in SH. apply SHAD_app in SH. destruct SH as [S1 S2].
  rewrite repeat_length in S2. replace (8 * Z.of_nat (Z.to_nat (k / 8))) with k in S2 by (Z.div_mod_to_equations; nia).
  split; (split; [lia|]); rewrite shadow_of_mult8 by (try lia; Z.div_mod_to_equations; nia); assumption.
Qed.

Lemma SHAD_rw_cells : forall m A sbs, SHAD m A sbs -> rw_cells asegs m (sh A) [CB (length sbs) sbs].
Proof. intros m A sbs (_ & _ & U). apply rw_cells_of_u8arr. exact U. Qed.

Lemma SHAD_of_rw_cells : forall m A n sbs, 0 <= A -> A mod 8 = 0 -> rw_cells asegs m (sh A) [CB n sbs] -> SHAD m A sbs.
Proof. intros m A n sbs A0 HA RC. split; [exact A0|]. split; [exact HA| eapply u8arr_of_rw_cells; exact RC]. Qed.

Definition hull_lo (a : Z) : Z := a - a mod 64.
Definition hull_hi (b : Z) : Z := b + (64 - b mod 64) mod 64.

Lemma hull_lo_le : forall a, 0 <= a -> hull_lo a <= a /\ a < hull_lo a + 64 /\ hull_lo a mod 64 = 0.
Proof. intros a Ha. unfold hull_lo. Z.div_mod_to_equations. nia. Qed.
Lemma hull_hi_ge : forall b, 0 <= b -> b <= hull_hi b /\ hull_hi b < b + 64 /\ hull_hi b mod 64 = 0.
Proof. intros b Hb. unfold hull_hi. Z.div_mod_to_equations. nia. Qed.

Definition shvis (m : mem) (lo hi : Z) : Prop := stk asegs m (sh (hull_lo lo)) (sh (hull_hi hi)).

Lemma shvis_sub : forall m lo hi lo' hi', shvis m lo hi -> 0 <= lo -> lo <= lo' -> hi' <= hi -> lo' <= hi' -> 0 <= hi ->
  shvis m lo' hi'.
Proof.
  intros m lo hi lo' hi' SV ? ? ? ? ?. unfold shvis in *.
  pose proof (hull_lo_le lo) as HL. pose proof (hull_lo_le lo') as HL'. pose proof (hull_hi_ge hi) as HH. pose proof (hull_hi_ge hi') as HH'.
  assert (L1 : sh (hull_lo lo) <= sh (hull_lo lo')). { apply sh_mono. unfold hull_lo in *. Z.div_mod_to_equations. nia. }
  assert (L2 : sh (hull_hi hi') <= sh (hull_hi hi)). { apply sh_mono. unfold hull_hi in *. Z.div_mod_to_equations. nia. }
  destruct SV as (S0 & S1 & SS). split; [lia|]. split; [lia|]. intros a Ha. apply SS. lia.
Qed.

Lemma shvis_transport : forall W m m' lo hi,
  shvis m lo hi -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W (sh (hull_lo lo)) (sh (hull_hi hi) - sh (hull_lo lo)) -> shvis m' lo hi.
Proof. intros. unfold shvis in *. eapply stk_transport_disjoint; eauto. Qed.
