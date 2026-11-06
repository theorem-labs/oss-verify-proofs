(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling InitStack.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).
Notation wz := (Z_to_bv 64) (only parsing).

Definition env_layout (m : mem) : Prop :=
  rw_cells asegs m 0xaa0d8 [C8 (Z_to_bv 64 0xb45e8); C8 (Z_to_bv 64 0xb45f0); C8 (Z_to_bv 64 0xb45e0)]
  /\ rw_cells asegs m 0xb45e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition env_shadow (m : mem) : Prop :=
  rw_cells asegs m 0xaa0d0 [C8 (Z_to_bv 64 0xb38f8)] /\ rw_cells asegs m 0xb38f8 [C8 (Z_to_bv 64 0x7fff8000)].
Lemma env_shadow_of_globals : forall m, asan_globals asegs m -> env_shadow m.
Proof. intros m (G1 & G2 & _). split; assumption. Qed.

Definition env_inited (m : mem) : Prop := rw_cells asegs m 0xb45d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].

Definition env_ric (m : mem) : Prop := rw_cells asegs m 0xaac38 [C8 (Z_to_bv 64 0xb45d9)].

Definition env_real_mem (m : mem) : Prop := rw_cells asegs m 0xabf78 [C8 (Z_to_bv 64 0xa1e18); C8 (Z_to_bv 64 0xa221c)].

Definition env_cf (m : mem) : Prop := rw_cells asegs m 0xaa0c0 [C8 (Z_to_bv 64 0x145428); C8 (Z_to_bv 64 0xb10f8)].

Definition env_flags (m : mem) : Prop :=
  rw_cells asegs m 0x145518 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
                            C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].

Definition env_real_str (m : mem) : Prop :=
  rw_cells asegs m 0xabde8 [C8 (Z_to_bv 64 0xa2468)] /\ rw_cells asegs m 0xabe20 [C8 (Z_to_bv 64 0xa1d1c)]
  /\ rw_cells asegs m 0xabf28 [C8 (Z_to_bv 64 0xa27c8)].
Definition env_real_io (m : mem) : Prop :=
  rw_cells asegs m 0xabe30 [C8 (Z_to_bv 64 0xa8a84); C8 (Z_to_bv 64 0x9b0bc)]
  /\ rw_cells asegs m 0xabe68 [C8 (Z_to_bv 64 0xa1628); C8 (Z_to_bv 64 0x9b344)].

Definition env_ckpf (m : mem) : Prop :=
  rw_cells asegs m 0x145478 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

Definition env_aflags (m : mem) : Prop :=
  rw_cells asegs m 0xb1110 [C4 (Z_to_bv 64 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].

Definition env_real_lib (m : mem) : Prop :=
  rw_cells asegs m 0xabe08 [C8 (Z_to_bv 64 0xa280c)]
  /\ rw_cells asegs m 0xabe58 [C8 (Z_to_bv 64 0xa17ec); C8 (Z_to_bv 64 0x9dd7c)]
  /\ rw_cells asegs m 0xabe88 [C8 (Z_to_bv 64 0x999cc)]
  /\ rw_cells asegs m 0xabf50 [C8 (Z_to_bv 64 0xa1afc); C8 (Z_to_bv 64 0xa1c64); C8 (Z_to_bv 64 0xa192c)].

Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac fold_lits :=
  repeat match goal with
  | |- context [Z.b2z (?a <? ?b)%Z] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (a <? b)%Z) in change (Z.b2z (a <? b)%Z) with v
  | |- context [Z.b2z (?a =? ?b)%Z] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (a =? b)%Z) in change (Z.b2z (a =? b)%Z) with v
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.modulo ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v
  | |- context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  end.

Lemma mrd_munch : forall W (m m' : mem) a, munch W m m' -> 0 <= a < 2^64 -> outside W a ->
  mrd asegs m' (wa a) = mrd asegs m (wa a).
Proof. intros W m m' a MU Ha HO. unfold mrd. rewrite (MU (wa a)); [reflexivity|]. rewrite wa_unsigned by lia. exact HO. Qed.

Definition zrun (m : mem) (lo hi : Z) : Prop := forall a, lo <= a < hi -> mrd asegs m (wa a) = Some (Z_to_bv 8 0).
Lemma zrun_sub : forall m lo hi lo' hi', zrun m lo hi -> lo <= lo' -> hi' <= hi -> zrun m lo' hi'.
Proof. intros m lo hi lo' hi' H H1 H2 a Ha. apply H. lia. Qed.
Lemma zrun_munch : forall W m m' lo hi, zrun m lo hi -> munch W m m' -> 0 <= lo -> hi <= 2^64 ->
  (forall a, lo <= a < hi -> outside W a) -> zrun m' lo hi.
Proof. intros W m m' lo hi H MU H0 H1 HO a Ha. rewrite (mrd_munch W m m' a MU) by (try apply HO; lia). apply H. exact Ha. Qed.

Lemma bytes_at_of_mrd : forall (m : mem) n a, 0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall i, (i < n)%nat -> exists v, mrd asegs m (wa (a + Z.of_nat i)) = Some v) ->
  exists bs, length bs = n /\ bytes_at asegs m a bs.
Proof.
  intros m n. induction n as [|n IH]; intros a H0 H1 H.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as [v0 Hv0]. rewrite Z.add_0_r in Hv0.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & L & (_ & _ & B)).
    { intros i Hi. destruct (H (S i) ltac:(lia)) as [v Hv]. exists v. rewrite <- Hv. f_equal. f_equal. lia. }
    exists (v0 :: bs). split; [cbn; lia|]. split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi; cbn [nth_error].
    + rewrite Z.add_0_r. exact Hv0.
    + rewrite <- (B i) by (cbn in Hi; lia). f_equal. f_equal. lia.
Qed.

Lemma ov_read_of_bytes_at : forall (m : mem) a bs,
  bytes_at asegs m a bs -> ov_read_bytes asegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read asegs m a bs 0 (length bs) H ltac:(lia)) as R.
  rewrite Z.add_0_r in R. cbn [skipn] in R. rewrite firstn_all in R. exact R.
Qed.

Lemma ov_read1_mrd : forall (m : mem) s b, 0 <= s -> s + 1 <= 2^64 -> mrd asegs m (wa s) = Some b ->
  ov_read_bytes asegs m (wa s) 1 = Some [b].
Proof.
  intros m s b A B H. apply (ov_read_of_bytes_at m s [b]). split; [lia|]. split; [cbn; lia|].
  intros [|i] Hi; cbn in Hi; [|lia]. cbn [nth_error]. rewrite Z.add_0_r. exact H.
Qed.

Lemma ov_read8_exists : forall (m : mem) s, 0 <= s -> s + 8 <= 2^64 ->
  (forall a, s <= a < s + 8 -> exists v, mrd asegs m (wa a) = Some v) ->
  exists w : word, ov_read_bytes asegs m (wa s) 8 = Some (le8 w).
Proof.
  intros m s H0 H1 H. destruct (bytes_at_of_mrd m 8 s H0 ltac:(lia)) as (bs & L & B).
  { intros i Hi. apply H. lia. }
  exists (le_bytes_to_word bs). rewrite (le8_of_bytes bs L). rewrite <- L at 1. apply ov_read_of_bytes_at. exact B.
Qed.

Lemma ov_read8_zrun : forall (m : mem) s, 0 <= s -> s + 8 <= 2^64 -> zrun m s (s + 8) ->
  ov_read_bytes asegs m (wa s) 8 = Some (le8 (Z_to_bv 64 0)).
Proof.
  intros m s H0 H1 H.
  assert (B : bytes_at asegs m s (le8 (Z_to_bv 64 0))).
  { split; [lia|]. split; [cbn; lia|]. intros i Hi. change (length (le8 (Z_to_bv 64 0))) with 8%nat in Hi.
    rewrite (H (s + Z.of_nat i)) by lia.
    do 8 (destruct i as [|i]; [reflexivity|]). lia. }
  exact (ov_read_of_bytes_at m s _ B).
Qed.

Definition cwin (A n : Z) : Prop :=
  0 <= n /\ ((4096 <= A /\ A + n <= 0x7fff7000) \/ (0x10007fff8000 <= A /\ A + n <= 2^47)).

Lemma sh_div8 : forall a, 8 * (sh a - SHADOW_OFF) <= a < 8 * (sh a - SHADOW_OFF) + 8.
Proof. intros a. unfold sh. pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). lia. Qed.
Lemma sh_mono : forall a b, a <= b -> sh a <= sh b.
Proof. intros a b H. unfold sh. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.
Lemma cwin_sh_band : forall A n a, cwin A n -> A <= a < A + n -> 0x7fff8000 <= sh a < 0x10007fff8000.
Proof. intros A n a [Hn W] Ha. pose proof (sh_div8 a). unfold SHADOW_OFF in *. lia. Qed.

Lemma acc_full_zero : forall m A n s, accessible m A n -> sh A <= s -> 8 * (s - SHADOW_OFF) + 8 <= A + n ->
  mrd asegs m (wa s) = Some (Z_to_bv 8 0).
Proof.
  intros m A n s AC H1 H2. pose proof (sh_div8 A) as DA.
  destruct (AC (8 * (s - SHADOW_OFF) + 7) ltac:(lia)) as (k & (_ & _ & B) & Hk).
  assert (E : sh (8 * (s - SHADOW_OFF) + 7) = s).
  { unfold sh. replace (8 * (s - SHADOW_OFF) + 7) with (7 + (s - SHADOW_OFF) * 8) by lia. rewrite Z.div_add by lia. change (7 / 8) with 0. lia. }
  assert (M : (8 * (s - SHADOW_OFF) + 7) mod 8 = 7).
  { replace (8 * (s - SHADOW_OFF) + 7) with (7 + (s - SHADOW_OFF) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  specialize (B 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r, E in B. cbn [nth_error] in B.
  rewrite B. destruct Hk as [->|Hk]; [reflexivity| lia].
Qed.
Lemma acc_core_zrun : forall m A n lo hi, accessible m A n -> sh A <= lo -> 8 * (hi - SHADOW_OFF) <= A + n -> zrun m lo hi.
Proof. intros m A n lo hi AC H1 H2 s Hs. eapply acc_full_zero; [exact AC| lia| lia]. Qed.

Lemma acc_byte : forall m A n a, accessible m A n -> A <= a < A + n ->
  exists k, mrd asegs m (wa (sh a)) = Some (Z_to_bv 8 k) /\ (k = 0 \/ (0 < k < 8 /\ a mod 8 < k)).
Proof.
  intros m A n a AC Ha. destruct (AC a Ha) as (k & (_ & _ & B) & Hk). exists k. split; [|exact Hk].
  specialize (B 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in B. exact B.
Qed.

Lemma probe8 : forall m A n x, sh_readable m A n -> 0 <= A -> A + n <= 2^64 -> A <= x < A + n ->
  exists w : word, ov_read_bytes asegs m (wa (sh x - sh x mod 8)) 8 = Some (le8 w).
Proof.
  intros m A n x RD H0 H1 Hx.
  pose proof (sh_mono A x ltac:(lia)) as M1. pose proof (sh_mono x (A + n - 1) ltac:(lia)) as M2.
  assert (S0 : 0 <= sh A) by (unfold sh, SHADOW_OFF; pose proof (Z.div_pos A 8); lia).
  assert (S1 : sh (A + n - 1) < 2^62) by (unfold sh, SHADOW_OFF; pose proof (Z.div_lt_upper_bound (A + n - 1) 8 (2^61)); lia).
  apply ov_read8_exists.
  - Z.div_mod_to_equations; lia.
  - Z.div_mod_to_equations; lia.
  - intros a Ha. apply RD; [lia|]. Z.div_mod_to_equations; lia.
Qed.

Lemma accessible_munch : forall W m m' A n, accessible m A n -> munch W m m' -> cwin A n ->
  (forall s, 0x7fff8000 <= s < 0x10007fff8000 -> outside W s) -> accessible m' A n.
Proof.
  intros W m m' A n AC MU CW HO a Ha. destruct (AC a Ha) as (k & (B0 & B1 & B) & Hk). exists k. split; [|exact Hk].
  split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. assert (i = 0%nat) as -> by lia. rewrite Z.add_0_r.
  pose proof (cwin_sh_band A n a CW Ha) as BD.
  rewrite (mrd_munch W m m' (sh a) MU) by (try apply HO; lia). specialize (B 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in B. exact B.
Qed.
Lemma sh_readable_munch : forall W m m' A n, sh_readable m A n -> munch W m m' -> cwin A n ->
  (forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside W s) -> sh_readable m' A n.
Proof.
  intros W m m' A n RD MU CW HO Hn a Ha.
  assert (BD : 0x7fff7000 <= a < 0x10007fff8000).
  { destruct CW as [_ CW]. pose proof (sh_div8 A). pose proof (sh_div8 (A + n - 1)). unfold SHADOW_OFF in *. Z.div_mod_to_equations; lia. }
  rewrite (mrd_munch W m m' a MU) by (try apply HO; lia). apply RD; assumption.
Qed.

Definition rwin (A n : Z) : Prop := (4096 <= A /\ A + n <= 0x7fff7000) \/ (0x10007fff8000 <= A /\ A + n < 2^47).
Lemma rwin_cwin : forall A n, rwin A n -> 0 <= n -> cwin A n.
Proof. unfold rwin, cwin. intros. lia. Qed.

Lemma sxb_small : forall k, 0 <= k < 128 -> sxb (Z_to_bv 8 k) = Z_to_bv 64 k.
Proof.
  intros k Hk. unfold sxb. f_equal. unfold bv_signed. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 8 / 2) with 128.
  rewrite (Z.mod_small k 256) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma signed_small64 : forall z, - 2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.
Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Ltac zify_granule K :=
  rewrite ?land7_mod8 in K;
  repeat match type of K with
  | context [bv_signed (Z_to_bv 64 ?z)] =>
      rewrite (signed_small64 z) in K
        by (repeat match goal with |- context [?x mod 8] => lazymatch goal with _ : 0 <= x mod 8 < 8 |- _ => fail | _ => pose proof (Z.mod_pos_bound x 8 ltac:(lia)) end end; lia)
  end.

Lemma acc_byte_rd : forall m A n a, accessible m A n -> A <= a < A + n -> 0 <= A -> A + n <= 2^64 ->
  exists k, ov_read_bytes asegs m (wa (sh a)) 1 = Some [Z_to_bv 8 k] /\ (k = 0 \/ (0 < k < 8 /\ a mod 8 < k)).
Proof.
  intros m A n a AC Ha H0 H1. destruct (acc_byte m A n a AC Ha) as (k & R & Hk). exists k. split; [|exact Hk].
  pose proof (sh_div8 a). apply ov_read1_mrd; [unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia | exact R].
Qed.

Lemma aip_zero : forall off k, 0 <= off < 8 -> (k = 0 \/ (0 < k < 8 /\ off < k)) ->
  Z.land (Z.b2z (0 <? k)) (Z.lxor (Z.b2z (Z.lxor off 9223372036854775808 <? Z.lxor k 9223372036854775808)) 1) = 0.
Proof.
  intros off k Ho Hk.
  assert (Ek : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  assert (Eo : off = 0 \/ off = 1 \/ off = 2 \/ off = 3 \/ off = 4 \/ off = 5 \/ off = 6 \/ off = 7) by lia.
  destruct Ek as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; destruct Eo as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; first [ reflexivity | exfalso; lia ].
Qed.

Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.

Lemma probe8_at : forall m A n x (a : Z), sh_readable m A n -> 0 <= A -> A + n <= 2^64 -> A <= x < A + n ->
  a = sh x - sh x mod 8 -> exists w : word, ov_read_bytes asegs m (Z_to_bv 64 a) 8 = Some (le8 w).
Proof. intros m A n x a RD H0 H1 Hx ->. exact (probe8 m A n x RD H0 H1 Hx). Qed.

Lemma align8_walk : forall x, 0 <= x < 2^47 ->
  Z.land ((2147450880 + Z.shiftr x 3) mod 18446744073709551616) 18446744073709551608 = sh x - sh x mod 8.
Proof.
  intros x Hx. rewrite shiftr3_div. assert (0 <= x / 8 < 2^44) by (Z.div_mod_to_equations; lia).
  rewrite Z.mod_small by lia. change 18446744073709551608 with (2^64 - 2^3). rewrite land_align_down by lia.
  unfold sh, SHADOW_OFF. change (2^3) with 8. replace (x / 8 + 2147450880) with (2147450880 + x / 8) by lia. reflexivity.
Qed.
Lemma align8_walk' : forall x, 0 <= x < 2^47 ->
  Z.land ((Z.shiftr x 3 + 2147450880) mod 18446744073709551616) 18446744073709551608 = sh x - sh x mod 8.
Proof. intros x Hx. rewrite (Z.add_comm (Z.shiftr x 3)). apply align8_walk. exact Hx. Qed.

Tactic Notation "probe8_reg" constr(r) constr(RD) constr(x) ident(w) ident(Pw) :=
  let a := reg_val r in
  lazymatch a with Z_to_bv 64 ?e =>
    lazymatch type of RD with sh_readable ?mm ?A ?nn =>
      destruct (probe8_at mm A nn x e RD ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(first [ apply align8_walk; lia | apply align8_walk'; lia ])) as [w Pw]
    end end.

Definition env_real_lib2 (m : mem) : Prop := rw_cells asegs m 0xabf48 [C8 (Z_to_bv 64 0xa2690)].

Definition env_got_rms (m : mem) : Prop := rw_cells asegs m 0xaa0f0 [C8 (Z_to_bv 64 0xabf80)].
Definition env_got_rmem (m : mem) : Prop := rw_cells asegs m 0xaa0f8 [C8 (Z_to_bv 64 0xabf78)].

Definition env_real_cmp (m : mem) : Prop :=
  rw_cells asegs m 0xabe10 [C8 (Z_to_bv 64 0xa2314)] /\ rw_cells asegs m 0xabe18 [C8 (Z_to_bv 64 0xa1de8)].

Definition icpt_env (m : mem) : Prop :=
  env_shadow m /\ env_layout m /\ env_inited m /\ env_ric m /\ env_real_mem m
  /\ env_cf m /\ env_flags m /\ env_real_str m /\ env_real_io m
  /\ env_ckpf m /\ env_aflags m /\ env_real_lib m /\ env_real_lib2 m /\ env_got_rms m /\ env_got_rmem m /\ env_real_cmp m.
Lemma ie_shadow : forall m, icpt_env m -> env_shadow m. Proof. intros m H; apply H. Qed.
Lemma ie_layout : forall m, icpt_env m -> env_layout m. Proof. intros m H; apply H. Qed.
Lemma ie_inited : forall m, icpt_env m -> env_inited m. Proof. intros m H; apply H. Qed.
Lemma ie_ric : forall m, icpt_env m -> env_ric m. Proof. intros m H; apply H. Qed.
Lemma ie_real_mem : forall m, icpt_env m -> env_real_mem m. Proof. intros m H; apply H. Qed.
Lemma ie_cf : forall m, icpt_env m -> env_cf m. Proof. intros m H; apply H. Qed.
Lemma ie_flags : forall m, icpt_env m -> env_flags m. Proof. intros m H; apply H. Qed.
Lemma ie_real_str : forall m, icpt_env m -> env_real_str m. Proof. intros m H; apply H. Qed.
Lemma ie_real_io : forall m, icpt_env m -> env_real_io m. Proof. intros m H; apply H. Qed.
Lemma ie_ckpf : forall m, icpt_env m -> env_ckpf m. Proof. intros m H; apply H. Qed.
Lemma ie_aflags : forall m, icpt_env m -> env_aflags m. Proof. intros m H; apply H. Qed.
Lemma ie_real_lib : forall m, icpt_env m -> env_real_lib m. Proof. intros m H; apply H. Qed.
Lemma ie_real_lib2 : forall m, icpt_env m -> env_real_lib2 m. Proof. intros m H; apply H. Qed.
Lemma ie_got_rms : forall m, icpt_env m -> env_got_rms m. Proof. intros m H; apply H. Qed.
Lemma ie_got_rmem : forall m, icpt_env m -> env_got_rmem m. Proof. intros m H; apply H. Qed.
Lemma ie_real_cmp : forall m, icpt_env m -> env_real_cmp m. Proof. intros m H; apply H. Qed.

Definition env_band_safe (W : list ivl) : Prop := Forall (fun iv => snd iv <= 0xa9000 \/ 0x146000 <= fst iv) W.
Lemma env_band_disjoint : forall W A n, env_band_safe W -> 0xa9000 <= A -> A + n <= 0x146000 -> disjoint_from W A n.
Proof.
  intros W A n SAFE H1 H2. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  inversion SAFE as [|x l S1 S2]; subst. split; [cbn in S1; lia| apply IH; exact S2].
Qed.
Lemma env_cell_frame : forall W m m' A cs, rw_cells asegs m A cs -> munch W m m' -> wmono asegs m m' -> env_band_safe W ->
  0xa9000 <= A -> A + Z.of_nat (cells_size cs) <= 0x146000 -> rw_cells asegs m' A cs.
Proof. intros W m m' A cs H MU WM SAFE H1 H2. eapply rw_cells_transport; [exact H| exact MU| exact WM| apply env_band_disjoint; assumption]. Qed.
Ltac ecf H MU WM SAFE := eapply env_cell_frame; [exact H| exact MU| exact WM| exact SAFE| lia| cbn [cells_size csize Nat.add]; lia].
Lemma icpt_env_frame : forall W m m', icpt_env m -> munch W m m' -> wmono asegs m m' -> env_band_safe W -> icpt_env m'.
Proof.
  intros W m m' IE MU WM SAFE.
  destruct IE as ((G1 & G2) & (L1 & L2) & I1 & R1 & M1 & C1 & F1 & (S1 & S2 & S3) & (O1 & O2) & K1 & A1 & (B1 & B2 & B3 & B4) & B5 & B6 & B7 & (B8a & B8b)).
  unfold icpt_env, env_shadow, env_layout, env_inited, env_ric, env_real_mem, env_cf, env_flags, env_real_str, env_real_io, env_ckpf, env_aflags, env_real_lib, env_real_lib2, env_got_rms, env_got_rmem, env_real_cmp in *.
  split; [split; [ecf G1 MU WM SAFE | ecf G2 MU WM SAFE]|]. split; [split; [ecf L1 MU WM SAFE | ecf L2 MU WM SAFE]|].
  split; [ecf I1 MU WM SAFE|]. split; [ecf R1 MU WM SAFE|]. split; [ecf M1 MU WM SAFE|]. split; [ecf C1 MU WM SAFE|]. split; [ecf F1 MU WM SAFE|].
  split; [split; [ecf S1 MU WM SAFE| split; [ecf S2 MU WM SAFE| ecf S3 MU WM SAFE]]|]. split; [split; [ecf O1 MU WM SAFE| ecf O2 MU WM SAFE]|].
  split; [ecf K1 MU WM SAFE|]. split; [ecf A1 MU WM SAFE|].
  split; [split; [ecf B1 MU WM SAFE| split; [ecf B2 MU WM SAFE| split; [ecf B3 MU WM SAFE| ecf B4 MU WM SAFE]]]|].
  split; [ecf B5 MU WM SAFE|]. split; [ecf B6 MU WM SAFE|]. split; [ecf B7 MU WM SAFE|]. split; [ecf B8a MU WM SAFE| ecf B8b MU WM SAFE].
Qed.
Lemma icpt_env_stack : forall lo q m m', icpt_env m -> munch [(lo, q)] m m' -> wmono asegs m m' -> 0x146000 <= lo -> icpt_env m'.
Proof. intros lo q m m' IE MU WM H. eapply icpt_env_frame; [exact IE| exact MU| exact WM|]. constructor; [cbn; lia| constructor]. Qed.

Lemma icpt_env_of_zaw : forall m, ZAW.Shadow.icpt_env asegs m -> icpt_env m.
Proof. intros m H. exact H. Qed.
Lemma icpt_env_of_asan_env : forall m, asan_env asegs m -> icpt_env m.
Proof. intros m H. exact (icpt_env_of_zaw m (asan_env_icpt asegs m H)). Qed.

Definition ihide (X : Prop) : Prop := X.
Ltac ihide H := lazymatch type of H with ?T => change (ihide T) in H end.
Ltac iunhide H := unfold ihide in H.
