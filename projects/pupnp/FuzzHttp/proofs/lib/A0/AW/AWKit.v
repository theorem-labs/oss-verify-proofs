(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StepFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
Import ListNotations.
Open Scope Z_scope.

Ltac a0_prologue AE0 W m :=
  pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR;
  pose proof (munch_refl W m) as MU; pose proof (wmono_refl asegs m) as WM;
  let AG := fresh "AG" in pose proof AE0 as AG; apply asan_env_globals in AG;
  destruct AG as (GOT & SHBASE & GOT2 & UAR);
  unfold A0_GOT_SHADOW, A0_SHADOW_CELL, A0_GOT_UAR, A0_UAR_CELL, SHADOW_OFF in GOT, SHBASE, GOT2, UAR.

Ltac env_now AE0 MU WM :=
  lazymatch type of MU with munch ?Ws ?ma ?mb =>
    repeat match goal with H : asan_env asegs ?mx |- _ => lazymatch mx with ma => fail | _ => clear H end end;
    let AE' := fresh "AE" in
    assert (AE' : asan_env asegs mb)
      by (eapply (asan_env_frame asegs ma mb Ws AE0 MU WM); unfold env_safe;
          repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil)
  end.

Ltac achk SH i APP := asan_check SH i APP 0x7fff8000%Z; try match goal with H : ov_read_bytes _ _ _ 1 = Some _ |- _ => clear H end.

Ltac release_to q := match goal with FR : rw_cells asegs ?mm ?a _, P : stk asegs ?mm _ ?a |- _ => release_frame FR P q end.

Lemma shadow_zero_sub : forall (m : word -> option byte) A k off n,
  rw_cells asegs m (sh A) (shadow_zero_cells k) -> A mod 8 = 0 -> off mod 8 = 0 -> 0 <= off ->
  (Z.to_nat (off / 8) + n <= k)%nat ->
  rw_cells asegs m (sh (A + off)) (shadow_zero_cells n).
Proof.
  intros m A k off n SH AL OL OP LE.
  set (i := Z.to_nat (off / 8)) in LE.
  assert (E : shadow_zero_cells k = shadow_zero_cells i ++ shadow_zero_cells n ++ shadow_zero_cells (k - i - n)).
  { unfold shadow_zero_cells. rewrite <- !shadow_cells_app, <- !repeat_app. f_equal. f_equal. lia. }
  rewrite E in SH. destruct (rw_cells_take3 asegs m (sh A) _ _ _ SH) as (_ & S2 & _).
  unfold shadow_zero_cells in S2 at 1. rewrite cells_size_shadow, repeat_length in S2.
  replace (sh (A + off)) with (sh A + Z.of_nat i); [exact S2|].
  unfold sh. subst i. rewrite Z2Nat.id by (apply Z.div_pos; lia).
  Z.div_mod_to_equations. nia.
Qed.

Ltac shw_now H MU :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
    lazymatch type of H with shw ma ?A ?n =>
      first [ apply (shw_frame W ma mb A n H MU) in H || (eapply (shw_frame W ma mb A n) in H; [ | exact MU | app_ivs_tac ])
            | fail 1 "shw_now: footprint not provably app memory for" H ] end end.

Lemma acc_load : forall (m : word -> option byte) APP (a : word), acc m APP -> a = wa (sh APP) ->
  exists k, ov_read_bytes asegs m a 1 = Some [Z_to_bv 8 k] /\ (k = 0 \/ (0 < k < 8 /\ APP mod 8 < k)).
Proof.
  intros m APP a (k & BA & Hk) ->. exists k. split; [| exact Hk].
  pose proof (bytes_at_ov_read asegs m (sh APP) [Z_to_bv 8 k] 0 1 BA ltac:(cbn; lia)) as R. cbn [firstn skipn] in R.
  rewrite <- R. f_equal. f_equal. cbn [Z.of_nat]. lia.
Qed.
Ltac acc_chk r APP HACC k SHR Hk :=
  let a := reg_val r in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (acc_load mm APP a HACC ltac:(shadow_addr_tac)) as (k & SHR & Hk) end.

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

Lemma acc_load0 : forall (m : word -> option byte) X n APP (a : word),
  accessible m X n -> X <= APP - APP mod 8 -> APP - APP mod 8 + 8 <= X + n -> a = wa (sh APP) ->
  ov_read_bytes asegs m a 1 = Some [Z_to_bv 8 0].
Proof.
  intros m X n APP a HA H1 H2 ->.
  destruct (HA (APP - APP mod 8 + 7) ltac:(lia)) as (k & BA & Hk).
  assert (E : sh (APP - APP mod 8 + 7) = sh APP) by (unfold sh; f_equal; Z.div_mod_to_equations; lia).
  assert (K0 : k = 0) by (destruct Hk as [Hk|[Hk1 Hk2]]; [exact Hk| exfalso; Z.div_mod_to_equations; lia]).
  subst k. rewrite E in BA.
  pose proof (bytes_at_ov_read asegs m (sh APP) [Z_to_bv 8 0] 0 1 BA ltac:(cbn; lia)) as R. cbn [firstn skipn] in R.
  rewrite <- R. f_equal. f_equal. cbn [Z.of_nat]. lia.
Qed.
Ltac acc_chk0 r APP HA :=
  let a := reg_val r in
  let SHR := fresh "SHR" in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of HA with accessible mm ?X ?n =>
      assert (SHR : ov_read_bytes asegs mm a 1 = Some [Z_to_bv 8 0])
        by (apply (acc_load0 mm X n APP a HA); [ Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | shadow_addr_tac ])
    end end.

Lemma rw_cells_reshape : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[W B] WR] W' EB ES. split; [split; [exact W'| rewrite EB; exact B]| rewrite ES; exact WR].
Qed.
Ltac reshape H cs' :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let H' := fresh in
    assert (H' : rw_cells segs m A cs') by (eapply (rw_cells_reshape segs m A cs cs' H); [cbn; repeat split; reflexivity| vm_compute; reflexivity| vm_compute; reflexivity]);
    clear H; rename H' into H end.

Lemma rw_cells_join3 : forall segs m A n1 bs1 (b : byte) n3 bs3 N,
  rw_cells segs m A [CB n1 bs1] -> rw_cells segs m (A + Z.of_nat n1) [C1 b] -> rw_cells segs m (A + Z.of_nat n1 + 1) [CB n3 bs3] ->
  N = (n1 + 1 + n3)%nat -> rw_cells segs m A [CB N (bs1 ++ [b] ++ bs3)].
Proof.
  intros segs m A n1 bs1 b n3 bs3 N H1 H2 H3 ->.
  pose proof (proj2 (rw_cells_app segs m (A + Z.of_nat n1) [C1 b] [CB n3 bs3])) as J1.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in J1. specialize (J1 (conj H2 H3)).
  pose proof (proj2 (rw_cells_app segs m A [CB n1 bs1] ([C1 b] ++ [CB n3 bs3]))) as J2.
  cbn [cells_size csize Nat.add] in J2. rewrite Nat.add_0_r in J2. specialize (J2 (conj H1 J1)).
  pose proof (rw_cells_merge segs m A [] ([CB n1 bs1] ++ [C1 b] ++ [CB n3 bs3]) []) as M.
  rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
  specialize (M J2). rewrite !app_nil_r in M.
  replace (n1 + 1 + n3)%nat with (n1 + (1 + (n3 + 0)))%nat by lia. exact M.
Qed.
