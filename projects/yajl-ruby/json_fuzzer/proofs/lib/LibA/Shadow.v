(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Export StepA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition blk_shadow (n : Z) : list byte :=
  repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)) ++ (if n mod 8 =? 0 then [] else [Z_to_bv 8 (n mod 8)]).

Lemma blk_shadow_length : forall n, 0 <= n -> Z.of_nat (length (blk_shadow n)) = (n + 7) / 8.
Proof.
  intros n Hn. unfold blk_shadow. rewrite length_app, repeat_length.
  destruct (Z.eqb_spec (n mod 8) 0) as [E|E]; cbn [length]; Z.div_mod_to_equations; lia.
Qed.

Lemma blk_shadow_full : forall n g, 0 <= g < n / 8 -> nth_error (blk_shadow n) (Z.to_nat g) = Some (Z_to_bv 8 0).
Proof.
  intros n g Hg. unfold blk_shadow. rewrite nth_error_app1 by (rewrite repeat_length; lia).
  apply nth_error_repeat. lia.
Qed.

Lemma blk_shadow_partial : forall n, 0 <= n -> n mod 8 <> 0 -> nth_error (blk_shadow n) (Z.to_nat (n / 8)) = Some (Z_to_bv 8 (n mod 8)).
Proof.
  intros n Hn Hm. unfold blk_shadow. rewrite nth_error_app2 by (rewrite repeat_length; lia).
  rewrite repeat_length, Nat.sub_diag. destruct (Z.eqb_spec (n mod 8) 0); [lia| reflexivity].
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition block_shadow (m : mem) (SB A n : Z) : Prop :=
  A mod 8 = 0 /\ 0 < n /\ u8arr segs m (SB + A / 8) (blk_shadow n).

Lemma block_shadow_u8arr : forall m SB A n, block_shadow m SB A n -> u8arr segs m (SB + A / 8) (blk_shadow n).
Proof. intros m SB A n (_ & _ & H); exact H. Qed.

(* [comment removed for export] *)
Lemma block_shadow_read_u : forall m SB A n (a w : Z),
  A mod 8 = 0 -> 0 < n -> u8arr segs m (SB + A / 8) (blk_shadow n) ->
  A <= a -> 1 <= w -> a + w <= A + n -> a mod 8 + w <= 8 ->
  exists k, ov_read_bytes segs m (Z_to_bv 64 (SB + a / 8)) 1 = Some [Z_to_bv 8 k]
            /\ (k = 0 \/ (a mod 8 + w <= k /\ 1 <= k <= 7)).
Proof.
  intros m SB A n a w HA8 Hn HU HAa Hw Haw Hg.
  set (g := a / 8 - A / 8).
  assert (Hg0 : 0 <= g) by (unfold g; Z.div_mod_to_equations; nia).
  destruct (Z.lt_ge_cases g (n / 8)) as [Hfull | Hlast].
  - exists 0. split; [|left; reflexivity].
    eapply (u8arr_read segs m (SB + A / 8) (blk_shadow n) g); [exact HU| apply blk_shadow_full; lia| lia|].
    unfold wa. f_equal. lia.
  - assert (Hgeq : g = n / 8) by (unfold g in *; Z.div_mod_to_equations; nia).
    assert (Hm : n mod 8 <> 0) by (unfold g in *; Z.div_mod_to_equations; nia).
    exists (n mod 8). split.
    + eapply (u8arr_read segs m (SB + A / 8) (blk_shadow n) g); [exact HU| rewrite Hgeq; apply blk_shadow_partial; lia| lia|].
      unfold wa. f_equal. lia.
    + right. unfold g in *. Z.div_mod_to_equations. nia.
Qed.

Lemma block_shadow_read0_u : forall m SB A n (a w : Z),
  A mod 8 = 0 -> 0 < n -> u8arr segs m (SB + A / 8) (blk_shadow n) ->
  A <= a -> 1 <= w -> a + w <= A + 8 * (n / 8) -> a mod 8 + w <= 8 ->
  ov_read_bytes segs m (Z_to_bv 64 (SB + a / 8)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m SB A n a w HA8 Hn HU HAa Hw Haw Hg.
  eapply (u8arr_read segs m (SB + A / 8) (blk_shadow n) (a / 8 - A / 8)); [exact HU| | Z.div_mod_to_equations; nia|].
  - apply blk_shadow_full. Z.div_mod_to_equations. nia.
  - unfold wa. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma block_shadow_read : forall m SB A n (a w : Z),
  block_shadow m SB A n ->
  A <= a -> 1 <= w -> a + w <= A + n -> a mod 8 + w <= 8 ->
  exists k, ov_read_bytes segs m (Z_to_bv 64 (SB + a / 8)) 1 = Some [Z_to_bv 8 k]
            /\ (k = 0 \/ (a mod 8 + w <= k /\ 1 <= k <= 7)).
Proof.
  intros m SB A n a w (HA8 & Hn & HU). apply block_shadow_read_u; assumption.
Qed.

(* [comment removed for export] *)
Lemma block_shadow_read0 : forall m SB A n (a w : Z),
  block_shadow m SB A n ->
  A <= a -> 1 <= w -> a + w <= A + 8 * (n / 8) -> a mod 8 + w <= 8 ->
  ov_read_bytes segs m (Z_to_bv 64 (SB + a / 8)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m SB A n a w BS. apply block_shadow_read0_u; destruct BS as (HA8 & Hn & HU); assumption.
Qed.

(* [comment removed for export] *)
Lemma block_shadow_bound : forall m SB A n, block_shadow m SB A n ->
  0 <= SB + A / 8 /\ SB + A / 8 + (n + 7) / 8 <= 2^64.
Proof.
  intros m SB A n (HA8 & Hn & HU). pose proof (u8arr_bound segs m _ _ HU) as [H1 H2].
  rewrite blk_shadow_length in H2 by lia. lia.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zxb_small : forall k, 0 <= k < 256 -> zxb (Z_to_bv 8 k) = Z_to_bv 64 k.
Proof. intros k Hk. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma sxb_small : forall k, 0 <= k < 128 -> sxb (Z_to_bv 8 k) = Z_to_bv 64 k.
Proof.
  intros k Hk. unfold sxb. f_equal. rewrite Z_to_bv_signed. apply bv_swrap_small.
  change (bv_half_modulus 8) with 128. lia.
Qed.

Lemma signed_lit_small : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. change (bv_half_modulus 64) with (2^63)%Z. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac shadow_addr :=
  repeat match goal with
  | |- context [Z.shiftr ?E 3] => rewrite (Z.shiftr_div_pow2 E 3) by lia; change (2 ^ 3)%Z with 8%Z
  end.

(* [comment removed for export] *)
Ltac open_shadow BS :=
  let Ha := fresh BS "a" in let Hn := fresh BS "n" in let HU := fresh "U" in
  let shb := fresh "shb" in let E := fresh BS "eq" in let L := fresh BS "len" in
  destruct BS as (Ha & Hn & HU);
  lazymatch type of HU with
  | u8arr _ _ _ (blk_shadow ?n) =>
      pose proof (blk_shadow_length n ltac:(lia)) as L;
      remember (blk_shadow n) as shb eqn:E in HU, L
  end;
  rename HU into BS.

(* [comment removed for export] *)
Ltac shadow_fast BS E w :=
  let HR := fresh "SHR" in
  lazymatch goal with
  | |- evtA ?segs _ _ (MS _ _ _ _ _ ?m _) =>
      lazymatch type of BS with
      | u8arr _ _ (?SB + ?A / 8) ?shb =>
          lazymatch goal with
          | Eshb : shb = blk_shadow ?n |- _ =>
              assert (HR : ov_read_bytes segs m (Z_to_bv 64 (SB + E / 8)) 1 = Some [Z_to_bv 8 0])
                by (apply (block_shadow_read0_u segs m SB A n E w); [lia| lia| rewrite <- Eshb; exact BS| lia| lia| lia| lia])
          end
      end
  end;
  zstepA; shadow_addr;        (* [comment removed for export] *)
  zstepA;                     (* [comment removed for export] *)
  zstepA; clear HR;           (* [comment removed for export] *)
  rewrite ?zxb_small, ?sxb_small by lia;
  zstepA; if_false.           (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac shadow_cases BS E w :=
  let HR := fresh "SHR" in let k := fresh "k" in let HK := fresh "HK" in
  lazymatch goal with
  | |- evtA ?segs _ _ (MS _ _ _ _ _ ?m _) =>
      lazymatch type of BS with
      | u8arr _ _ (?SB + ?A / 8) ?shb =>
          lazymatch goal with
          | Eshb : shb = blk_shadow ?n |- _ =>
              destruct (block_shadow_read_u segs m SB A n E w) as (k & HR & HK); [lia|lia|rewrite <- Eshb; exact BS|lia|lia|lia|lia|]
          end
      end
  end;
  zstepA; shadow_addr; zstepA; zstepA; clear HR;
  (destruct HK as [-> | HK];
   [ rewrite ?zxb_small, ?sxb_small by lia; zstepA; if_false
   | rewrite ?zxb_small, ?sxb_small by lia; zstepA;
     let Kc := fresh "Kc" in if_cases Kc; zify_cond Kc; [ clear Kc | exfalso; lia ] ]).

(* [comment removed for export] *)
Ltac shadow_slow :=
  zstepA;                                                     (* [comment removed for export] *)
  change 7 with (Z.ones 3); rewrite ?Z.land_ones by lia; change (2^3) with 8;
  zstepA;                                                     (* [comment removed for export] *)
  (lazymatch goal with
   | |- evtA _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstepA   (* [comment removed for export] *)
   | _ => idtac end);
  let Kc := fresh "Kc" in if_cases Kc; zify_cond Kc;
  [ clear Kc | exfalso; revert Kc; rewrite ?sxb_small, ?zxb_small, ?signed_lit_small by lia; intro Kc; lia ].
