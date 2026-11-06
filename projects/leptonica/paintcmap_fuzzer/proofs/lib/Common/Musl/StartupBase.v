(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Export StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Reloc Require Export RelocKit RImg.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Musl Require Export RelocRW RelocStart.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Musl Require MuslTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma rl_add_nat : forall d c (n : nat) c', (c + Z.of_nat n = c')%Z -> (rl d c + nat_to_word n)%bv = rl d c'.
Proof.
  intros d c n c' <-. rewrite word_add_nat. rewrite rl_u_mod. unfold rl. apply Z_to_bv64_mod_eq.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rl_mod_align : forall d c m, (0 < m)%Z -> (2^64 mod m = 0)%Z -> (d mod m = 0)%Z ->
  (bv_unsigned (rl d c) mod m = c mod m)%Z.
Proof.
  intros d c m Hm H64 Hd. rewrite rl_u_mod.
  apply Z.mod_divide in H64; [|lia]. destruct H64 as [q Hq]. rewrite Hq.
  rewrite Z.mul_comm, Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. rewrite Z.mod_mod by lia.
  apply Z.mod_divide in Hd; [|lia]. destruct Hd as [q' ->]. rewrite Z.mod_add by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rl_and7_sub : forall d c k r, (d mod 8 = 0)%Z -> ((k - c) mod 8 = r)%Z ->
  v_and (Z_to_bv 64 7) (v_sub (Z_to_bv 64 k) (rl d c)) = Z_to_bv 64 r.
Proof.
  intros d c k r Hd <-. unfold v_and, v_sub. apply bv_eq. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_comm, Z.land_ones by lia. change (2^3)%Z with 8%Z.
  rewrite rl_u_mod. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
  assert (D8 : (8 | 2^64)%Z) by (exists (2^61)%Z; reflexivity).
  set (x := ((k mod 2^64 - (c + d) mod 2^64) mod 2^64)%Z).
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hb1.
  pose proof (Z.mod_pos_bound (k - c) 8 ltac:(lia)) as Hb.
  rewrite (Z.mod_small (x mod 8)), (Z.mod_small ((k - c) mod 8)) by lia.
  subst x. rewrite Z.mod_mod_divide by exact D8.
  rewrite Zminus_mod. rewrite !Z.mod_mod_divide by exact D8. rewrite <- Zminus_mod.
  apply Z.mod_divide in Hd; [|lia]. destruct Hd as [q ->].
  replace (k - (c + q * 8))%Z with (k - c + (- q) * 8)%Z by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma mod8_mod4 : forall d, (d mod 8 = 0)%Z -> (d mod 4 = 0)%Z.
Proof. intros d H. rewrite <- (Z.mod_mod_divide d 8 4) by (exists 2%Z; reflexivity). rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Ltac rl_andi3 :=
  match goal with
  | |- context [v_andi (rl ?d ?c) 3] =>
      rewrite (v_andi_3_aligned (rl d c)) by
        (rewrite (rl_mod_align d c 4 ltac:(lia) eq_refl
                    ltac:(apply mod8_mod4; rl_dmod8)); reflexivity)
  end.

Ltac rl_and7 :=
  match goal with
  | |- context [v_and (Z_to_bv 64 7) (v_sub (Z_to_bv 64 ?k) (rl ?d ?c))] =>
      let r := eval vm_compute in ((k - c) mod 8)%Z in
      rewrite (rl_and7_sub d c k r ltac:(rl_dmod8) eq_refl)
  end.

Lemma rl_wrap : forall d c c', (c mod 2^64 = c' mod 2^64)%Z -> rl d c = rl d c'.
Proof. intros d c c' H. unfold rl. apply Z_to_bv64_mod_eq. rewrite (Zplus_mod c d), (Zplus_mod c' d), H. reflexivity. Qed.

Ltac rl_wrapfold :=
  repeat match goal with
  | |- context [rl ?d ?c] =>
      let b := eval vm_compute in ((c <? 0) || (2^64 <=? c))%Z in
      lazymatch b with
      | true => let c' := eval vm_compute in (c mod 2^64)%Z in rewrite (rl_wrap d c c' eq_refl)
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rdn_wbytes_out_rl : forall segs bs m (d ca cb : Z) (n : nat),
  (- 2^16 <= d <= 2^32)%Z ->
  ((2^16 <=? cb)%Z && (cb + Z.of_nat (length bs) <=? 2^62)%Z && (2^16 <=? ca)%Z && (ca + Z.of_nat n <=? 2^62)%Z &&
   ((ca + Z.of_nat n <=? cb)%Z || (cb + Z.of_nat (length bs) <=? ca)%Z))%bool = true ->
  rdn segs (wbytes m (rl d cb) bs) (rl d ca) n = rdn segs m (rl d ca) n.
Proof.
  intros segs bs m d ca cb n Hd Hb.
  apply andb_prop in Hb as [Hb Hor]. apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3].
  apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
  assert (E1 : bv_unsigned (rl d ca) = (ca + d)%Z) by (apply rl_u; lia).
  assert (E2 : bv_unsigned (rl d cb) = (cb + d)%Z) by (apply rl_u; lia).
  apply rdn_wbytes_out; rewrite ?E1, ?E2; [| lia | lia].
  apply Bool.orb_prop in Hor as [H|H]; apply Z.leb_le in H; [left | right]; lia.
Qed.

(* [comment removed for export] *)
#[export] Ltac unorm ::=
  rl_unorm;
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with
             | context [Z_to_bv 64 _] => fail
             | _ => rewrite (u_Z2bv z) by lia
             end
         end.

(* [comment removed for export] *)
Ltac start_bounds :=
  rl_dwin_bounds;
  lazymatch goal with
  | _ : (0x10270 <= rl_data_lo)%Z |- _ => idtac
  | _ => let h := fresh "RSTh" in pose proof rl_hdr_below as h
  end.

#[export] Ltac region_side ::=
  unfold win_lo; rewrite ?stack_max_size_val, ?length_N_to_le_bytes, ?length_zeros, ?repeat_length;
  cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; imm_norm; rl_bounds; unorm; lia.

(* [comment removed for export] *)
#[export] Ltac ok_data ::=
  apply rl_store_ok_data; try start_bounds; rl_bounds; unorm; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

(* [comment removed for export] *)
#[export] Ltac peel ::=
  addr_lin;
  lazymatch goal with
  | |- rdn _ _ (rl (@rl_delta ?RL ?b) _) _ = _ =>
      let Hd := fresh "PEEL_d" in
      pose proof (@rl_delta_bd RL b) as Hd;
      try start_bounds;
      repeat (lazymatch goal with
              | |- rdn _ (wbytes _ ?a _) ?x _ = _ =>
                  tryif constr_eq a x then fail else
                  first [ rewrite rdn_wbytes_out_rl by (first [exact Hd | peel_bool])
                        | rewrite rdn_wbytes_out_xblk by peel_bool
                        | rewrite rdn_wbytes_out by region_side ]
              end); clear Hd
  | |- rdn _ _ (Z_to_bv 64 (?s - _)%Z) _ = _ =>
      let L := fresh "PEEL_lo" in let H := fresh "PEEL_hi" in
      tryif (assert (L : (2^33 <= s)%Z) by lia; assert (H : (s <= 2^63)%Z) by lia) then
        (repeat (lazymatch goal with
                 | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
                     tryif constr_eq a b then fail else
                     first [ rewrite rdn_wbytes_out_off by (first [exact L | exact H | peel_bool])
                           | rewrite rdn_wbytes_out_off0 by (first [exact L | exact H | peel_bool])
                           | rewrite rdn_wbytes_out_lit by peel_bool
                           | rewrite rdn_wbytes_out by region_side ]
                 end); clear L H)
      else peel_generic
  | |- _ => try start_bounds; peel_generic
  end.

#[export] Ltac rd_hit8 ::=
  addr_norm; peel;
  lazymatch goal with |- rdn _ (wbytes _ ?a' _) ?a _ = _ =>
    first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ] end;
  apply rdn_wbytes_hit8; rl_bounds; unorm; lia.

(* [comment removed for export] *)
Ltac stepretF F D FK := MuslTac.stepretF F D FK.
Ltac stepretK F D FK tac := MuslTac.stepretK F D FK tac.
Ltac stepjrK F D FK tac := MuslTac.stepjrK F D FK tac.
Ltac rl_ret_ok := MuslTac.rl_ret_ok.
Ltac rl_cond := MuslTac.rl_cond.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Hdr.
  Context {RL : Reloc} {RI : RelocImg RL} {RD : RelocData RL} {RST : RelocStart RL RD}.
  Ltac hdr C := let H := fresh in pose proof C as H; rewrite rl_abs in H; exact H.
  Lemma imgL_10040_4 : rdn rl_segs (fun _ => None) (Z_to_bv 64 0x10040) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
  Proof. hdr img_10040_4. Qed.
  Lemma imgL_10050_8 : rdn rl_segs (fun _ => None) (Z_to_bv 64 0x10050) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
  Proof. hdr img_10050_8. Qed.
  Lemma imgL_10078_4 : rdn rl_segs (fun _ => None) (Z_to_bv 64 0x10078) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
  Proof. hdr img_10078_4. Qed.
  Lemma imgL_100b0_4 : rdn rl_segs (fun _ => None) (Z_to_bv 64 0x100b0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
  Proof. hdr img_100b0_4. Qed.
  Lemma imgL_100e8_4 : rdn rl_segs (fun _ => None) (Z_to_bv 64 0x100e8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
  Proof. hdr img_100e8_4. Qed.
  Lemma imgL_10120_4 : rdn rl_segs (fun _ => None) (Z_to_bv 64 0x10120) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
  Proof. hdr img_10120_4. Qed.
  Lemma imgL_10158_4 : rdn rl_segs (fun _ => None) (Z_to_bv 64 0x10158) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
  Proof. hdr img_10158_4. Qed.
  Lemma imgL_10190_4 : rdn rl_segs (fun _ => None) (Z_to_bv 64 0x10190) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
  Proof. hdr img_10190_4. Qed.
  Lemma imgL_101c8_4 : rdn rl_segs (fun _ => None) (Z_to_bv 64 0x101c8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
  Proof. hdr img_101c8_4. Qed.
  Lemma imgL_101f0_8 : rdn rl_segs (fun _ => None) (Z_to_bv 64 0x101f0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Proof. hdr img_101f0_8. Qed.
  Lemma imgL_10200_4 : rdn rl_segs (fun _ => None) (Z_to_bv 64 0x10200) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
  Proof. hdr img_10200_4. Qed.
  Lemma imgL_10238_4 : rdn rl_segs (fun _ => None) (Z_to_bv 64 0x10238) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
  Proof. hdr img_10238_4. Qed.
End Hdr.
