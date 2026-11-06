(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require ExLoad.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxKb AxVal.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

(* [comment removed for export] *)
Definition sext_id_ok (s : store) (x : xv) : bool :=
  match xrange s x with
  | Some (lo, hi) => ((two64 - 2147483648 <=? lo) &&& (hi <? two64)) ||| ((0 <=? lo) &&& (hi <? 2147483648))
  | None => false
  end.

Definition is_zero_lit (y : xv) : bool := match y with XL z => w_eqb z w_zero | _ => false end.

(* [comment removed for export] *)
Definition a_alu32_kb (s : store) (op : aluop) (x y : xv) : xv :=
  match op with
  | ALU_ADD | ALU_SUB =>
      let p := to_kb s x in let q := to_kb s y in
      let k := Z.min 32 (Z.min (lowrun (fst p)) (lowrun (fst q))) in
      if k <=? 0 then XT else
      mk_kb (Z.ones k, Z.land (match op with ALU_SUB => snd p - snd q | _ => snd p + snd q end) (Z.ones k))
  | _ => XT
  end.

Lemma sext32_mod (Z32 : bv 32) : bv_unsigned (sext 64 Z32) mod two32 = bv_unsigned Z32.
Proof.
  rewrite ExLoad.sext64_unsigned by lia. change (Z.of_N 32 - 1) with 31. change (2 ^ Z.of_N 32) with two32.
  pose proof (bv_unsigned_in_range 32 Z32) as Hr. change (bv_modulus 32) with two32 in Hr.
  destruct (bv_unsigned Z32 <? 2 ^ 31).
  - apply Z.mod_small. exact Hr.
  - replace (bv_unsigned Z32 + two64 - two32) with (bv_unsigned Z32 + (two64 / two32 - 1) * two32) by (unfold two64, two32; lia).
    rewrite Z.mod_add by (unfold two32; lia). apply Z.mod_small. exact Hr.
Qed.

Lemma a_alu32_kb_sound (ρ : valuation) (s : store) (op : aluop) (x y : xv) (X Y : bv 32) :
  sat ρ s -> xv_val32 ρ x X -> xv_val32 ρ y Y -> xv_val ρ (a_alu32_kb s op x y) (sext 64 (alu32 op X Y)).
Proof.
  intros Hs [a [Ha HX]] [b [Hb HY]]. unfold a_alu32_kb.
  assert (Hgen : forall sub : bool, bv_unsigned (alu32 op X Y) = (if sub then bv_unsigned a - bv_unsigned b else bv_unsigned a + bv_unsigned b) mod two32 ->
     xv_val ρ (let p := to_kb s x in let q := to_kb s y in
               let k := Z.min 32 (Z.min (lowrun (fst p)) (lowrun (fst q))) in
               if k <=? 0 then XT else
               mk_kb (Z.ones k, Z.land (if sub then snd p - snd q else snd p + snd q) (Z.ones k))) (sext 64 (alu32 op X Y))).
  { intros sub E. cbv zeta.
    pose proof (to_kb_sound ρ s x a Hs Ha) as K1. pose proof (to_kb_sound ρ s y b Hs Hb) as K2.
    set (p := to_kb s x) in *. set (q := to_kb s y) in *.
    destruct (lowrun_spec (fst p)) as [Hr1 Hb1]. destruct (lowrun_spec (fst q)) as [Hr2 Hb2].
    set (k := Z.min 32 (Z.min (lowrun (fst p)) (lowrun (fst q)))).
    destruct (Z.leb_spec k 0) as [|Hk0]; [exact I|].
    assert (Hk32 : k <= 32) by (apply Z.le_min_l).
    assert (Hk1 : k <= lowrun (fst p)) by (unfold k; etransitivity; [apply Z.le_min_r | apply Z.le_min_l]).
    assert (Hk2 : k <= lowrun (fst q)) by (unfold k; etransitivity; [apply Z.le_min_r | apply Z.le_min_r]).
    clearbody k p q. assert (Hk : 0 < k <= 32) by (split; assumption).
    apply mk_kb_sound. cbn [fst snd]. unfold kb_val. rewrite !Z.land_ones by lia.
    assert (Hdiv : (2 ^ k | two32)).
    { exists (2 ^ (32 - k)). change two32 with (2 ^ 32). rewrite <- Z.pow_add_r by (clear - Hk; lia). f_equal. clear - Hk; lia. }
    rewrite <- (Z.mod_mod_divide (bv_unsigned (sext 64 (alu32 op X Y))) two32 (2 ^ k)) by exact Hdiv.
    rewrite sext32_mod, E. rewrite Z.mod_mod_divide by exact Hdiv.
    assert (E1 : bv_unsigned a mod 2 ^ k = snd p mod 2 ^ k) by (apply (kb_mod (fst p)); [clear - Hk; lia | intros i Hi; apply Hb1; clear - Hi Hk1; lia | exact K1]).
    assert (E2 : bv_unsigned b mod 2 ^ k = snd q mod 2 ^ k) by (apply (kb_mod (fst q)); [clear - Hk; lia | intros i Hi; apply Hb2; clear - Hi Hk2; lia | exact K2]).
    destruct sub.
    - rewrite Zminus_mod, E1, E2, <- Zminus_mod. reflexivity.
    - rewrite Zplus_mod, E1, E2, <- Zplus_mod. reflexivity. }
  destruct op; try exact I.
  - apply (Hgen false). cbn [alu32 alu]. rewrite bv_add_unsigned, HX, HY. unfold bv_wrap. change (bv_modulus 32) with two32.
    rewrite <- Zplus_mod. reflexivity.
  - apply (Hgen true). cbn [alu32 alu]. rewrite bv_sub_unsigned, HX, HY. unfold bv_wrap. change (bv_modulus 32) with two32.
    rewrite <- Zminus_mod. reflexivity.
Qed.

(* [comment removed for export] *)
Definition a_alu32_lit (s : store) (op : aluop) (x y : xv) : xv :=
  match op with
  | ALU_ADD => match a_add s x y with XL r => XL (w_sext32 (w_low32 r)) | _ => XT end
  | ALU_SUB => match a_sub s x y with XL r => XL (w_sext32 (w_low32 r)) | _ => XT end
  | _ => XT
  end.

Lemma a_alu32_lit_sound (ρ : valuation) (s : store) (op : aluop) (x y : xv) (X Y : bv 32) :
  sat ρ s -> xv_val32 ρ x X -> xv_val32 ρ y Y -> xv_val ρ (a_alu32_lit s op x y) (sext 64 (alu32 op X Y)).
Proof.
  intros Hs [a [Ha HX]] [b [Hb HY]]. unfold a_alu32_lit.
  assert (Hdiv : (two32 | two64)) by (exists two32; reflexivity).
  destruct op; try exact I.
  - pose proof (a_add_sound ρ s x y a b Hs Ha Hb) as Hr. destruct (a_add s x y) as [r| | | | |]; try exact I.
    cbn [xv_val] in Hr. apply xv_XL. symmetry. apply w_sext32_ok. rewrite phi_low32, <- Hr.
    assert (EX : bv_unsigned (alu32 ALU_ADD X Y) = (bv_unsigned a + bv_unsigned b) mod two32).
    { cbn [alu32 alu]. rewrite bv_add_unsigned, HX, HY. unfold bv_wrap. change (bv_modulus 32) with two32. rewrite <- Zplus_mod. reflexivity. }
    rewrite EX, bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with two64.
    rewrite Z.mod_mod_divide by exact Hdiv. reflexivity.
  - pose proof (a_sub_sound ρ s x y a b Hs Ha Hb) as Hr. destruct (a_sub s x y) as [r| | | | |]; try exact I.
    cbn [xv_val] in Hr. apply xv_XL. symmetry. apply w_sext32_ok. rewrite phi_low32, <- Hr.
    assert (EX : bv_unsigned (alu32 ALU_SUB X Y) = (bv_unsigned a - bv_unsigned b) mod two32).
    { cbn [alu32 alu]. rewrite bv_sub_unsigned, HX, HY. unfold bv_wrap. change (bv_modulus 32) with two32. rewrite <- Zminus_mod. reflexivity. }
    rewrite EX, bv_sub_unsigned. unfold bv_wrap. change (bv_modulus 64) with two64.
    rewrite Z.mod_mod_divide by exact Hdiv. reflexivity.
Qed.

(* [comment removed for export] *)
Definition a_shift32 (s : store) (op : aluop) (x y : xv) : xv :=
  match op with
  | ALU_SLL | ALU_SRL | ALU_SRA =>
      match lit32 s x with
      | Some a => if 5 <=? lowrun (fst (to_kb s y)) then XL (w_sext32 (w_alu32 op (w_low32 a) (of_Z (Z.land (snd (to_kb s y)) 31)))) else XT
      | None => XT
      end
  | _ => XT
  end.

Lemma a_shift32_sound (ρ : valuation) (s : store) (op : aluop) (x y : xv) (X Y : bv 32) :
  sat ρ s -> xv_val32 ρ x X -> xv_val32 ρ y Y -> xv_val ρ (a_shift32 s op x y) (sext 64 (alu32 op X Y)).
Proof.
  intros Hs Hx Hy. unfold a_shift32.
  assert (Hop : forall (Hop : op = ALU_SLL \/ op = ALU_SRL \/ op = ALU_SRA),
    xv_val ρ (match lit32 s x with
              | Some a => if 5 <=? lowrun (fst (to_kb s y)) then XL (w_sext32 (w_alu32 op (w_low32 a) (of_Z (Z.land (snd (to_kb s y)) 31)))) else XT
              | None => XT end) (sext 64 (alu32 op X Y))).
  { intros Hop. destruct (lit32 s x) as [a|] eqn:Ea; [|exact I].
    destruct (5 <=? lowrun (fst (to_kb s y))) eqn:El; [|exact I]. apply Z.leb_le in El.
    pose proof (low32_of_XL ρ a X (lit32_sound ρ s x X a Hs Hx Ea)) as HX.
    destruct Hy as [b [Hb HY]].
    pose proof (to_kb_sound ρ s y b Hs Hb) as Hk. destruct (lowrun_spec (fst (to_kb s y))) as [_ Hbits].
    pose proof (kb_mod _ _ _ 5 ltac:(lia) (fun i Hi => Hbits i ltac:(lia)) Hk) as Hm.
    set (v := snd (to_kb s y)) in *.
    assert (EL : Z.land v 31 = v mod 32) by (change (Z.land v 31) with (Z.land v (Z.ones 5)); rewrite Z.land_ones by lia; reflexivity).
    assert (Hv31 : 0 <= Z.land v 31 < 32) by (rewrite EL; apply Z.mod_pos_bound; lia).
    set (Y' := Z_to_bv 32 (Z.land v 31)).
    assert (HY' : bv_unsigned Y' = Z.land v 31) by (unfold Y'; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 32) with (2 ^ 32); apply Z.mod_small; lia).
    assert (HYm : bv_unsigned Y mod 32 = v mod 32).
    { rewrite HY. change two32 with (2 ^ 27 * 32). rewrite Z.mod_mod_divide by (exists (2 ^ 27); reflexivity).
      change (2 ^ 5) with 32 in Hm. exact Hm. }
    assert (Eand : bv_and Y (Z_to_bv 32 31) = bv_and Y' (Z_to_bv 32 31)).
    { apply bv_eq. rewrite !bv_and_unsigned. change (bv_unsigned (Z_to_bv 32 31)) with (Z.ones 5). rewrite !Z.land_ones by lia.
      change (2 ^ 5) with 32. rewrite HY', HYm, EL. rewrite Z.mod_mod by lia. reflexivity. }
    assert (Ealu : alu32 op X Y = alu32 op X Y') by (destruct Hop as [->|[->| ->]]; unfold alu32, alu; rewrite Eand; reflexivity).
    rewrite Ealu. apply xv_XL. symmetry. apply w_op32_ok; [exact HX|]. rewrite HY', of_Z_spec. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  destruct op; try exact I; apply Hop; tauto.
Qed.

Definition a_alu32x (s : store) (op : aluop) (x y : xv) : xv :=
  match a_alu32 s op x y with
  | XT => match op with
          | ALU_ADD => if is_zero_lit y &&& sext_id_ok s x then x else
                       match a_alu32_lit s op x y with XT => a_alu32_kb s op x y | r => r end
          | ALU_SLL | ALU_SRL | ALU_SRA => a_shift32 s op x y
          | _ => match a_alu32_lit s op x y with XT => a_alu32_kb s op x y | r => r end
          end
  | r => r
  end.

Lemma a_alu32x_sound (ρ : valuation) (s : store) (op : aluop) (x y : xv) (X Y : bv 32) :
  sat ρ s -> xv_val32 ρ x X -> xv_val32 ρ y Y -> xv_val ρ (a_alu32x s op x y) (sext 64 (alu32 op X Y)).
Proof.
  intros Hs Hx Hy. pose proof (a_alu32_sound ρ s op x y X Y Hs Hx Hy) as H0. unfold a_alu32x.
  destruct (a_alu32 s op x y) eqn:E; try exact H0.
  assert (Hkb : xv_val ρ (match a_alu32_lit s op x y with XT => a_alu32_kb s op x y | r => r end) (sext 64 (alu32 op X Y))).
  { pose proof (a_alu32_lit_sound ρ s op x y X Y Hs Hx Hy) as Hl. pose proof (a_alu32_kb_sound ρ s op x y X Y Hs Hx Hy) as Hk.
    destruct (a_alu32_lit s op x y); first [exact Hl | exact Hk]. }
  pose proof (a_shift32_sound ρ s op x y X Y Hs Hx Hy) as Hsh.
  destruct op; try exact Hkb; try exact Hsh.
  destruct (is_zero_lit y &&& sext_id_ok s x) eqn:Hc; [|exact Hkb].
  apply land_true in Hc as [Hz Hr]. destruct Hx as [a [Ha HX]]. destruct Hy as [b [Hb HY]].
  destruct y as [z| | | | |]; cbn [is_zero_lit] in Hz; try discriminate. rewrite w_eqb_spec in Hz. apply Z.eqb_eq in Hz.
  cbn [xv_val] in Hb. rewrite Hb, Hz in HY. change (wZ w_zero) with 0 in HY. rewrite Z.mod_0_l in HY by (unfold two32; lia).
  unfold sext_id_ok in Hr. destruct (xrange s x) as [[lo hi]|] eqn:Er; [|discriminate].
  pose proof (xrange_sound ρ s x a Hs Ha _ Er) as Hra. cbn [fst snd] in Hra.
  replace (sext 64 (alu32 ALU_ADD X Y)) with a; [exact Ha|]. apply bv_eq.
  rewrite ExLoad.sext64_unsigned by lia. change (Z.of_N 32 - 1) with 31. change (2 ^ 31) with 2147483648. change (2 ^ Z.of_N 32) with two32.
  assert (EX : bv_unsigned (alu32 ALU_ADD X Y) = bv_unsigned a mod two32).
  { cbn [alu32 alu]. rewrite bv_add_unsigned, HX, HY, Z.add_0_r. unfold bv_wrap. change (bv_modulus 32) with two32. apply Z.mod_mod. unfold two32; lia. }
  rewrite EX. pose proof (bvu_range a) as Hab.
  apply lor_true in Hr as [Hr|Hr]; apply land_true in Hr as [R1 R2]; apply Z.leb_le in R1; apply Z.ltb_lt in R2.
  - assert (Em : bv_unsigned a mod two32 = bv_unsigned a - (two64 - two32)).
    { rewrite <- (Z_mod_plus_full (bv_unsigned a) (- (two64 / two32 - 1))). unfold two64, two32 in *. rewrite Z.mod_small; lia. }
    rewrite Em. rewrite (proj2 (Z.ltb_ge _ _)) by (unfold two64, two32 in *; lia). lia.
  - rewrite Z.mod_small by (unfold two32; lia). rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.
