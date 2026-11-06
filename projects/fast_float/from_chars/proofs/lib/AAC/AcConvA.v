(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt FxDrv FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChAllow.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMALp AcSteps AcMALlib AcTbl AcConv AcConvG.

Module AcRdw.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxSubst FxEnt FxCall FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put AXG_put3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConvInvLib AcConvInvG AcUch.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvInvLib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvInvG OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition rom_byte (img : tree Z) (x : Z) : option Z :=
  match tget (okey (Z.shiftr x 3)) img with Some w => Some (Z.land (Z.shiftr w (8 * Z.land x 7)) 255) | None => None end.
(* [comment removed for export] *)
Definition rcbyte (img : tree Z) (R : region) (o : Z) : option Z :=
  match tget (okey o) (rg_cont R) with
  | Some (BK b) => if (Z.leb 0 b && Z.ltb b 256)%bool then Some b else None
  | Some (BV l j) => match is_const l with Some c => if Z.leb 0 j then Some (Z.land (Z.shiftr c (8 * j)) 255) else None | None => None end
  | None => match rg_kind R with
            | RZ => Some 0
            | RO | RI => match is_const (rg_base R) with Some b => if Z.leb 0 (b + o) then rom_byte img (b + o) else None | None => None end
            | _ => None
            end
  end.
Fixpoint rcword (img : tree Z) (R : region) (o : Z) (w : nat) : option Z :=
  match w with
  | O => Some 0
  | Datatypes.S w' => match rcbyte img R o, rcword img R (o + 1) w' with Some b, Some r => Some (b + 256 * r) | _, _ => None end
  end.
Definition rword (img : tree Z) (R : region) (o : Z) (w : nat) : option lin :=
  match (if Nat.eqb w 8 then lword (rg_cont R) o else None) with
  | Some l => Some l
  | None => option_map lconst (rcword img R o w)
  end.
Fixpoint rdw (img : tree Z) (G : list region) (a : lin) (w : nat) : option lin :=
  match G with
  | [] => None
  | R :: G' => match lin_off a (rg_base R), is_const (rg_size R) with
               | Some o, Some z => if (Z.leb 0 o && Z.leb (o + Z.of_nat w) z)%bool then rword img R o w else rdw img G' a w
               | _, _ => rdw img G' a w
               end
  end.
(* [comment removed for export] *)
Definition rdc (img : tree Z) (G : list region) (a : Z) (w : nat) (v : Z) : bool :=
  match rdw img G (lconst a) w with Some l => lin_eqb l (lconst v) | None => false end.

Lemma terms_eqb_refl' : forall t, terms_eqb t t = true.
Proof. induction t as [|[x k] t IH]; cbn; [reflexivity|]. rewrite Pos.eqb_refl, Z.eqb_refl, IH. reflexivity. Qed.
Lemma lin_eqb_refl' : forall l, lin_eqb l l = true.
Proof. intros [c t]. unfold lin_eqb. cbn. rewrite Z.eqb_refl, terms_eqb_refl'. reflexivity. Qed.

Section Rdw.
Variable img : tree Z.
Hypothesis Himg : img_ok SEGS img.
Variable E : valu.
Variable m : word -> option byte.

#[using="Type"] Lemma land7_split : forall x, 0 <= x -> 8 * Z.shiftr x 3 + Z.land x 7 = x /\ 0 <= Z.land x 7 < 8.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change (Z.land x 7) with (Z.land x (Z.ones 3)). rewrite Z.land_ones by lia.
  change (2 ^ 3) with 8. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
Qed.
#[using="Himg"] Lemma rom_byte_sound : forall x b, 0 <= x -> rom_byte img x = Some b -> seg_rom SEGS (Z_to_bv 64 x) = Some (Z_to_bv 8 b) /\ 0 <= b < 256.
Proof. LiaFast.lf_pins (fun (Himg : LiaFast.U) => LiaFast.u0).
  intros x b Hx H. unfold rom_byte in H. destruct (tget (okey (Z.shiftr x 3)) img) as [w|] eqn:Ht; [|discriminate]. injection H as <-.
  destruct (land7_split x Hx) as [Ex Rj]. pose proof (Himg _ _ Ht (Z.land x 7) Rj) as X.
  assert (Hs : 0 <= Z.shiftr x 3) by (apply Z.shiftr_nonneg; exact Hx).
  rewrite okey_pos in X by exact Hs. rewrite Ex in X. split; [exact X|].
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

#[using="Himg"] Lemma rcbyte_sound : forall R o b, rg_ok SEGS E m R -> 0 <= o < rsz E R -> rcbyte img R o = Some b ->
  rd1 SEGS m (Z_to_bv 64 (uE E (rg_base R) + o)) = Some (Z_to_bv 8 b) /\ 0 <= b < 256.
Proof. LiaFast.lf_pins (fun (Himg : LiaFast.U) => LiaFast.u0).
  intros [bl zl k c] o b HR Ho H. unfold rcbyte in H. cbn [rg_cont rg_kind rg_base] in *.
  destruct (tget (okey o) c) as [[bb|l j]|] eqn:Ht.
  - destruct (Z.leb 0 bb && Z.ltb bb 256)%bool eqn:Hb; [|discriminate]. injection H as <-.
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    rewrite (byte_tracked E m bl zl k c o _ HR ltac:(lia) Ht). cbn [bden]. split; [reflexivity | lia].
  - destruct (is_const l) as [cc|] eqn:Hc; [|discriminate]. destruct (Z.leb 0 j) eqn:Hj; [|discriminate]. injection H as <-. apply Z.leb_le in Hj.
    rewrite (byte_tracked E m bl zl k c o _ HR ltac:(lia) Ht). cbn [bden]. destruct (is_const_sound E l cc Hc) as [El Rc].
    rewrite El, u_small64 by exact Rc. split; [rewrite byte_land255; reflexivity|].
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
  - destruct k; try discriminate.
    + (* [comment removed for export] *) destruct (is_const bl) as [b0|] eqn:Hb0; [|discriminate]. destruct (Z.leb 0 (b0 + o)) eqn:Hp; [|discriminate]. apply Z.leb_le in Hp.
      destruct (rom_byte_sound _ _ Hp H) as [X Rb]. destruct (is_const_sound E bl b0 Hb0) as [Eb Rb0].
      assert (Eu : uE E bl = b0) by (unfold uE; rewrite Eb; apply u_small64; exact Rb0). rewrite Eu.
      destruct HR as (_ & _ & HB & _). specialize (HB o Ho). cbn [rg_kind rg_base] in HB. fold (uE E bl) in HB. rewrite Eu in HB.
      destruct HB as [Hm _]. unfold rd1. rewrite Hm. split; [exact X | exact Rb].
    + (* [comment removed for export] *) injection H as <-. split; [exact (byte_rz E m bl zl c o HR Ho Ht) | lia].
    + (* [comment removed for export] *) destruct (is_const bl) as [b0|] eqn:Hb0; [|discriminate]. destruct (Z.leb 0 (b0 + o)) eqn:Hp; [|discriminate]. apply Z.leb_le in Hp.
      destruct (rom_byte_sound _ _ Hp H) as [X Rb]. destruct (is_const_sound E bl b0 Hb0) as [Eb Rb0].
      assert (Eu : uE E bl = b0) by (unfold uE; rewrite Eb; apply u_small64; exact Rb0). rewrite Eu.
      destruct HR as (_ & _ & HB & _). specialize (HB o Ho). cbn [rg_kind rg_base rg_cont] in HB. fold (uE E bl) in HB. rewrite Eu in HB.
      destruct HB as [_ Hu]. rewrite (Hu Ht). split; [exact X | exact Rb].
Qed.

#[using="Himg"] Lemma rcword_sound : forall R w o v, rg_ok SEGS E m R -> 0 <= o -> o + Z.of_nat w <= rsz E R -> rcword img R o w = Some v ->
  0 <= v < 2 ^ (8 * Z.of_nat w) /\
  forall j, (j < w)%nat -> rd1 SEGS m (Z_to_bv 64 (uE E (rg_base R) + (o + Z.of_nat j))) = nth_error (Z_to_le_bytes w v) j.
Proof. LiaFast.lf_pins (fun (Himg : LiaFast.U) => LiaFast.u0).
  intros R w. induction w as [|w IH]; intros o v HR Ho Hz H; cbn [rcword] in H.
  - injection H as <-. split; [cbn; lia | intros j Hj; lia].
  - destruct (rcbyte img R o) as [b|] eqn:Hb; [|discriminate]. destruct (rcword img R (o + 1) w) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
    destruct (rcbyte_sound R o b HR ltac:(lia) Hb) as [Xb Rb]. destruct (IH (o + 1) r HR ltac:(lia) ltac:(lia) Hr) as [Rr Xr].
    split.
    + replace (8 * Z.of_nat (Datatypes.S w)) with (8 + 8 * Z.of_nat w) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. lia.
    + intros j Hj. rewrite le_bytes_cons by lia. destruct j as [|j]; cbn [nth_error].
      * rewrite Z.add_0_r. exact Xb.
      * replace (o + Z.of_nat (Datatypes.S j)) with (o + 1 + Z.of_nat j) by lia. apply Xr. lia.
Qed.

#[using="Type"] Lemma lin_off_u : forall a R o w, rg_ok SEGS E m R -> lin_off a (rg_base R) = Some o -> 0 <= o -> o + w <= rsz E R -> 0 < w ->
  uE E a = uE E (rg_base R) + o.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a R o w HR Hl Ho Hz Hw. destruct HR as (R0 & Rb & _). fold (uE E (rg_base R)) in Rb.
  destruct (lin_off_sound E _ _ _ Hl) as [Hs Hr]. rewrite lden_lsub in Hs.
  pose proof (uE_range E a) as Ra. pose proof (uE_range E (rg_base R)) as Rbb. unfold uE in *.
  assert (X : bv_unsigned (lden E a - lden E (rg_base R))%bv = o) by (rewrite Hs; apply u_small64; exact Hr).
  rewrite bv_sub_unsigned in X. unfold bv_wrap, bv_modulus in X. change (2 ^ Z.of_N 64) with two64 in X. unfold two64 in *.
  destruct (Z_le_gt_dec (bv_unsigned (lden E (rg_base R))) (bv_unsigned (lden E a))) as [Q|Q].
  - rewrite Z.mod_small in X by lia. lia.
  - exfalso. assert (Y : (bv_unsigned (lden E a) - bv_unsigned (lden E (rg_base R))) mod 18446744073709551616 =
                           bv_unsigned (lden E a) - bv_unsigned (lden E (rg_base R)) + 18446744073709551616) by (symmetry; apply Z.mod_unique with (-1); lia).
    rewrite Y in X. lia.
Qed.

#[using="Type"] Lemma lword_fb : forall c o l, lword c o = Some l -> forallb (fun e => tget_is (fst e) c (snd e)) (bv_list o l 8) = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros c o l H. unfold lword in H. destruct (tget (okey o) c) as [[b|l0 j0]|] eqn:H0; try discriminate.
  destruct (Z.eqb j0 0) eqn:Hj0; [|discriminate]. cbn [andb] in H.
  destruct (forallb _ (seq 1 7)) eqn:Hf; [|discriminate]. injection H as <-. apply Z.eqb_eq in Hj0. subst j0.
  unfold bv_list. apply forallb_forall. intros e He. apply in_map_iff in He as (j & <- & Hj). cbn [fst snd]. apply in_seq in Hj.
  unfold tget_is. destruct j as [|j].
  - rewrite Z.add_0_r, H0. cbn [bval_eqb]. rewrite lin_eqb_refl', Z.eqb_refl. reflexivity.
  - rewrite forallb_forall in Hf. specialize (Hf (Datatypes.S j) ltac:(apply in_seq; lia)).
    destruct (tget (okey (o + Z.of_nat (Datatypes.S j))) c) as [[b|l' j']|]; try discriminate.
    apply andb_prop in Hf as [F1 F2]. apply lin_eqb_eq in F1. apply Z.eqb_eq in F2. subst. cbn [bval_eqb]. rewrite lin_eqb_refl', Z.eqb_refl. reflexivity.
Qed.

#[using="Himg"] Theorem rdw_sound : forall G a w l, Forall (rg_ok SEGS E m) G -> (1 <= w <= 8)%nat -> rdw img G a w = Some l -> rd m (uE E a) w (uE E l).
Proof. LiaFast.lf_pins (fun (Himg : LiaFast.U) => LiaFast.u0).
  induction G as [|R G IH]; intros a w l HG Hw H; cbn [rdw] in H; [discriminate|].
  inversion HG as [|? ? HR HG']; subst.
  destruct (lin_off a (rg_base R)) as [o|] eqn:Hl; [|exact (IH a w l HG' Hw H)].
  destruct (is_const (rg_size R)) as [z|] eqn:Hz; [|exact (IH a w l HG' Hw H)].
  destruct (Z.leb 0 o && Z.leb (o + Z.of_nat w) z)%bool eqn:Hb; [|exact (IH a w l HG' Hw H)].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
  assert (Ez : rsz E R = z) by (unfold rsz; destruct (is_const_sound E _ z Hz) as [X1 X2]; rewrite X1; apply u_small64; exact X2).
  pose proof (lin_off_u a R o (Z.of_nat w) HR Hl H1 ltac:(lia) ltac:(lia)) as Ea.
  pose proof HR as HR0. destruct HR0 as (_ & Rb & _). fold (uE E (rg_base R)) in Rb. pose proof (uE_range E (rg_base R)) as Rbb.
  unfold rword in H. destruct (if Nat.eqb w 8 then lword (rg_cont R) o else None) as [l0|] eqn:Hlw.
  - injection H as <-. destruct (Nat.eqb w 8) eqn:Hw8; [|discriminate]. apply Nat.eqb_eq in Hw8. subst w.
    rewrite Ea. destruct R as [bl zl k c]. cbn [rg_base rg_cont] in *.
    apply (rd_bv E m bl zl k c o l0 HR H1); [unfold two64 in *; lia | exact (lword_fb _ _ _ Hlw)].
  - destruct (rcword img R o w) as [v|] eqn:Hc; [|discriminate]. injection H as <-.
    destruct (rcword_sound R w o v HR H1 ltac:(lia) Hc) as [Rv Xv].
    assert (Rv64 : 0 <= v < two64).
    { split; [lia|]. apply Z.lt_le_trans with (2 ^ (8 * Z.of_nat w)); [lia|]. unfold two64. change 18446744073709551616 with (2 ^ 64). apply Z.pow_le_mono_r; lia. }
    rewrite uE_lconst' by exact Rv64. rewrite Ea. apply rd_of_rd1; [lia | unfold two64 in *; lia |].
    intros j Hj. rewrite <- Z.add_assoc. rewrite (Xv j Hj). unfold word_to_le_bytes, wa. rewrite u_small64 by exact Rv64. reflexivity.
Qed.

#[using="Himg"] Corollary rdc_sound : forall G a w v, Forall (rg_ok SEGS E m) G -> (1 <= w <= 8)%nat -> 0 <= a < two64 -> 0 <= v < two64 ->
  rdc img G a w v = true -> rd m a w v.
Proof. LiaFast.lf_pins (fun (Himg : LiaFast.U) => LiaFast.u0).
  intros G a w v HG Hw Ha Hv H. unfold rdc in H. destruct (rdw img G (lconst a) w) as [l|] eqn:Hr; [|discriminate].
  apply lin_eqb_eq in H. subst l. pose proof (rdw_sound G (lconst a) w (lconst v) HG Hw Hr) as X.
  rewrite !uE_lconst' in X by assumption. exact X.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma rdw_in : forall G a w l, Forall (rg_ok SEGS E m) G -> (1 <= w)%nat -> rdw img G a w = Some l ->
  exists R, In R G /\ uE E (rg_base R) <= uE E a /\ uE E a + Z.of_nat w <= uE E (rg_base R) + rsz E R.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction G as [|R G IH]; intros a w l HG Hw H; cbn [rdw] in H; [discriminate|].
  inversion HG as [|? ? HR HG']; subst.
  assert (Hrec : rdw img G a w = Some l -> exists R0, In R0 (R :: G) /\ uE E (rg_base R0) <= uE E a /\ uE E a + Z.of_nat w <= uE E (rg_base R0) + rsz E R0).
  { intros H0. destruct (IH a w l HG' Hw H0) as (R0 & HR0 & X). exists R0. split; [right; exact HR0 | exact X]. }
  destruct (lin_off a (rg_base R)) as [o|] eqn:Hl; [|exact (Hrec H)].
  destruct (is_const (rg_size R)) as [z|] eqn:Hz; [|exact (Hrec H)].
  destruct (Z.leb 0 o && Z.leb (o + Z.of_nat w) z)%bool eqn:Hb; [|exact (Hrec H)].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
  assert (Ez : rsz E R = z) by (unfold rsz; destruct (is_const_sound E _ z Hz) as [X1 X2]; rewrite X1; apply u_small64; exact X2).
  pose proof (lin_off_u a R o (Z.of_nat w) HR Hl H1 ltac:(lia) ltac:(lia)) as Ea.
  exists R. split; [left; reflexivity|]. rewrite Ea, Ez. lia.
Qed.
End Rdw.
End AcRdw.

From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvG OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA.AcRdw OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChAdd.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd.AcAddOwn.

Module AcPriDen.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec AsanAcct FxLin FxCore FxSound FxMem FxFacts FxStep FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst AcDenW AcPri AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMALlib AcDepDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section PriDen.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Lemma rgs_sz_ok : forall E S M ms model, DEN ASEGS LIMIT model0 mem0 E S M ms model ->
  Forall (fun R => 0 <= rsz E R /\ uE E (rg_base R) + rsz E R <= two64) (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model Hd. pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HR & _).
  apply (Forall_impl _ (P := rg_ok ASEGS E (ms_mem (restrict (Hof E M model) ms)))); [|exact HR].
  intros R (H1 & H2 & _). split; [exact H1 | exact H2].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tg_pg_disj : forall E S M ms model a m0, DEN ASEGS LIMIT model0 mem0 E S M ms model -> PRI_on E M a m0 ->
  z_tg (pden E a) + 4096 <= z_pg (pden E a) \/ z_pg (pden E a) + PG_SIZE <= z_tg (pden E a).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 Hd [Hi _ (kp & Hp) (kt & Ht) _ _].
  pose proof (dn_maps _ _ _ _ _ _ _ _ _ Hd) as Hmaps. pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd) as Hgsh. pose proof (dn_pd _ _ _ _ _ _ _ _ _ Hd) as Hpd.
  destruct (In_nth_error _ _ Hp) as (j & Hj). destruct (In_nth_error _ _ Ht) as (j' & Hj').
  assert (Hne : j <> j').
  { intros ->. rewrite Hj in Hj'. injection Hj' as E1 E2 _. unfold PG_SIZE, TG_SIZE in E2. discriminate. }
  assert (Hd' : iv_disj (gden E (p_pg a, lconst PG_SIZE, kp)) (gden E (p_tg a, lconst TG_SIZE, kt))).
  { rewrite Hmaps in Hpd. exact (pdisj_lden_nth E _ _ j j' _ _ Hpd Hj Hj' Hne (is_mark_csize _ _ _) (is_mark_csize _ _ _)). }
  rewrite Forall_forall in Hgsh. destruct (Hgsh _ Hp) as (G1 & _ & _ & G4 & _). destruct (Hgsh _ Ht) as (G1' & _ & _ & G4' & _).
  unfold iv_disj, FxBacking.B, FxBacking.S, gden in Hd'. cbn [fst snd] in Hd'.
  assert (Zpg : uE E (p_pg a) = z_pg (pden E a)) by (symmetry; apply zn_pden).
  assert (Ztg : uE E (p_tg a) = z_tg (pden E a)) by (symmetry; apply zn_pden).
  assert (GP : uE E (lconst PG_SIZE) = PG_SIZE) by (apply uE_lc; unfold PG_SIZE; lia).
  assert (GT : uE E (lconst TG_SIZE) = 4096) by (apply uE_lc; unfold TG_SIZE; lia).
  unfold gsz, uE in *. cbn [fst snd] in *. lia.
Qed.

#[using="Type"] Lemma pri_outside_den : forall E S M ms model a m0 jP jT, DEN ASEGS LIMIT model0 mem0 E S M ms model -> PRI_on E M a m0 ->
  find_grant (sm_maps M) (p_pg a) PG_SIZE = Some jP -> find_grant (sm_maps M) (p_tg a) TG_SIZE = Some jT ->
  forallb_l (pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a) (s_rgs S) = true ->
  forall x, 0 <= x < two64 -> FPmax (pden E a) x -> ~ alloc_part (pden E a) x -> outside E (s_rgs S) (Z_to_bv 64 x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 jP jT Hd [Hi _ _ _ _ Hsep Hxt _] HjP HjT Hck x Hx HF Hna.
  destruct (find_grant_sound _ _ _ _ HjP) as (kp & Hp). destruct (find_grant_sound _ _ _ _ HjT) as (kt & Ht).
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  rewrite forallb_l_eq in Hck.
  exact (pri_outside E (s_facts S) (sm_maps M) model (sm_sp M) _ HF0 (dn_maps _ _ _ _ _ _ _ _ _ Hd) (dn_pd _ _ _ _ _ _ _ _ _ Hd)
           (dn_gsh _ _ _ _ _ _ _ _ _ Hd) (dn_gtop _ _ _ _ _ _ _ _ _ Hd) (dn_sp _ _ _ _ _ _ _ _ _ Hd) (proj2 (dn_spok _ _ _ _ _ _ _ _ _ Hd))
           (proj1 (dn_spok _ _ _ _ _ _ _ _ _ Hd)) (dn_mres _ _ _ _ _ _ _ _ _ Hd) ASEGSR (dn_res _ _ _ _ _ _ _ _ _ Hd) gq_res a m0 Hi jP jT _ _ Hp eq_refl eq_refl Ht eq_refl eq_refl Hsep Hxt
           (s_rgs S) (rgs_sz_ok E S M ms model Hd) Hck x Hx HF Hna).
Qed.
End PriDen.
End AcPriDen.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition PRI_WR : list (Z * nat) := [(904176, 10%nat); (912208, 1%nat)].
Definition IMGP : tree Z := mk_img_runs PRI_WR TEmpty.

(* [comment removed for export] *)
Fixpoint cut_steps_k (k : rkind) (i : nat) (b : lin) (c : tree bval) (z off : Z) (cuts : list Z) : list rstep :=
  match cuts with
  | [] => []
  | o :: cuts' => let d := o - off in
                  let c2 := sub_cont c d (z - d) in      (* [comment removed for export] *)
                  RSplit i (RG b (lconst d) k (sub_cont c 0 d)) (RG (laddc b d) (lconst (z - d)) k c2) d ::
                  cut_steps_k k (Datatypes.S i) (laddc b d) c2 (z - d) o cuts'
  end.
Definition rg_is (b : lin) (z : Z) (k : rkind) (R : region) : bool :=
  (lin_eqb (rg_base R) b && lin_eqb (rg_size R) (lconst z) && AcSteps.rkind_eqb (rg_kind R) k)%bool.
Fixpoint find_gsz_acc (gs : list (lin * lin * gkind)) (z : Z) (i : nat) : option (nat * lin) :=
  match gs with
  | [] => None
  | g :: r => if lin_eqb (snd (fst g)) (lconst z) then Some (i, fst (fst g)) else find_gsz_acc r z (Datatypes.S i)
  end.
Definition weaken_rw (R : region) : region := RG (rg_base R) (rg_size R) RW (rg_cont R).

(* [comment removed for export] *)
Definition pri_lins0 (SBl SHl CAl PGl TGl : lin) : list lin :=
  SBl :: SHl :: CAl :: PGl :: TGl :: List.flat_map (fun _ : Z => [lc0; lc0]) CLS ++ [lc0; lc0; lc0] ++ [lc0; lc0; lc0].
Definition with_pri (a : ast) (own : list (lin * lin)) (pri : list lin) : ast :=
  AST (a_on a) (a_rgs a) (a_fcts a) own (a_dep a) (a_nl a) (a_live a) pri.
Definition with_own_allow (M : smodel) (own : list (lin * lin)) (al : list (lin * Z)) : smodel :=
  SM (sm_maps M) al (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) own.

(* [comment removed for export] *)
Fixpoint find_const_rg (G : list region) (lo hi : Z) (i : nat) : option (nat * Z * Z) :=
  match G with
  | [] => None
  | R :: r => match is_const (rg_base R), is_const (rg_size R) with
              | Some b, Some z => if Z.leb b lo &&& Z.leb hi (b + z) then Some (i, b, z) else find_const_rg r lo hi (Datatypes.S i)
              | _, _ => find_const_rg r lo hi (Datatypes.S i)
              end
  end.

(* [comment removed for export] *)
Definition tzero_b (t : tree bval) : bool := tforall (fun _ v => match v with BK 0 => true | _ => false end) t.

(* [comment removed for export] *)
Definition zr_cover (zr : list (Z * Z)) (sblo sbhi : Z) : bool :=
  existsb (fun p => Z.leb (fst p) (sblo / 8 + 2147450880) && Z.leb (sbhi / 8 + 2147450880 + 17179869184) (snd p))%bool zr.
Definition conva_extra (S : sst) (M : smodel) (a a' : ast) (RT RP0 RCA RST RGQ : region) (SBl SB8 PGl Tl : lin) (G6 : list region) : bool :=
  let fs := s_facts S in
  (match a_rgs a, a_fcts a with [], [] => true | _, _ => false end &&     (* [comment removed for export] *)
   rg_is (laddc Tl 80) 2720 RZ RCA && AcSteps.rkind_eqb (rg_kind RP0) RZ && AcSteps.rkind_eqb (rg_kind RST) RZ &&
   rg_is (lconst GQ_LO) (GQ_HI - GQ_LO) RZ RGQ &&
   zr_cover (sm_zr M) (fst (irange fs SBl)) (snd (irange fs SBl)) && Z.ltb (snd (irange fs SB8)) 2305843009213693952 &&
   Z.leb 17594333495296 (fst (irange fs PGl)) && sep_noshadow_b fs RT &&
   forallb_l (fun R => if sep_cached a' R then true else sep_noshadow_b fs R) G6)%bool.

(* [comment removed for export] *)
Definition sep_cache_d (fs : list fact) (gs : list (lin * lin * gkind)) (res : list (word * word)) (jP jT : nat) (sp : lin) (a : ast)
    (dc : region -> bool) (rgs : list region) : list (lin * lin) :=
  List.map (fun R => (rg_base R, rg_size R)) (List.filter (fun R => pri_sep_ff fs gs res jP jT sp a R &&& dc R) rgs).
Definition apost_conva (LIMIT : Z) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  let G := s_rgs S in
  obool (a_on a && Nat.eqb (List.length (a_pri a)) 0 && list_eqb pair_eqb (sm_own M) (a_own a))%bool (
  obind (rdw IMGP G (lconst 923512) 8) (fun SBl =>
  obind (rdw IMGP G (lconst 923528) 8) (fun RIBl =>
  obind (ldiv8 SBl) (fun SB8 =>
  let SHl := laddc SB8 2147450880 in
  let TPl := rget (s_regs S) (rk 4) in
  obind (rdw IMGP G (lconst 935460) 4) (fun Kl =>
  obind (is_const Kl) (fun K =>
  obind (rdw IMGP G (laddc TPl (-88)) 8) (fun TSDAl =>
  obind (rdw IMGP G (laddc TSDAl (8 * K)) 8) (fun PTl =>
  obind (rdw IMGP G (laddc PTl 152) 8) (fun Tl =>
  let CAl := laddc Tl 208 in
  obind (find_gsz_acc (sm_maps M) PG_SIZE O) (fun jPG =>
  let PGl := snd jPG in
  obind (find_grant (sm_maps M) Tl TG_SIZE) (fun jT =>
  obind (find_grant (sm_maps M) (fst (a_dep a)) 1048576) (fun jD1 =>
  obind (find_grant (sm_maps M) (snd (a_dep a)) 8388608) (fun jB1 =>
  obind (find_rg_acc' (rg_is (laddc SBl 137438953472) 4096 RZ) G O) (fun iRI =>
  obind (nth_error G iRI) (fun RRI =>
  let G1 := remove_nth iRI G in
  obind (find_rg_acc' (rg_is Tl 4096 RZ) G1 O) (fun iT =>
  obind (nth_error G1 iT) (fun RT =>
  obind (steps_rgs (s_next S) (s_facts S) G1 (cut_steps_k RZ iT Tl (rg_cont RT) 4096 0 [80; 2800; 2872; 2888])) (fun G2 =>
  obind (nth_error G2 iT) (fun RP0 =>
  obind (nth_error G2 (Datatypes.S iT)) (fun RCA =>
  obind (nth_error G2 (2 + iT)) (fun RP2 =>
  obind (nth_error G2 (3 + iT)) (fun RST =>
  (* [comment removed for export] *)
  let G4 := firstn iT G2 ++ weaken_rw RP0 :: RP2 :: weaken_rw RST :: skipn (4 + iT) G2 in
  (* [comment removed for export] *)
  obind (find_const_rg G4 GQ_LO GQ_HI O) (fun fq => let iQ := fst (fst fq) in let bq := snd (fst fq) in let zq := snd fq in
  obind (nth_error G4 iQ) (fun RQ =>
  obind (steps_rgs (s_next S) (s_facts S) G4 (cut_steps_k RZ iQ (lconst bq) (rg_cont RQ) zq 0 [GQ_LO - bq; GQ_HI - bq])) (fun G5 =>
  obind (nth_error G5 (Datatypes.S iQ)) (fun RGQ =>
  let G6 := remove_nth (Datatypes.S iQ) G5 in
  let pri := pri_lins0 SBl SHl CAl PGl Tl in
  let a0 := with_pri a (a_own a) pri in
  let own' := a_own a ++ pri_own a0 in
  let a1 := with_pri a own' pri in
  (* [comment removed for export] *)
  let a' := AST (a_on a1) (a_rgs a1) (a_fcts a1) (a_own a1) (a_dep a1) (a_nl a1)
                (sep_cache_d (s_facts S) (sm_maps M) ASEGSR (fst jPG) jT (sm_sp M) a1
                   (dep_cacheable (s_facts S) M a jD1 jB1 (sep_noshadow_b (s_facts S) (RGz (fst (a_dep a)) 1048576 RZ TEmpty))
                      (sep_noshadow_b (s_facts S) (RGz (snd (a_dep a)) 8388608 RZ TEmpty))) G6) (a_pri a1) in
  let M' := with_own_allow M own' ((SHl, 17179869184) :: sm_allow M) in
  obool (lin_eqb RIBl (laddc SBl 137438953472) && tempty_b (rg_cont RRI) && tempty_b (rg_cont RCA) &&
         rg_is (lconst bq) zq RZ RQ && tzero_b (rg_cont RGQ) &&
         Z.leb 0 (fst (irange (s_facts S) (lsub SBl PGl))) && Z.leb (snd (irange (s_facts S) (lsub SBl PGl))) 65536 &&
         Z.leb 17594333495296 (fst (irange (s_facts S) SBl)) && lal4096 SBl &&
         Z.leb 0 K && Z.leb K 1023 && rdc IMGP G 935456 1 1 &&
         allow_ins_ok LIMIT (s_next S) M O (SHl, 17179869184) &&
         forallb (fun p => lwf (s_next S) (fst p) && lwf (s_next S) (snd p))%bool own' && forallb (lwf (s_next S)) pri &&
         conva_extra S M a a' RT RP0 RCA RST RGQ SBl SB8 PGl Tl G6)%bool (
  Some (with_rgs S G6, M', a')))))))))))))))))))))))))))).
