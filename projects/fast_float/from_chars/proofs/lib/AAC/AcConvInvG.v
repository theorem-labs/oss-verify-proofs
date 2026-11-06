(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxSubst FxEnt FxCall FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put AXG_put3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConvInvLib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvInvLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition cbyte (c : tree bval) (o : Z) : option Z :=
  match tget (okey o) c with Some (BK b) => if (Z.leb 0 b && Z.ltb b 256)%bool then Some b else None | Some _ => None | None => Some 0 end.
(* [comment removed for export] *)
Fixpoint cword (c : tree bval) (o : Z) (w : nat) : option Z :=
  match w with
  | O => Some 0
  | Datatypes.S w' => match cbyte c o, cword c (o + 1) w' with Some b, Some r => Some (b + 256 * r) | _, _ => None end
  end.
(* [comment removed for export] *)
Fixpoint chain_b (cd : tree bval) (n : Z) (fuel : nat) (id : Z) : bool :=
  match fuel with
  | O => Z.eqb id 0
  | Datatypes.S f => (Z.eqb id 0 || (Z.leb 1 id && Z.leb id n && Z.ltb (16 * id + 16) 1048576 &&
                      match cword cd (16 * id + 8) 4 with Some lk => (Z.ltb lk id && chain_b cd n f lk)%bool | None => false end))%bool
  end.
(* [comment removed for export] *)
Definition tab_ok_g (ct cd : tree bval) (n : Z) (fuel : nat) : bool :=
  tforall (fun p v => let o := Zpos p - 1 in
             if (Z.leb 3224 o && Z.ltb o 4197528)%bool then
               let b := (o - 3224) / 4 in
               match cword ct (3224 + 4 * b) 4 with Some hd => (Z.ltb hd 2147483648 && chain_b cd n fuel hd)%bool | None => false end
             else (Z.leb 4197528 o && Z.ltb o 4197552)%bool) ct.

Lemma cbyte_range : forall c o b, cbyte c o = Some b -> 0 <= b < 256.
Proof.
  intros c o b H. unfold cbyte in H. destruct (tget (okey o) c) as [[x|l j]|]; try discriminate.
  - destruct (Z.leb 0 x && Z.ltb x 256)%bool eqn:Hx; [|discriminate]. injection H as <-. apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
  - injection H as <-. lia.
Qed.
Lemma cword_range : forall c w o v, cword c o w = Some v -> 0 <= v < 2 ^ (8 * Z.of_nat w).
Proof.
  intros c w. induction w as [|w IH]; intros o v H; cbn [cword] in H.
  - injection H as <-. cbn. lia.
  - destruct (cbyte c o) as [b|] eqn:Hb; [|discriminate]. destruct (cword c (o + 1) w) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
    pose proof (cbyte_range _ _ _ Hb) as Rb. pose proof (IH _ _ Hr) as Rr.
    replace (8 * Z.of_nat (Datatypes.S w)) with (8 + 8 * Z.of_nat w) by lia. rewrite Z.pow_add_r by lia. lia.
Qed.
Lemma le_bytes_cons : forall w b r, 0 <= b < 256 -> 0 <= r ->
  Z_to_le_bytes (Datatypes.S w) (b + 256 * r) = Z_to_bv 8 b :: Z_to_le_bytes w r.
Proof.
  intros w b r Hb Hr. cbn [Z_to_le_bytes]. f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    replace (b + 256 * r) with (b + r * 256) by lia. rewrite Z_mod_plus_full. reflexivity.
  - f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. replace (b + 256 * r) with (b + r * 256) by lia.
    rewrite Z_div_plus_full by lia. rewrite Z.div_small by lia. lia.
Qed.

Section CWord.
Variable E : valu.
Variable m : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Lemma cword_bytes : forall bl zl c w o v, rg_ok SEGS E m (RG bl zl RZ c) -> 0 <= o -> o + Z.of_nat w <= rsz E (RG bl zl RZ c) ->
  cword c o w = Some v -> forall j, (j < w)%nat -> rd1 SEGS m (Z_to_bv 64 (uE E bl + o + Z.of_nat j)) = nth_error (Z_to_le_bytes w v) j.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bl zl c w. induction w as [|w IH]; intros o v HR Ho Hz Hc j Hj; [lia|].
  cbn [cword] in Hc. destruct (cbyte c o) as [b|] eqn:Hb; [|discriminate]. destruct (cword c (o + 1) w) as [r|] eqn:Hr; [|discriminate].
  injection Hc as <-. pose proof (cbyte_range _ _ _ Hb) as Rb'. pose proof (cword_range _ _ _ _ Hr) as Rr.
  rewrite le_bytes_cons by lia. destruct j as [|j].
  - cbn [nth_error]. rewrite Z.add_0_r. unfold cbyte in Hb. destruct (tget (okey o) c) as [[x|l jj]|] eqn:Ht; try discriminate.
    + destruct (Z.leb 0 x && Z.ltb x 256)%bool; [|discriminate]. injection Hb as <-.
      rewrite (byte_tracked E m bl zl RZ c o (BK x) HR Ho Ht). reflexivity.
    + injection Hb as <-. rewrite (byte_rz E m bl zl c o HR ltac:(lia) Ht). reflexivity.
  - cbn [nth_error]. replace (uE E bl + o + Z.of_nat (Datatypes.S j)) with (uE E bl + (o + 1) + Z.of_nat j) by lia.
    apply (IH (o + 1) r HR ltac:(lia) ltac:(lia) Hr j ltac:(lia)).
Qed.

#[using="Type"] Lemma cword_rd : forall bl zl c o w v, rg_ok SEGS E m (RG bl zl RZ c) -> 0 <= o -> o + Z.of_nat w <= rsz E (RG bl zl RZ c) ->
  uE E bl + o + Z.of_nat w <= two64 -> (w <= 8)%nat -> cword c o w = Some v -> rd m (uE E bl + o) w v.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bl zl c o w v HR Ho Hz Hw H8 Hc. assert (Rb : 0 <= uE E bl) by (unfold uE; pose proof (bv_unsigned_in_range _ (lden E bl)) as X; unfold bv_modulus in X; lia).
  pose proof (cword_range _ _ _ _ Hc) as Rv.
  assert (Hv64 : v < 2 ^ 64) by (apply (Z.lt_le_trans _ (2 ^ (8 * Z.of_nat w))); [lia | apply Z.pow_le_mono_r; lia]).
  apply rd_of_rd1; [lia | exact Hw |]. unfold word_to_le_bytes, wa. rewrite u_small64 by (unfold two64; lia).
  exact (cword_bytes bl zl c w o v HR Ho Hz Hc).
Qed.
End CWord.

Section MainG.
Variables (E : valu) (m : word -> option byte) (D1l B1l : lin) (ct cs cd cb : tree bval) (n F st : Z) (fuel : nat).
Hypothesis Rt : rg_ok SEGS E m (RG (lconst 1859584) (lconst 4198400) RZ ct).
Hypothesis Rs : rg_ok SEGS E m (RG (lconst 1794048) (lconst 4096) RZ cs).
Hypothesis Rd : rg_ok SEGS E m (RG D1l (lconst 1048576) RZ cd).
Hypothesis Rb : rg_ok SEGS E m (RG B1l (lconst 8388608) RZ cb).
Hypothesis Htab : tab_ok_g ct cd n fuel = true.
Hypothesis Hn : cword ct 4197528 4 = Some n.
Hypothesis Hnr : 0 <= n <= 65533.
Hypothesis Hmap : fb ct (bv_list 4197544 D1l 8) = true.
Hypothesis HF : cword cs 3208 8 = Some F.
Hypothesis Hst : cword cs 3232 4 = Some st.
Hypothesis HFr : 0 <= st <= F /\ F <= 1048000.
Hypothesis HsD : fb cs (bv_list 3224 B1l 8) = true.
Hypothesis HD1 : 6529024 <= uE E D1l /\ uE E D1l + 1048576 <= 2^47 /\ uE E D1l mod 16 = 0.
Hypothesis HB1 : 6529024 <= uE E B1l /\ uE E B1l + 8388608 <= 2^47 /\ uE E B1l mod 8 = 0.
Hypothesis Hap : uE E D1l + 1048576 <= uE E B1l \/ uE E B1l + 8388608 <= uE E D1l.

#[using="B1l cd Rd"] Lemma Rd1' : forall i, 0 <= i < 1048576 -> rd1 SEGS m (Z_to_bv 64 (uE E D1l + i)) <> None /\ wview SEGS m (Z_to_bv 64 (uE E D1l + i)) <> None.
Proof. LiaFast.lf_pins (fun (B1l cd Rd : LiaFast.U) => LiaFast.u0). intros i Hi. exact (rg_ok_rw_byte SEGS E m _ Rd eq_refl i ltac:(rewrite rsz_lconst' by (unfold two64; lia); lia)). Qed.

#[using="Type"] Lemma rd_readable' : forall a w, 0 <= a -> a + Z.of_nat w <= two64 -> (w <= 8)%nat ->
  (forall i, 0 <= i < Z.of_nat w -> rd1 SEGS m (Z_to_bv 64 (a + i)) <> None) -> exists v, 0 <= v < 2^(8 * Z.of_nat w) /\ v < 2^64 /\ rd m a w v.
Proof. LiaFast.lf_pins LiaFast.u0. intros a w Ha Hw H8 H. destruct (rdn_some m a w Ha Hw H) as (bs & Hbs). exact (rd_exists m a w bs H8 Hbs). Qed.

#[using="B1l Rd Hnr HD1 HB1"] Lemma chain_b_sound : forall f id, chain_b cd n f id = true -> chainz m (uE E D1l) n f id.
Proof. LiaFast.lf_pins (fun (B1l Rd Hnr HD1 HB1 : LiaFast.U) => LiaFast.u0).
  destruct HD1 as (D1a & D1b & D1c).
  induction f as [|f IH]; intros id H; cbn [chain_b] in H; cbn [chainz].
  - apply Z.eqb_eq in H. exact H.
  - apply orb_prop in H as [H|H]; [left; apply Z.eqb_eq in H; exact H|]. right.
    apply andb_prop in H as [H Hl]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. apply Z.ltb_lt in H3.
    destruct (cword cd (16 * id + 8) 4) as [lk|] eqn:Hlk; [|discriminate]. apply andb_prop in Hl as [Hlt Hc]. apply Z.ltb_lt in Hlt.
    split; [lia|].
    destruct (rd_readable' (uE E D1l + 16 * id) 8 ltac:(lia) ltac:(unfold two64; lia) ltac:(lia)) as (hv & Hhv & _ & Hrd).
    { intros i Hi. replace (uE E D1l + 16 * id + i) with (uE E D1l + (16 * id + i)) by lia. exact (proj1 (Rd1' (16 * id + i) ltac:(lia))). }
    exists hv, lk. split; [exact Hhv|]. pose proof (cword_range _ _ _ _ Hlk) as Rlk. split; [lia|]. split; [exact Hrd|]. split.
    + pose proof (cword_rd E m D1l (lconst 1048576) cd (16 * id + 8) 4 lk Rd ltac:(lia) ltac:(rewrite rsz_lconst' by (unfold two64; lia); cbn; lia)
                    ltac:(unfold two64; lia) ltac:(lia) Hlk) as X. replace (uE E D1l + 16 * id + 8) with (uE E D1l + (16 * id + 8)) by lia. exact X.
    + exact (IH lk Hc).
Qed.
End MainG.

Section MainG2.
Variables (E : valu) (m : word -> option byte) (D1l B1l : lin) (ct cs cd cb : tree bval) (n F st : Z) (fuel : nat).
Hypothesis Rt : rg_ok SEGS E m (RG (lconst 1859584) (lconst 4198400) RZ ct).
Hypothesis Rs : rg_ok SEGS E m (RG (lconst 1794048) (lconst 4096) RZ cs).
Hypothesis Rd : rg_ok SEGS E m (RG D1l (lconst 1048576) RZ cd).
Hypothesis Rb : rg_ok SEGS E m (RG B1l (lconst 8388608) RZ cb).
Hypothesis Htab : tab_ok_g ct cd n fuel = true.
Hypothesis Hn : cword ct 4197528 4 = Some n.
Hypothesis Hnr : 0 <= n <= 65533.
Hypothesis Hmap : fb ct (bv_list 4197544 D1l 8) = true.
Hypothesis HF : cword cs 3208 8 = Some F.
Hypothesis Hst : cword cs 3232 4 = Some st.
Hypothesis HFr : 0 <= st <= F /\ F <= 1048000.
Hypothesis HsD : fb cs (bv_list 3224 B1l 8) = true.
Hypothesis HD1 : 6529024 <= uE E D1l /\ uE E D1l + 1048576 <= 2^47 /\ uE E D1l mod 16 = 0.
Hypothesis HB1 : 6529024 <= uE E B1l /\ uE E B1l + 8388608 <= 2^47 /\ uE E B1l mod 8 = 0.
Hypothesis Hap : uE E D1l + 1048576 <= uE E B1l \/ uE E B1l + 8388608 <= uE E D1l.

#[using="E D1l B1l Htab HD1 HB1"] Lemma tab_bucket : forall b, 0 <= b < 1048576 -> exists hd, cword ct (3224 + 4 * b) 4 = Some hd /\ hd < 2147483648 /\ chain_b cd n fuel hd = true.
Proof. LiaFast.lf_pins (fun (E D1l B1l Htab HD1 HB1 : LiaFast.U) => LiaFast.u0).
  intros b Hb.
  assert (Hchk : forall j, (j < 4)%nat -> tget (okey (3224 + 4 * b + Z.of_nat j)) ct <> None ->
            exists hd, cword ct (3224 + 4 * b) 4 = Some hd /\ hd < 2147483648 /\ chain_b cd n fuel hd = true).
  { intros j Hj Ht. destruct (tget (okey (3224 + 4 * b + Z.of_nat j)) ct) as [v|] eqn:Hv; [|exfalso; apply Ht; reflexivity].
    pose proof (tforall_spec _ _ Htab _ _ Hv) as X. cbv beta zeta in X. unfold okey in X. rewrite Z2Pos.id in X by lia.
    replace (3224 + 4 * b + Z.of_nat j + 1 - 1) with (3224 + 4 * b + Z.of_nat j) in X by lia.
    rewrite (proj2 (Z.leb_le 3224 _)) in X by lia. rewrite (proj2 (Z.ltb_lt _ 4197528)) in X by lia. cbn [andb] in X.
    replace ((3224 + 4 * b + Z.of_nat j - 3224) / 4) with b in X.
    2: { replace (3224 + 4 * b + Z.of_nat j - 3224) with (Z.of_nat j + b * 4) by lia. rewrite Z_div_plus_full by lia. rewrite Z.div_small by lia. lia. }
    destruct (cword ct (3224 + 4 * b) 4) as [hd|]; [|discriminate]. apply andb_prop in X as [X1 X2]. apply Z.ltb_lt in X1.
    exists hd. split; [reflexivity|]. split; [exact X1 | exact X2]. }
  destruct (tget (okey (3224 + 4 * b + Z.of_nat 0)) ct) eqn:T0; [apply (Hchk 0%nat); [lia | rewrite T0; discriminate]|].
  destruct (tget (okey (3224 + 4 * b + Z.of_nat 1)) ct) eqn:T1; [apply (Hchk 1%nat); [lia | rewrite T1; discriminate]|].
  destruct (tget (okey (3224 + 4 * b + Z.of_nat 2)) ct) eqn:T2; [apply (Hchk 2%nat); [lia | rewrite T2; discriminate]|].
  destruct (tget (okey (3224 + 4 * b + Z.of_nat 3)) ct) eqn:T3; [apply (Hchk 3%nat); [lia | rewrite T3; discriminate]|].
  exists 0. split; [|split; [lia | destruct fuel; reflexivity]].
  cbn [cword]. unfold cbyte. rewrite Z.add_0_r in T0. rewrite T0.
  replace (3224 + 4 * b + 1) with (3224 + 4 * b + Z.of_nat 1) by reflexivity. rewrite T1.
  replace (3224 + 4 * b + Z.of_nat 1 + 1) with (3224 + 4 * b + Z.of_nat 2) by (cbn; lia). rewrite T2.
  replace (3224 + 4 * b + Z.of_nat 2 + 1) with (3224 + 4 * b + Z.of_nat 3) by (cbn; lia). rewrite T3. reflexivity.
Qed.

#[using="ct cs cd cb fuel Rt Rs Rd Rb Htab Hn Hnr Hmap HF Hst HFr HsD HD1 HB1 Hap"] Theorem inv_d_main_g : INV_D m (uE E D1l) (uE E B1l) n F st.
Proof. LiaFast.lf_pins (fun (ct cs cd cb fuel Rt Rs Rd Rb Htab Hn Hnr Hmap HF Hst HFr HsD HD1 HB1 Hap : LiaFast.U) => LiaFast.u0).
  assert (Et : uE E (lconst 1859584) = 1859584) by (apply uE_lconst'; unfold two64; lia).
  assert (Es : uE E (lconst 1794048) = 1794048) by (apply uE_lconst'; unfold two64; lia).
  assert (Zt : rsz E (RG (lconst 1859584) (lconst 4198400) RZ ct) = 4198400) by (apply rsz_lconst'; unfold two64; lia).
  assert (Zs : rsz E (RG (lconst 1794048) (lconst 4096) RZ cs) = 4096) by (apply rsz_lconst'; unfold two64; lia).
  destruct HD1 as (D1a & D1b & D1c). destruct HB1 as (B1a & B1b & B1c).
  assert (Rd1 : forall i, 0 <= i < 1048576 -> rd1 SEGS m (Z_to_bv 64 (uE E D1l + i)) <> None /\ wview SEGS m (Z_to_bv 64 (uE E D1l + i)) <> None).
  { intros i Hi. exact (rg_ok_rw_byte SEGS E m _ Rd eq_refl i ltac:(rewrite rsz_lconst' by (unfold two64; lia); lia)). }
  assert (Rb1 : forall i, 0 <= i < 8388608 -> wview SEGS m (Z_to_bv 64 (uE E B1l + i)) <> None).
  { intros i Hi. exact (proj2 (rg_ok_rw_byte SEGS E m _ Rb eq_refl i ltac:(rewrite rsz_lconst' by (unfold two64; lia); lia))). }
  assert (Rt1 : forall i, 0 <= i < 4198400 -> wview SEGS m (Z_to_bv 64 (1859584 + i)) <> None).
  { intros i Hi. pose proof (proj2 (rg_ok_rw_byte SEGS E m _ Rt eq_refl i ltac:(rewrite Zt; lia))) as X.
    cbn [rg_base] in X. fold (uE E (lconst 1859584)) in X. rewrite Et in X. exact X. }
  assert (Rs1 : forall i, 0 <= i < 4096 -> wview SEGS m (Z_to_bv 64 (1794048 + i)) <> None).
  { intros i Hi. pose proof (proj2 (rg_ok_rw_byte SEGS E m _ Rs eq_refl i ltac:(rewrite Zs; lia))) as X.
    cbn [rg_base] in X. fold (uE E (lconst 1794048)) in X. rewrite Es in X. exact X. }
  constructor.
  - pose proof (cword_rd E m _ _ _ 4197528 4 n Rt ltac:(lia) ltac:(rewrite Zt; cbn; lia) ltac:(rewrite Et; cbn; unfold two64; lia) ltac:(lia) Hn) as X.
    rewrite Et in X. exact X.
  - exact Hnr.
  - pose proof (rd_bv E m _ _ _ _ 4197544 D1l Rt ltac:(lia) ltac:(rewrite Et; unfold two64; lia) Hmap) as X. rewrite Et in X. exact X.
  - split; [lia|]. split; [exact D1b | exact D1c].
  - intros b Hb. destruct (tab_bucket b Hb) as (hd & Hw & Hhd & Hc). exists hd. pose proof (cword_range _ _ _ _ Hw) as Rhd.
    split; [lia|]. split.
    + pose proof (cword_rd E m _ _ _ (3224 + 4 * b) 4 hd Rt ltac:(lia) ltac:(rewrite Zt; cbn; lia) ltac:(rewrite Et; cbn; unfold two64; lia) ltac:(lia) Hw) as X.
      rewrite Et in X. replace (1862808 + 4 * b) with (1859584 + (3224 + 4 * b)) by lia. exact X.
    + exists fuel. exact (chain_b_sound E m D1l B1l cd n Rd Hnr (conj D1a (conj D1b D1c)) (conj B1a (conj B1b B1c)) fuel hd Hc).
  - pose proof (cword_rd E m _ _ _ 3208 8 F Rs ltac:(lia) ltac:(rewrite Zs; cbn; lia) ltac:(rewrite Es; cbn; unfold two64; lia) ltac:(lia) HF) as X.
    rewrite Es in X. exact X.
  - pose proof (cword_rd E m _ _ _ 3232 4 st Rs ltac:(lia) ltac:(rewrite Zs; cbn; lia) ltac:(rewrite Es; cbn; unfold two64; lia) ltac:(lia) Hst) as X.
    rewrite Es in X. exact X.
  - exact HFr.
  - pose proof (rd_bv E m _ _ _ _ 3224 B1l Rs ltac:(lia) ltac:(rewrite Es; unfold two64; lia) HsD) as X. rewrite Es in X. exact X.
  - split; [lia|]. split; [exact B1b | exact B1c].
  - intros x Hx. unfold downed in Hx. unfold wa.
    destruct Hx as [X|[X|[X|[X|[X|X]]]]].
    + replace x with (1859584 + (x - 1859584)) by lia. apply Rt1. lia.
    + replace x with (1859584 + (x - 1859584)) by lia. apply Rt1. lia.
    + replace x with (1859584 + (x - 1859584)) by lia. apply Rt1. lia.
    + replace x with (uE E D1l + (x - uE E D1l)) by lia. apply Rd1. lia.
    + replace x with (1794048 + (x - 1794048)) by lia. apply Rs1. lia.
    + replace x with (uE E B1l + (x - uE E B1l)) by lia. apply Rb1. lia.
  - split; [lia|]. split; [lia | exact Hap].
  - destruct (rdn_some m (uE E D1l) 8 ltac:(lia) ltac:(unfold two64; cbn; lia)) as (bs0 & Hbs0).
    { intros i Hi. exact (proj1 (Rd1 i ltac:(cbn in Hi; lia))). }
    destruct (rd_exists m (uE E D1l) 8 bs0 ltac:(lia) Hbs0) as (hv & Hhv & _ & Hrd0).
    destruct (rdn_some m (uE E D1l + 8) 4 ltac:(lia) ltac:(unfold two64; cbn; lia)) as (bs1 & Hbs1).
    { intros i Hi. replace (uE E D1l + 8 + i) with (uE E D1l + (8 + i)) by lia. exact (proj1 (Rd1 (8 + i) ltac:(cbn in Hi; lia))). }
    destruct (rd_exists m (uE E D1l + 8) 4 bs1 ltac:(lia) Hbs1) as (lk & Hlk & _ & Hrd8).
    exists hv, lk. split; [exact Hhv|]. split; [exact Hlk|]. split; [exact Hrd0 | exact Hrd8].
Qed.
End MainG2.
