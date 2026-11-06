(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim StoreOk ShapeSet RealizesCfg AsanAcct AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put AXG_put3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AXG_uw.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMrg.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcComm AcDenW AcHand AcHand0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp AcConvInvLib AcConvInvG.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.AcShift OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcComm OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvInvLib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvInvG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint ctword (c : tree bval) (o : Z) (w : nat) : option Z :=
  match w with
  | O => Some 0
  | Datatypes.S w' => match tget (okey o) c, ctword c (o + 1) w' with
                      | Some (BK b), Some r => if (Z.leb 0 b && Z.ltb b 256)%bool then Some (b + 256 * r) else None
                      | _, _ => None
                      end
  end.
(* [comment removed for export] *)
Definition lword (c : tree bval) (o : Z) : option lin :=
  match tget (okey o) c with
  | Some (BV l j0) => if (Z.eqb j0 0 && forallb (fun j => match tget (okey (o + Z.of_nat j)) c with
                                                          | Some (BV l' j') => (lin_eqb l' l && Z.eqb j' (Z.of_nat j))%bool
                                                          | _ => false end) (seq 1 7))%bool then Some l else None
  | _ => None
  end.
Definition rkind_rwz (k : rkind) : bool := match k with RW | RZ => true | _ => false end.
(* [comment removed for export] *)
Fixpoint find_rec (G : list region) (f : lin) : option (region * Z) :=
  match G with
  | [] => None
  | R :: G' => match lin_off (laddc f (-16)) (rg_base R), is_const (rg_size R) with
               | Some d, Some z => if (rkind_rwz (rg_kind R) && Z.leb 0 d && Z.leb (d + 16) z)%bool then Some (R, d) else find_rec G' f
               | _, _ => find_rec G' f
               end
  end.
(* [comment removed for export] *)
Definition rel_le (fs : list fact) (l f : lin) : bool :=
  if Z.ltb (snd (irange fs (lsub f l))) 9223372036854775808 then Z.ltb (snd (irange fs l)) 9223372036854775808 else false.
Fixpoint uchk (fuel : nat) (fs : list fact) (G : list region) (f : lin) : bool :=
  match fuel with
  | O => false
  | Datatypes.S k =>
      Z.leb 16 (fst (irange fs f)) &&&
      match find_rec G f with
      | Some (R, d) =>
          match ctword (rg_cont R) d 8 with
          | Some v => Z.leb v (fst (irange fs f))
          | None => match lword (rg_cont R) d with
                    | Some l => if Z.leb (snd (irange fs l)) (fst (irange fs f)) then true      (* [comment removed for export] *)
                                else if rel_le fs l f then true else uchk k fs G l
                    | None => false end
          end
      | None => false
      end
  end.

(* [comment removed for export] *)
Lemma ctword_range : forall c w o v, ctword c o w = Some v -> 0 <= v < 2 ^ (8 * Z.of_nat w).
Proof.
  intros c w. induction w as [|w IH]; intros o v H; cbn [ctword] in H.
  - injection H as <-. cbn. lia.
  - destruct (tget (okey o) c) as [[b|l j]|]; try discriminate. destruct (ctword c (o + 1) w) as [r|] eqn:Hr; [|discriminate].
    destruct (Z.leb 0 b && Z.ltb b 256)%bool eqn:Hb; [|discriminate]. injection H as <-.
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. pose proof (IH _ _ Hr) as Rr.
    replace (8 * Z.of_nat (Datatypes.S w)) with (8 + 8 * Z.of_nat w) by lia. rewrite Z.pow_add_r by lia. lia.
Qed.
Lemma ctword_byte : forall c w o v j, ctword c o w = Some v -> (j < w)%nat ->
  exists b, tget (okey (o + Z.of_nat j)) c = Some (BK b) /\ Z_to_bv 8 b = nth j (Z_to_le_bytes w v) (Z_to_bv 8 0).
Proof.
  intros c w. induction w as [|w IH]; intros o v j H Hj; [lia|]. cbn [ctword] in H.
  destruct (tget (okey o) c) as [[b|l jj]|] eqn:Ht; try discriminate. destruct (ctword c (o + 1) w) as [r|] eqn:Hr; [|discriminate].
  destruct (Z.leb 0 b && Z.ltb b 256)%bool eqn:Hb; [|discriminate]. injection H as <-.
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. pose proof (ctword_range _ _ _ _ Hr) as Rr.
  rewrite le_bytes_cons by lia. destruct j as [|j].
  - exists b. rewrite Z.add_0_r. split; [exact Ht | reflexivity].
  - destruct (IH (o + 1) r j Hr ltac:(lia)) as (b' & Hb' & E'). exists b'. split.
    + replace (o + Z.of_nat (Datatypes.S j)) with (o + 1 + Z.of_nat j) by lia. exact Hb'.
    + cbn [nth]. exact E'.
Qed.
Lemma find_rec_sound : forall G f R d, find_rec G f = Some (R, d) ->
  In R G /\ lin_off (laddc f (-16)) (rg_base R) = Some d /\ exists z, is_const (rg_size R) = Some z /\ rkind_rwz (rg_kind R) = true /\ 0 <= d /\ d + 16 <= z.
Proof.
  induction G as [|R0 G IH]; intros f R d H; cbn [find_rec] in H; [discriminate|].
  destruct (lin_off (laddc f (-16)) (rg_base R0)) as [d0|] eqn:Hd0; [|destruct (IH f R d H) as (A & B & C); split; [right; exact A | split; [exact B | exact C]]].
  destruct (is_const (rg_size R0)) as [z0|] eqn:Hz0; [|destruct (IH f R d H) as (A & B & C); split; [right; exact A | split; [exact B | exact C]]].
  destruct (rkind_rwz (rg_kind R0) && Z.leb 0 d0 && Z.leb (d0 + 16) z0)%bool eqn:Hc.
  - injection H as <- <-. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H2, H3.
    split; [left; reflexivity|]. split; [exact Hd0|]. exists z0. split; [exact Hz0|]. split; [exact H1|]. lia.
  - destruct (IH f R d H) as (A & B & C). split; [right; exact A | split; [exact B | exact C]].
Qed.

Section Sound.
Variable E : valu.
Variable m : word -> option byte.
Variable fs : list fact.
Variable G : list region.
Variable TOP : Z.
Hypothesis HF : Forall (fact_ok E) fs.
Hypothesis HG : Forall (rg_ok SEGS E m) G.
Hypothesis HTOP : TOP <= 2^47.

(* [comment removed for export] *)
#[using="HG"] Lemma rec_bytes : forall f R d z, In R G -> lin_off (laddc f (-16)) (rg_base R) = Some d -> is_const (rg_size R) = Some z ->
  rkind_rwz (rg_kind R) = true -> 0 <= d -> d + 16 <= z -> 16 <= uE E f ->
  uE E f - 16 = uE E (rg_base R) + d /\ (forall i, uE E f - 16 <= i < uE E f -> rd1 SEGS m (Z_to_bv 64 i) <> None) /\
  (forall j v, tget (okey (d + Z.of_nat j)) (rg_cont R) = Some v -> rd1 SEGS m (Z_to_bv 64 (uE E f - 16 + Z.of_nat j)) = Some (bden E v)).
Proof. LiaFast.lf_pins (fun (HG : LiaFast.U) => LiaFast.u0).
  intros f R d z HR Hd Hz Hk Hd0 Hdz Hf.
  rewrite Forall_forall in HG. pose proof (HG R HR) as Rok. pose proof Rok as Rok'. destruct Rok' as (Rz & Rb & Rall & _).
  assert (Ez : rsz E R = z) by (unfold rsz; destruct (is_const_sound E _ z Hz) as [H1 H2]; rewrite H1; apply u_small64; exact H2).
  destruct (lin_off_sound E _ _ _ Hd) as [Hl Hr]. rewrite lden_lsub, lden_laddc in Hl.
  assert (Ed : uE E f - 16 = uE E (rg_base R) + d).
  { pose proof (uE_range E f) as Rf. pose proof (uE_range E (rg_base R)) as Rbb. unfold uE in *.
    assert (X : bv_unsigned (Z_to_bv 64 (bv_unsigned (lden E f) + -16) - lden E (rg_base R))%bv = d) by (rewrite Hl; apply u_small64; exact Hr).
    rewrite bv_sub_unsigned in X. rewrite Z_to_bv_unsigned in X. unfold bv_wrap, bv_modulus in X. change (2 ^ Z.of_N 64) with two64 in X.
    rewrite (Z.mod_small (bv_unsigned (lden E f) + -16)) in X by (unfold two64 in *; lia).
    unfold two64 in *. rewrite Ez in Rb.
    destruct (Z_le_gt_dec (bv_unsigned (lden E (rg_base R))) (bv_unsigned (lden E f) - 16)) as [Q|Q].
    - rewrite Z.mod_small in X by lia. lia.
    - exfalso. assert (Y : (bv_unsigned (lden E f) + -16 - bv_unsigned (lden E (rg_base R))) mod 18446744073709551616 =
                             bv_unsigned (lden E f) + -16 - bv_unsigned (lden E (rg_base R)) + 18446744073709551616) by (symmetry; apply Z.mod_unique with (-1); lia).
      rewrite Y in X. lia. }
  split; [exact Ed|]. split.
  - intros i Hi. specialize (Rall (i - uE E (rg_base R)) ltac:(rewrite Ez; lia)). unfold uE in *.
    replace (bv_unsigned (lden E (rg_base R)) + (i - bv_unsigned (lden E (rg_base R)))) with i in Rall by lia.
    destruct (rg_kind R); try discriminate; [exact (proj1 Rall) | exact (proj1 (proj1 Rall))].
  - intros j v Ht. destruct Rok as (_ & _ & _ & HT). destruct (HT _ _ Ht) as [_ X]. unfold okey in X. rewrite Z2Pos.id in X by lia.
    replace (bv_unsigned (lden E (rg_base R)) + (d + Z.of_nat j + 1 - 1)) with (uE E f - 16 + Z.of_nat j) in X by (unfold uE in *; lia). exact X.
Qed.

#[using="HF HG HTOP"] Theorem uchk_sound : forall fuel f, uchk fuel fs G f = true -> uch m TOP (uE E f).
Proof. LiaFast.lf_pins (fun (HF HG HTOP : LiaFast.U) => LiaFast.u0).
  induction fuel as [|k IH]; intros f H; cbn [uchk] in H; [discriminate|].
  apply andb_prop in H as [H16 H]. apply Z.leb_le in H16.
  pose proof (irange_sound E fs f HF) as Rf. fold (uE E f) in Rf.
  destruct (find_rec G f) as [[R d]|] eqn:Hfr; [|discriminate].
  destruct (find_rec_sound G f R d Hfr) as (HR & Hd & z & Hz & Hk & Hd0 & Hdz).
  destruct (rec_bytes f R d z HR Hd Hz Hk Hd0 Hdz ltac:(lia)) as (Ed & Hrd & Htr).
  pose proof (uE_range E f) as Rff. unfold two64 in Rff.
  apply uch_mk.
  - apply (rdn_some m (uE E f - 8) 8); [lia | cbn; unfold two64; lia |]. intros i Hi. apply Hrd. cbn in Hi. lia.
  - apply (rdn_some m (uE E f - 16) 8); [lia | cbn; unfold two64; lia |]. intros i Hi. apply Hrd. cbn in Hi. lia.
  - intros nb Hnb H1 H2 H3.
    destruct (ctword (rg_cont R) d 8) as [v|] eqn:Hcw.
    + (* [comment removed for export] *)
      exfalso. apply Z.leb_le in H. pose proof (ctword_range _ _ _ _ Hcw) as Rv. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rv.
      assert (Hrv : rd m (uE E f - 16) 8 v).
      { unfold rd, word_to_le_bytes. rewrite u_wa_small by lia.
        assert (Hl : length (Z_to_le_bytes 8 v) = 8%nat) by apply length_Z_to_le_bytes. rewrite <- Hl.
        unfold wa. apply rdn_of_rd1; [lia | rewrite Hl; unfold two64; lia |]. rewrite Hl. intros j Hj.
        destruct (ctword_byte _ 8 d v j Hcw Hj) as (b & Hb & Eb). rewrite (Htr j _ Hb). cbn [bden].
        rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite length_Z_to_le_bytes; exact Hj). f_equal. exact Eb. }
      assert (Hnv : nb = v) by (apply (rd_inj m (uE E f - 16) 8 nb v); [lia | | | exact Hnb | exact Hrv];
                                change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
      lia.
    + destruct (lword (rg_cont R) d) as [l|] eqn:Hlw; [|discriminate].
      (* [comment removed for export] *)
      assert (Hrl : rd m (uE E f - 16) 8 (uE E l)).
      { pose proof (uE_range E l) as Rl. unfold two64 in Rl.
        apply rd_of_rd1; [lia | unfold two64; lia |]. intros j Hj.
        unfold lword in Hlw. destruct (tget (okey d) (rg_cont R)) as [[b|l0 j0]|] eqn:H0; try discriminate.
        destruct (Z.eqb j0 0 && forallb _ (seq 1 7))%bool eqn:Hall; [|discriminate]. injection Hlw as <-.
        apply andb_prop in Hall as [Hj0 Hall]. apply Z.eqb_eq in Hj0. subst j0.
        assert (Ht : tget (okey (d + Z.of_nat j)) (rg_cont R) = Some (BV l0 (Z.of_nat j))).
        { destruct j as [|j]; [rewrite Z.add_0_r; exact H0|]. rewrite forallb_forall in Hall. specialize (Hall (Datatypes.S j) ltac:(apply in_seq; lia)).
          destruct (tget (okey (d + Z.of_nat (Datatypes.S j))) (rg_cont R)) as [[b|l1 j1]|]; try discriminate.
          apply andb_prop in Hall as [A1 A2]. apply lin_eqb_eq in A1. apply Z.eqb_eq in A2. subst. reflexivity. }
        rewrite (Htr j _ Ht). unfold word_to_le_bytes. rewrite u_wa_small by lia. rewrite nth_Z_to_le_bytes by exact Hj.
        cbn [bden]. unfold uE. reflexivity. }
      assert (Hnl : nb = uE E l).
      { apply (rd_inj m (uE E f - 16) 8 nb (uE E l)); [lia | | | exact Hnb | exact Hrl]; change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64);
          [lia | pose proof (uE_range E l); unfold two64 in *; lia]. }
      subst nb. destruct (Z.leb (snd (irange fs l)) (fst (irange fs f))) eqn:Hlow.
      * (* [comment removed for export] *)
        exfalso. apply Z.leb_le in Hlow. pose proof (irange_sound E fs l HF) as Rl. fold (uE E l) in Rl. lia.
      * destruct (rel_le fs l f) eqn:Hrel; [|exact (IH l H)].
        exfalso. unfold rel_le in Hrel. destruct (Z.ltb (snd (irange fs (lsub f l))) 9223372036854775808) eqn:Hr1; [|discriminate].
        apply Z.ltb_lt in Hr1, Hrel. pose proof (irange_sound E fs l HF) as Rl. fold (uE E l) in Rl.
        pose proof (irange_sound E fs (lsub f l) HF) as Rd. fold (uE E (lsub f l)) in Rd.
        destruct (small_diff E f l _ _ Rd) as [[Hle _]|[Hlt He]]; unfold two64 in *; lia.
Qed.
End Sound.
