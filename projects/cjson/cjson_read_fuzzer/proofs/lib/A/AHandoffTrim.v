(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require MainExport.
Module AHandoffSh.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.MainExport.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lin : Type := (list (nat * Z) * Z)%type.

Fixpoint lden_l (V : nat -> Z) (l : list (nat * Z)) : Z :=
  match l with [] => 0 | (v, c) :: t => c * V v + lden_l V t end.
Definition lden (V : nat -> Z) (l : lin) : Z := lden_l V (fst l) + snd l.

Fixpoint ladd_var (v : nat) (c : Z) (l : list (nat * Z)) : list (nat * Z) :=
  match l with
  | [] => [(v, c)]
  | (v', c') :: t => if Nat.eqb v v' then (v', c + c') :: t
                     else if Nat.ltb v v' then (v, c) :: l else (v', c') :: ladd_var v c t
  end.

Lemma lden_ladd_var : forall V v c l, lden_l V (ladd_var v c l) = c * V v + lden_l V l.
Proof.
  intros V v c l. induction l as [|[v' c'] t IH]; cbn [ladd_var lden_l]; [lia|].
  destruct (Nat.eqb_spec v v') as [->|Hne]; [cbn [lden_l]; lia|].
  destruct (Nat.ltb v v'); cbn [lden_l]; [lia | rewrite IH; lia].
Qed.

Fixpoint lmerge (l1 l2 : list (nat * Z)) : list (nat * Z) :=
  match l1 with [] => l2 | (v, c) :: t => ladd_var v c (lmerge t l2) end.

Lemma lden_lmerge : forall V l1 l2, lden_l V (lmerge l1 l2) = lden_l V l1 + lden_l V l2.
Proof. intros V l1 l2. induction l1 as [|[v c] t IH]; cbn [lmerge lden_l]; [lia|]. rewrite lden_ladd_var, IH. lia. Qed.

Definition lscale (k : Z) (l : list (nat * Z)) : list (nat * Z) := List.map (fun p => (fst p, k * snd p)) l.

Lemma lden_lscale : forall V k l, lden_l V (lscale k l) = k * lden_l V l.
Proof. intros V k l. induction l as [|[v c] t IH]; cbn [lscale List.map lden_l fst snd]; [lia|]. unfold lscale in IH. rewrite IH. lia. Qed.

Fixpoint zlin (e : zexp) : option lin :=
  match e with
  | ZLit z => Some ([], z)
  | ZV n => Some ([(n, 1)], 0)
  | ZAdd a b => match zlin a, zlin b with
                | Some la, Some lb => Some (lmerge (fst la) (fst lb), snd la + snd lb)
                | _, _ => None
                end
  | ZMul (ZLit k) x => match zlin x with Some l => Some (lscale k (fst l), k * snd l) | None => None end
  | _ => None
  end.

Lemma zlin_sound : forall V e l, zlin e = Some l -> zv V e = lden V l.
Proof.
  intros V e. induction e as [z|n|a IHa b IHb|a IHa b IHb|a IHa b IHb|a IHa b IHb]; intros l H; cbn [zlin] in H; try discriminate.
  - injection H as <-. reflexivity.
  - injection H as <-. unfold lden. cbn. lia.
  - destruct (zlin a) as [la|]; [|discriminate]. destruct (zlin b) as [lb|]; [|discriminate]. injection H as <-.
    cbn [zv]. rewrite (IHa la eq_refl), (IHb lb eq_refl). unfold lden. cbn [fst snd]. rewrite lden_lmerge. lia.
  - destruct a as [k| | | | |]; try discriminate. destruct (zlin b) as [lb|]; [|discriminate]. injection H as <-.
    cbn [zv]. rewrite (IHb lb eq_refl). unfold lden. cbn [fst snd]. rewrite lden_lscale. lia.
Qed.

(* [comment removed for export] *)
Definition lnz (l : list (nat * Z)) : list (nat * Z) := List.filter (fun p => negb (snd p =? 0)) l.

Lemma lden_lnz : forall V l, lden_l V (lnz l) = lden_l V l.
Proof.
  intros V l. induction l as [|[v c] t IH]; [reflexivity|]. cbn [lnz List.filter snd]. fold (lnz t).
  destruct (Z.eqb_spec c 0) as [->|Hc]; cbn [negb lden_l]; rewrite IH; lia.
Qed.

Fixpoint lv_eqb (l1 l2 : list (nat * Z)) : bool :=
  match l1, l2 with
  | [], [] => true
  | (v, c) :: t1, (v', c') :: t2 => Nat.eqb v v' && Z.eqb c c' && lv_eqb t1 t2
  | _, _ => false
  end.

Lemma lv_eqb_eq : forall l1 l2, lv_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|[v c] t1 IH]; intros [|[v' c'] t2] H; cbn [lv_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. subst. f_equal. apply IH. exact H3.
Qed.

(* [comment removed for export] *)
Definition zlin_eq_off (a b : zexp) (k : Z) : bool :=
  match zlin a, zlin b with
  | Some la, Some lb => lv_eqb (lnz (fst la)) (lnz (fst lb)) && Z.eqb (snd la) (snd lb + k)
  | _, _ => false
  end.

Lemma zlin_eq_off_sound : forall V a b k, zlin_eq_off a b k = true -> zv V a = zv V b + k.
Proof.
  intros V a b k H. unfold zlin_eq_off in H.
  destruct (zlin a) as [la|] eqn:Ea; [|discriminate]. destruct (zlin b) as [lb|] eqn:Eb; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply lv_eqb_eq in H1. apply Z.eqb_eq in H2.
  rewrite (zlin_sound V a la Ea), (zlin_sound V b lb Eb). unfold lden.
  rewrite <- (lden_lnz V (fst la)), <- (lden_lnz V (fst lb)), H1, H2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zdiv8 (e : zexp) : option zexp :=
  match e with
  | ZLit z => if z mod 8 =? 0 then Some (ZLit (z / 8)) else None
  | ZMul (ZLit c) x => if c mod 8 =? 0 then Some (ZMul (ZLit (c / 8)) x) else None
  | ZAdd a b => match zdiv8 a, zdiv8 b with Some a', Some b' => Some (ZAdd a' b') | _, _ => None end
  | _ => None
  end.

Lemma zdiv8_sound : forall V e e', zdiv8 e = Some e' -> zv V e = 8 * zv V e'.
Proof.
  intros V e. induction e as [z|n|a IHa b IHb|a IHa b IHb|a IHa b IHb|a IHa b IHb]; intros e' H; cbn [zdiv8] in H; try discriminate.
  - destruct (Z.eqb_spec (z mod 8) 0) as [Hz|]; [|discriminate]. injection H as <-. cbn [zv].
    pose proof (Z.div_mod z 8 ltac:(lia)). lia.
  - destruct (zdiv8 a) as [a'|]; [|discriminate]. destruct (zdiv8 b) as [b'|]; [|discriminate]. injection H as <-.
    cbn [zv]. rewrite (IHa a' eq_refl), (IHb b' eq_refl). lia.
  - destruct a as [c| | | | |]; try discriminate. destruct (Z.eqb_spec (c mod 8) 0) as [Hc|]; [|discriminate]. injection H as <-.
    cbn [zv]. pose proof (Z.div_mod c 8 ltac:(lia)). nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cover.
Variable segs : list Segment.
Variable SHOFF : Z.

Definition sh_cover1 (bn : zexp * zexp) (f : mfact) : bool :=
  match zdiv8 (fst bn) with
  | None => false
  | Some b' =>
      match f, snd bn with
      | MWr a len, ZLit nn => zlin_eq_off a b' SHOFF && (0 <=? nn) && (nn / 8 <=? len)
      | MWrS a len, n => match zdiv8 n with Some n' => zlin_eq_off a b' SHOFF && zlin_eq_off len n' 0 | None => false end
      | _, _ => false
      end
  end.

Definition sh_cover (MF : list mfact) (bn : zexp * zexp) : bool := existsb (sh_cover1 bn) MF.

Lemma sh_cover_sound : forall V m MF bn x,
  Forall (mfact_ok segs V m) MF -> sh_cover MF bn = true ->
  SHOFF + zv V (fst bn) / 8 <= x < SHOFF + (zv V (fst bn) + zv V (snd bn)) / 8 ->
  exists lo len, wr_at segs m lo len /\ lo <= x < lo + len.
Proof.
  intros V m MF [b n] x HF HC Hx. unfold sh_cover in HC. apply existsb_exists in HC as (f & Hf & HC).
  pose proof (proj1 (Forall_forall _ _) HF f Hf) as Hok. unfold sh_cover1 in HC. cbn [fst snd] in *.
  destruct (zdiv8 b) as [b'|] eqn:Eb; [|discriminate]. pose proof (zdiv8_sound V b b' Eb) as Hb.
  destruct f; try discriminate.
  - (* [comment removed for export] *) destruct n as [nn| | | | |]; try discriminate.
    apply andb_prop in HC as [HC H3]. apply andb_prop in HC as [H1 H2].
    apply (zlin_eq_off_sound V) in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. cbn [mfact_ok] in Hok. cbn [zv] in Hx.
    exists (zv V a), n0. split; [exact Hok|]. rewrite Hb in Hx.
    replace (8 * zv V b' / 8) with (zv V b') in Hx by (rewrite Z.mul_comm, Z.div_mul; lia).
    replace ((8 * zv V b' + nn) / 8) with (zv V b' + nn / 8) in Hx by (rewrite Z.mul_comm, Z.div_add_l; lia).
    lia.
  - (* [comment removed for export] *) destruct (zdiv8 n) as [n'|] eqn:En; [|discriminate]. pose proof (zdiv8_sound V n n' En) as Hn.
    apply andb_prop in HC as [H1 H2]. apply (zlin_eq_off_sound V) in H1. apply (zlin_eq_off_sound V) in H2.
    cbn [mfact_ok] in Hok. exists (zv V a), (zv V n0). split; [exact Hok|]. rewrite Hb, Hn in Hx.
    replace (8 * zv V b' / 8) with (zv V b') in Hx by (rewrite Z.mul_comm, Z.div_mul; lia).
    replace ((8 * zv V b' + 8 * zv V n') / 8) with (zv V b' + zv V n') in Hx
      by (rewrite <- Z.mul_add_distr_l, Z.mul_comm, Z.div_mul; lia).
    lia.
Qed.

End Cover.
End AHandoffSh.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import MainExport.
Import AHandoffSh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition TOP47 : Z := 0x800000000000.

Definition trim (m : word -> option byte) : word -> option byte :=
  fun x => if TOP47 <=? bv_unsigned x then None else m x.

Lemma trim_below : forall m x, bv_unsigned x < TOP47 -> trim m x = m x.
Proof. intros m x H. unfold trim. destruct (Z.leb_spec0 TOP47 (bv_unsigned x)); [lia | reflexivity]. Qed.

Lemma trim_none : forall m x, m x = None -> trim m x = None.
Proof. intros m x H. unfold trim. destruct (TOP47 <=? bv_unsigned x); [reflexivity | exact H]. Qed.

Section Trim.
Variable segs : list Segment.

Lemma wa_below : forall a, 0 <= a < TOP47 -> bv_unsigned (wa a) < TOP47.
Proof. intros a Ha. rewrite wa_unsigned; unfold TOP47 in *; lia. Qed.

Lemma bytes_at_trim : forall m a bs, bytes_at segs m a bs -> a + Z.of_nat (length bs) <= TOP47 -> bytes_at segs (trim m) a bs.
Proof.
  intros m a bs (H0 & H1 & H) Hb. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (H i Hi). unfold mrd. rewrite trim_below; [reflexivity|]. apply wa_below. lia.
Qed.

Lemma wr_at_trim : forall m a n, wr_at segs m a n -> a + n <= TOP47 -> wr_at segs (trim m) a n.
Proof.
  intros m a n (H0 & H1 & H) Hb. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (H i Hi) as Hw. unfold wview in *. rewrite trim_below; [exact Hw|]. apply wa_below. lia.
Qed.

Lemma rw_cells_trim : forall m a cs, rw_cells segs m a cs -> a + Z.of_nat (cells_size cs) <= TOP47 -> rw_cells segs (trim m) a cs.
Proof.
  intros m a cs [[Hwf Hb] Hw] Hlt. split; [split; [exact Hwf|]|].
  - apply bytes_at_trim; [exact Hb|]. destruct Hb as (_ & Hl & _). destruct Hw as (_ & _ & _).
    assert (E : length (cells_bytes cs) = cells_size cs) by (apply cells_bytes_length; exact Hwf). rewrite E. exact Hlt.
  - apply wr_at_trim; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BLl : list (nat * Z) := [(0%nat, 32768); (1%nat, 8); (2%nat, 8); (6%nat, 16); (10%nat, 4096)].
Definition BLc : Z := 184.

Lemma lden_nonneg : forall V l, (forall n, 0 <= V n) -> forallb (fun p => 0 <=? snd p) l = true -> 0 <= lden_l V l.
Proof.
  intros V l HV. induction l as [|[v c] t IH]; intros H; cbn [lden_l]; [lia|].
  cbn [forallb snd] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. specialize (IH H2). specialize (HV v). nia.
Qed.

(* [comment removed for export] *)
Definition lin_le_BL (e : zexp) : bool :=
  match zlin e with
  | Some l => forallb (fun p => 0 <=? snd p) (lmerge BLl (lscale (-1) (fst l))) && (snd l <=? BLc)
  | None => false
  end.

Lemma lin_le_BL_sound : forall V e, (forall n, 0 <= V n) -> lin_le_BL e = true -> zv V e <= lden_l V BLl + BLc.
Proof.
  intros V e HV H. unfold lin_le_BL in H. destruct (zlin e) as [l|] eqn:El; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H2.
  pose proof (lden_nonneg V _ HV H1) as Hn. rewrite lden_lmerge, lden_lscale in Hn.
  rewrite (zlin_sound V e l El). unfold lden. lia.
Qed.

(* [comment removed for export] *)
Definition end_ok (VR : vranges) (a : zexp) (hi : zexp) : bool :=
  match zbnd VR a with
  | Some (lo, _) => (0 <=? lo)
                    && (match zbnd VR hi with Some (_, h) => h <=? TOP47 | None => false end || lin_le_BL hi)
  | None => false
  end.

Definition fbelow (VR : vranges) (f : mfact) : bool :=
  match f with
  | MCell a w _ => end_ok VR a (ZAdd a (ZLit (Z.of_nat w))) && (Nat.eqb w 8 || Nat.eqb w 4 || Nat.eqb w 2 || Nat.eqb w 1)
  | MZeroC a n => end_ok VR a (ZAdd a (ZLit n)) && (0 <=? n)
  | MRo a w _ => end_ok VR a (ZAdd a (ZLit (Z.of_nat w))) && (Nat.leb w 8)
  | MZero a n => end_ok VR a (ZAdd a (ZLit n))
  | MFill a n _ => end_ok VR a (ZAdd a (ZLit n))
  | MImg _ _ => true
  | MWr a n => end_ok VR a (ZAdd a (ZLit n))
  | MZeroS a n => end_ok VR a (ZAdd a n)
  | MWrS a n => end_ok VR a (ZAdd a n)
  end.

Section Sound.
Variable V : nat -> Z.
Variable VR : vranges.
Hypothesis HVR : vr_sound V VR.
Hypothesis HV0 : forall n, 0 <= V n.
Hypothesis HBL : lden_l V BLl + BLc <= TOP47.

Lemma end_ok_sound : forall a hi, end_ok VR a hi = true -> 0 <= zv V a /\ zv V hi <= TOP47.
Proof.
  intros a hi H. unfold end_ok in H. destruct (zbnd VR a) as [[lo h0]|] eqn:Ea; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  pose proof (zbnd_sound V VR a lo h0 HVR Ea) as Ba. split; [lia|].
  apply orb_prop in H2 as [H2|H2].
  - destruct (zbnd VR hi) as [[l2 h2]|] eqn:Eh; [|discriminate]. apply Z.leb_le in H2.
    pose proof (zbnd_sound V VR hi l2 h2 HVR Eh). lia.
  - pose proof (lin_le_BL_sound V hi HV0 H2). lia.
Qed.

Lemma word_le_len : forall w v, (w <= 8)%nat -> length (word_to_le_bytes w v) = w.
Proof. intros w v Hw. do 9 (destruct w as [|w]; [reflexivity|]). lia. Qed.

Theorem mfact_trim : forall m f, mfact_ok segs V m f -> fbelow VR f = true -> mfact_ok segs V (trim m) f.
Proof.
  intros m f H Hb. destruct f; cbn [mfact_ok fbelow] in *.
  - (* [comment removed for export] *) apply andb_prop in Hb as [Hb Hw]. destruct (end_ok_sound _ _ Hb) as [A0 A1]. cbn [zv] in A1.
    apply rw_cells_trim; [exact H|].
    assert (Es : Z.of_nat (cells_size [cellw w (zv V v)]) = Z.of_nat w).
    { repeat (apply orb_prop in Hw as [Hw|Hw]); apply Nat.eqb_eq in Hw; subst w; reflexivity. }
    rewrite Es. exact A1.
  - (* [comment removed for export] *) apply andb_prop in Hb as [Hb Hn]. apply Z.leb_le in Hn. destruct (end_ok_sound _ _ Hb) as [A0 A1]. cbn [zv] in A1.
    apply rw_cells_trim; [exact H|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact A1.
  - (* [comment removed for export] *) apply andb_prop in Hb as [Hb Hw]. apply Nat.leb_le in Hw. destruct (end_ok_sound _ _ Hb) as [A0 A1]. cbn [zv] in A1.
    apply bytes_at_trim; [exact H|]. rewrite word_le_len by exact Hw. exact A1.
  - (* [comment removed for export] *) destruct (end_ok_sound _ _ Hb) as [A0 A1]. cbn [zv] in A1. intros i Hi.
    rewrite trim_below; [exact (H i Hi)|]. apply wa_below. lia.
  - (* [comment removed for export] *) destruct (end_ok_sound _ _ Hb) as [A0 A1]. cbn [zv] in A1. intros i Hi.
    rewrite trim_below; [exact (H i Hi)|]. apply wa_below. lia.
  - (* [comment removed for export] *) intros i Hi. apply trim_none. exact (H i Hi).
  - (* [comment removed for export] *) destruct (end_ok_sound _ _ Hb) as [A0 A1]. cbn [zv] in A1. apply wr_at_trim; assumption.
  - (* [comment removed for export] *) destruct (end_ok_sound _ _ Hb) as [A0 A1]. cbn [zv] in A1. intros i Hi.
    rewrite trim_below; [exact (H i Hi)|]. apply wa_below. lia.
  - (* [comment removed for export] *) destruct (end_ok_sound _ _ Hb) as [A0 A1]. cbn [zv] in A1. apply wr_at_trim; assumption.
Qed.

Corollary mfacts_trim : forall m l, Forall (mfact_ok segs V m) l -> forallb (fbelow VR) l = true -> Forall (mfact_ok segs V (trim m)) l.
Proof.
  intros m l H Hb. apply Forall_forall. intros f Hf.
  apply mfact_trim; [exact (proj1 (Forall_forall _ _) H f Hf) | exact (proj1 (forallb_forall _ _) Hb f Hf)].
Qed.

End Sound.
End Trim.
