(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module AX2 := AS.AxSymExec3.AX2.
Module AX2S := AS.AxSymExec3Sound.AX2S.

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition zb (z : Z) : byte := Z_to_bv 8 z.

Inductive rtfact : Type :=
| RW8 (a v : Z) | RW4 (a v : Z) | RW2 (a v : Z) | RW1 (a v : Z)
| RZero (a n : Z) | RFill (a n c : Z) | RDef (a n : Z)
| RWr (lo hi : Z) | RImg (lo hi : Z).

Definition zfill (m : word -> option byte) (a n : Z) : Prop :=
  0 <= a /\ a + n <= 2^64 /\ forall i, 0 <= i < n -> m (wa (a + i)) = Some (zb 0).
Definition bfill (m : word -> option byte) (a n c : Z) : Prop :=
  0 <= a /\ a + n <= 2^64 /\ forall i, 0 <= i < n -> m (wa (a + i)) = Some (zb c).
Definition dfill (m : word -> option byte) (a n : Z) : Prop :=
  0 <= a /\ a + n <= 2^64 /\ forall i, 0 <= i < n -> m (wa (a + i)) <> None.
Definition pristine (m : word -> option byte) (lo hi : Z) : Prop :=
  forall x, lo <= x < hi -> m (wa x) = None.

Section WithSegs.
Variable segs : list Segment.

Definition rtfact_ok (m : word -> option byte) (f : rtfact) : Prop :=
  match f with
  | RW8 a v => cells_at segs m a [C8 (wz v)]
  | RW4 a v => cells_at segs m a [C4 (wz v)]
  | RW2 a v => cells_at segs m a [C2 (wz v)]
  | RW1 a v => cells_at segs m a [C1 (zb v)]
  | RZero a n => zfill m a n
  | RFill a n c => bfill m a n c
  | RDef a n => dfill m a n
  | RWr lo hi => wr_at segs m lo (hi - lo)
  | RImg lo hi => 0x0 <= lo /\ hi <= 2^64 /\ (forall x : word, lo <= bv_unsigned x < hi -> ~ noseg segs x) /\ pristine m lo hi
  end.

(* [comment removed for export] *)
Lemma rtfacts_get : forall m l f, Forall (rtfact_ok m) l -> In f l -> rtfact_ok m f.
Proof. intros m l f H Hin. exact (proj1 (Forall_forall _ _) H f Hin). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition magrees (m m' : word -> option byte) : Prop :=
  forall x, m x <> None \/ ~ noseg segs x -> m' x = m x.

Lemma mrd_agrees : forall m m' x b, magrees m m' -> mrd segs m x = Some b -> mrd segs m' x = Some b.
Proof.
  intros m m' x b HA H. unfold mrd in *. destruct (m x) eqn:E.
  - rewrite (HA x ltac:(left; congruence)). rewrite E. exact H.
  - assert (Hs : ~ noseg segs x) by (intros Hn; rewrite (seg_rom_noseg segs x Hn) in H; discriminate).
    rewrite (HA x (or_intror Hs)), E. exact H.
Qed.

Lemma bytes_at_agrees : forall m m' a bs, magrees m m' -> bytes_at segs m a bs -> bytes_at segs m' a bs.
Proof.
  intros m m' a bs HA nelH_; (nelim nelH_ 3%nat; intros H0 H1 H). split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (H i Hi) as Hb. destruct (nth_error bs i) eqn:E; [| apply nth_error_None in E; lia].
  eapply mrd_agrees; eassumption.
Qed.

Lemma wview_agrees : forall m m' x, magrees m m' -> wview segs m x <> None -> wview segs m' x <> None.
Proof.
  intros m m' x HA H. unfold wview in *. destruct (m x) eqn:E.
  - rewrite (HA x ltac:(left; congruence)), E. discriminate.
  - destruct (m' x); [discriminate| exact H].
Qed.

Lemma rtfact_transfer : forall m m' f, magrees m m' -> rtfact_ok m f -> rtfact_ok m' f.
Proof.
  intros m m' f HA H. destruct f; cbn [rtfact_ok] in *.
  - destruct H as [Hw Hb]. split; [exact Hw| eapply bytes_at_agrees; eassumption].
  - destruct H as [Hw Hb]. split; [exact Hw| eapply bytes_at_agrees; eassumption].
  - destruct H as [Hw Hb]. split; [exact Hw| eapply bytes_at_agrees; eassumption].
  - destruct H as [Hw Hb]. split; [exact Hw| eapply bytes_at_agrees; eassumption].
  - (nelim H 3%nat; intros H0 H1 H). split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite (HA _ ltac:(left; rewrite (H i Hi); discriminate)). apply H. exact Hi.
  - (nelim H 3%nat; intros H0 H1 H). split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite (HA _ ltac:(left; rewrite (H i Hi); discriminate)). apply H. exact Hi.
  - (nelim H 3%nat; intros H0 H1 H). split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite (HA _ ltac:(left; apply H; exact Hi)). apply H. exact Hi.
  - (nelim H 3%nat; intros H0 H1 H). split; [exact H0|]. split; [exact H1|]. intros a Ha. eapply wview_agrees; [eassumption| apply H; exact Ha].
  - (nelim H 4%nat; intros H0 H1 Hs H). split; [exact H0|]. split; [exact H1|]. split; [exact Hs|]. intros x Hx.
    rewrite (HA (wa x)); [apply H; exact Hx|]. right. apply Hs. rewrite wa_unsigned by lia. exact Hx.
Qed.

Lemma rtfacts_transfer : forall m m' l, magrees m m' -> Forall (rtfact_ok m) l -> Forall (rtfact_ok m') l.
Proof. intros m m' l HA H. eapply Forall_impl; [| exact H]. intros f. apply rtfact_transfer. exact HA. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_bytes_at : forall n m a bs, 0 <= a -> a + Z.of_nat n <= 2^64 ->
  rdn segs m (wa a) n = Some bs -> bytes_at segs m a bs.
Proof.
  induction n as [|n IH]; intros m a bs Ha Hn H.
  - cbn in H. injection H as <-. apply bytes_at_nil. lia.
  - rewrite rdn_unfold in H. destruct (mrd segs m (wa a)) as [b|] eqn:Eb; [| discriminate].
    rewrite wa_succ in H. destruct (rdn segs m (wa (a + 1)) n) as [r|] eqn:Er; [| discriminate]. injection H as <-.
    (nelimp (IH m (a + 1) r ltac:(lia) ltac:(lia) Er) 3%nat; intros R0 R1 R).
    split; [lia|]. split; [cbn [length]; lia|]. intros [|i] Hi.
    + cbn. rewrite Z.add_0_r. exact Eb.
    + cbn [nth_error]. rewrite <- (R i) by (cbn [length] in Hi; lia). f_equal. f_equal. lia.
Qed.

Lemma Qrdn_rdn : forall m a n, AS.PropExec.rdn segs m a n = rdn segs m a n.
Proof. reflexivity. Qed.

Section K.
Variable E : AX2.env.
Variable M : word -> option byte.
Local Notation uE e := (bv_unsigned (AX2.edenot E e)).

(* [comment removed for export] *)
Definition jaddr (sa : AX2.saddr) (A : Z) : Prop := uE (AX2.a_base sa) + AX2.a_off sa = A.
Definition jval (e : AX2.expr) (v : Z) : Prop := uE e = v.

Lemma estart_jaddr : forall sa A, jaddr sa A -> AX2S.estart E sa = A.
Proof. intros sa A H. exact H. Qed.

Lemma adenot_wa : forall sa A n, AX2S.flat E sa n -> jaddr sa A -> AX2.adenot E sa = wa A.
Proof.
  intros sa A n Hf Ha. apply bv_eq. rewrite (AX2S.flat_u E sa n Hf). rewrite (estart_jaddr sa A Ha).
  (nelim Hf 4%nat; intros F1 F2 F3 F4). rewrite (estart_jaddr sa A Ha) in *. rewrite wa_unsigned by lia. reflexivity.
Qed.

Lemma edenot_wz : forall e v, jval e v -> AX2.edenot E e = wz v.
Proof. intros e v H. apply bv_eq. unfold jval in H. unfold wz. pose proof (bv_unsigned_in_range 64 (AX2.edenot E e)). rewrite unsigned_lit by (change (bv_modulus 64) with (2^64) in *; lia). exact H. Qed.

Lemma jword : forall sa w ve A v, AX2S.kentry_ok segs E M (AX2.KWord sa w ve) -> jaddr sa A -> jval ve v ->
  bytes_at segs M A (word_to_le_bytes w (wz v)) /\ 0 <= A /\ A + Z.of_nat w <= 2^64.
Proof.
  intros sa w ve A v (Hw & Hf & Hr) Ha Hv. rewrite (adenot_wa sa A _ Hf Ha), Qrdn_rdn, (edenot_wz ve v Hv) in Hr.
  (nelimp Hf 4%nat; intros F1 F2 F3 F4). rewrite (estart_jaddr sa A Ha) in *.
  split; [apply (rdn_bytes_at w); [lia| lia| exact Hr]| lia].
Qed.

Lemma jw8 : forall sa ve A v, AX2S.kentry_ok segs E M (AX2.KWord sa 8 ve) -> jaddr sa A -> jval ve v -> rtfact_ok M (RW8 A v).
Proof. intros sa ve A v HK Ha Hv. destruct (jword _ _ _ _ _ HK Ha Hv) as [Hb _]. split; [exact (conj I I)| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]. Qed.

Lemma jw4 : forall sa ve A v, AX2S.kentry_ok segs E M (AX2.KWord sa 4 ve) -> jaddr sa A -> jval ve v -> rtfact_ok M (RW4 A v).
Proof. intros sa ve A v HK Ha Hv. destruct (jword _ _ _ _ _ HK Ha Hv) as [Hb _]. split; [exact (conj I I)| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]. Qed.

Lemma jw2 : forall sa ve A v, AX2S.kentry_ok segs E M (AX2.KWord sa 2 ve) -> jaddr sa A -> jval ve v -> rtfact_ok M (RW2 A v).
Proof. intros sa ve A v HK Ha Hv. destruct (jword _ _ _ _ _ HK Ha Hv) as [Hb _]. split; [exact (conj I I)| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]. Qed.

Lemma jw1 : forall sa ve A v, AX2S.kentry_ok segs E M (AX2.KWord sa 1 ve) -> jaddr sa A -> jval ve v -> rtfact_ok M (RW1 A v).
Proof.
  intros sa ve A v HK Ha Hv. destruct (jword _ _ _ _ _ HK Ha Hv) as [Hb _]. split; [exact (conj I I)|].
  cbn [cells_bytes cbytes app]. eapply bytes_at_ext; [exact Hb|].
  unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. unfold zb, wz. apply Z_to_bv8_mod.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). apply mod_mod8_of_modw. lia.
Qed.

(* [comment removed for export] *)
Lemma jw0k : forall sa w ve A k, AX2S.kentry_ok segs E M (AX2.KWord sa w ve) -> jaddr sa A -> jval ve 0 ->
  (k < w)%nat -> rtfact_ok M (RW1 (A + Z.of_nat k) 0).
Proof.
  intros sa w ve A k HK Ha Hv Hk. destruct (jword _ _ _ _ _ HK Ha Hv) as [Hb _]. split; [exact (conj I I)|].
  cbn [cells_bytes cbytes app]. (nelim Hb 3%nat; intros B0 B1 B). unfold word_to_le_bytes in B1, B. rewrite length_Z_to_le_bytes in B1, B.
  split; [lia|]. split; [cbn [length]; lia|]. intros [|i] Hi; [| cbn in Hi; lia].
  cbn [nth_error]. rewrite Z.add_0_r. rewrite (B k Hk).
  assert (G : forall n j z, (j < n)%nat -> nth_error (Z_to_le_bytes n 0) j = Some (zb z) -> nth_error (Z_to_le_bytes n 0) j = Some (zb 0)).
  { intros n. induction n as [|n IH]; intros j z Hj H; [cbn in Hj; lia|]. destruct j; cbn [Z_to_le_bytes nth_error] in *; [reflexivity|]. cbn in H |- *. eapply IH; [lia| exact H]. }
  assert (G2 : forall n j, (j < n)%nat -> nth_error (Z_to_le_bytes n 0) j = Some (zb 0)).
  { intros n. induction n as [|n IH]; intros j Hj; [lia|]. destruct j; cbn [Z_to_le_bytes nth_error]; [reflexivity|]. cbn. apply IH. lia. }
  unfold wz. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. apply G2. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma jwn : forall sa w ve A v, AX2S.kentry_ok segs E M (AX2.KWord sa w ve) -> jaddr sa A -> jval ve v ->
  bytes_at segs M A (Z_to_le_bytes w v).
Proof.
  intros sa w ve A v HK Ha Hv. destruct (jword _ _ _ _ _ HK Ha Hv) as [Hb _].
  unfold word_to_le_bytes in Hb. unfold wz in Hb. pose proof (bv_unsigned_in_range 64 (AX2.edenot E ve)) as R.
  unfold jval in Hv. rewrite unsigned_lit in Hb by (change (bv_modulus 64) with (2^64) in R; lia). exact Hb.
Qed.

Lemma jzero : forall sa ne A n, AX2S.kentry_ok segs E M (AX2.KZero sa ne) -> jaddr sa A -> jval ne n -> rtfact_ok M (RZero A n).
Proof.
  intros sa ne A n [(F1 & F2 & F3 & F4) H] Ha Hn. unfold AX2S.elenZ in *. unfold jval in Hn. rewrite Hn in *. rewrite (estart_jaddr sa A Ha) in *. split; [lia|]. split; [lia|]. intros i Hi. unfold wa. apply H. exact Hi.
Qed.

Lemma jfill : forall sa ne c A n, AX2S.kentry_ok segs E M (AX2.KFill sa ne c) -> jaddr sa A -> jval ne n -> rtfact_ok M (RFill A n c).
Proof.
  intros sa ne c A n [(F1 & F2 & F3 & F4) H] Ha Hn. unfold AX2S.elenZ in *. unfold jval in Hn. rewrite Hn in *. rewrite (estart_jaddr sa A Ha) in *. split; [lia|]. split; [lia|]. intros i Hi. unfold wa. apply H. exact Hi.
Qed.

Lemma junk : forall sa ne A n, AX2S.kentry_ok segs E M (AX2.KUnk sa ne) -> jaddr sa A -> jval ne n -> rtfact_ok M (RDef A n).
Proof.
  intros sa ne A n [(F1 & F2 & F3 & F4) H] Ha Hn. unfold AX2S.elenZ in *. unfold jval in Hn. rewrite Hn in *. rewrite (estart_jaddr sa A Ha) in *. split; [lia|]. split; [lia|]. intros i Hi. unfold wa. apply H. exact Hi.
Qed.

Lemma jwr : forall sa ne A n, AX2S.kentry_ok segs E M (AX2.KWr sa ne) -> jaddr sa A -> jval ne n -> rtfact_ok M (RWr A (A + n)).
Proof.
  intros sa ne A n [(F1 & F2 & F3 & F4) H] Ha Hn. unfold AX2S.elenZ in *. unfold jval in Hn. rewrite Hn in *. rewrite (estart_jaddr sa A Ha) in *.
  cbn [rtfact_ok]. replace (A + n - A) with n by lia. split; [lia|]. split; [lia|]. intros i Hi.
  pose proof (H i 1%nat ltac:(lia) ltac:(cbn; lia)) as Hs.
  cbn [store_ok] in Hs. unfold wa. destruct (wview segs M (Z_to_bv 64 (A + i))); [discriminate| discriminate Hs].
Qed.

Lemma jimg : forall lo hi, AX2S.kentry_ok segs E M (AX2.KImg lo hi) ->
  (forall x : word, lo <= bv_unsigned x < hi -> ~ noseg segs x) -> rtfact_ok M (RImg lo hi).
Proof.
  intros lo hi (H0 & H1 & H) Hs. split; [exact H0|]. split; [exact H1|]. split; [exact Hs|]. intros x Hx. unfold wa. apply H. exact Hx.
Qed.

(* [comment removed for export] *)
Fixpoint plen (p : positive) : nat := match p with xH => 1%nat | xO q => S (plen q) | xI q => S (plen q) end.
Definition lit_ok (z : Z) : bool := match z with Z0 => true | Zpos p => Nat.leb (plen p) 64 | Zneg _ => false end.

Lemma plen_bound : forall p, Z.pos p < 2 ^ Z.of_nat (plen p).
Proof.
  induction p as [q IH | q IH |]; cbn [plen]; rewrite ?Nat2Z.inj_succ, ?Z.pow_succ_r by lia.
  - rewrite Pos2Z.inj_xI. lia.
  - rewrite Pos2Z.inj_xO. lia.
  - cbn. lia.
Qed.

Lemma lit_ok_sound : forall z, lit_ok z = true -> 0 <= z < 2^64.
Proof.
  intros z H. destruct z as [|p|p]; cbn [lit_ok] in H; [lia| | discriminate].
  apply Nat.leb_le in H. pose proof (plen_bound p). assert (2 ^ Z.of_nat (plen p) <= 2^64) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Definition leafv (e : AX2.expr) : option Z :=
  match e with
  | AX2.ELit z => if lit_ok z then Some z else None
  | AX2.EVar i => Some (bv_unsigned (AX2.ev E i))
  | _ => None
  end.

Fixpoint zev (e : AX2.expr) : option Z :=
  match e with
  | AX2.ELit z => Some z
  | AX2.EVar i => Some (bv_unsigned (AX2.ev E i))
  | AX2.EAlu Instr.ALU_ADD a b => match zev a, zev b with Some x, Some y => Some (x + y) | _, _ => None end
  | AX2.EAlu Instr.ALU_SUB a b => match zev a, zev b with Some x, Some y => Some (x - y) | _, _ => None end
  | AX2.EMd Instr.M_MUL a b => match zev a, zev b with Some x, Some y => Some (x * y) | _, _ => None end
  | AX2.EAlu Instr.ALU_SLTU a b => match leafv a, leafv b with Some x, Some y => Some (if x <? y then 1 else 0) | _, _ => None end
  | AX2.EAlu Instr.ALU_AND a b =>
      match leafv a, leafv b with
      | Some x, Some y => Some (Z.land x y)
      | _, _ => match zev a, zev b with Some x, Some y => Some (Z.land (x mod 2^64) (y mod 2^64)) | _, _ => None end
      end
  | _ => None
  end.

Lemma leafv_sound : forall e z, leafv e = Some z -> bv_unsigned (AX2.edenot E e) = z /\ 0 <= z < 2^64.
Proof.
  intros e z H. destruct e; cbn [leafv] in H; try discriminate.
  - destruct (lit_ok z0) eqn:El; [| discriminate]. apply lit_ok_sound in El.
    injection H as <-. cbn [AX2.edenot]. rewrite unsigned_lit by lia. lia.
  - injection H as <-. cbn [AX2.edenot]. pose proof (bv_unsigned_in_range 64 (AX2.ev E n)) as R. change (bv_modulus 64) with (2^64) in R. lia.
Qed.

Lemma zev_sound : forall e z, zev e = Some z -> bv_unsigned (AX2.edenot E e) = z mod 2^64.
Proof.
  induction e as [z0 | n | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb | sx lo n a IHa | sx k i n]; intros z H;
    cbn [zev] in H; try discriminate.
  - injection H as <-. cbn [AX2.edenot]. rewrite AX2S.u_lit64, AX2S.two64_eq. reflexivity.
  - injection H as <-. cbn [AX2.edenot]. pose proof (bv_unsigned_in_range 64 (AX2.ev E n)) as R. change (bv_modulus 64) with (2^64) in R.
    rewrite Z.mod_small by lia. reflexivity.
  - destruct op; try discriminate.
    + destruct (zev a) as [x|] eqn:Ea; [| discriminate]. destruct (zev b) as [y|] eqn:Eb; [| discriminate]. injection H as <-.
      cbn [AX2.edenot]. rewrite AX2S.u_add64, (IHa x eq_refl), (IHb y eq_refl). rewrite <- Zplus_mod. reflexivity.
    + destruct (zev a) as [x|] eqn:Ea; [| discriminate]. destruct (zev b) as [y|] eqn:Eb; [| discriminate]. injection H as <-.
      cbn [AX2.edenot]. rewrite AX2S.u_sub64, (IHa x eq_refl), (IHb y eq_refl). rewrite <- Zminus_mod. reflexivity.
    + destruct (leafv a) as [x|] eqn:Ea; [| discriminate]. destruct (leafv b) as [y|] eqn:Eb; [| discriminate]. injection H as <-.
      destruct (leafv_sound a x Ea) as [Ha Ra]. destruct (leafv_sound b y Eb) as [Hb Rb].
      cbn [AX2.edenot]. rewrite AX2S.u_sltu64, Ha, Hb. rewrite Z.mod_small; [reflexivity|]. destruct (x <? y); lia.
    + assert (G : forall x y, zev a = Some x -> zev b = Some y ->
                 bv_unsigned (AX2.edenot E (AX2.EAlu Instr.ALU_AND a b)) = (Z.land (x mod 2^64) (y mod 2^64)) mod 2^64).
      { intros x' y' Ea Eb. cbn [AX2.edenot]. rewrite AX2S.u_and64, (IHa x' Ea), (IHb y' Eb). rewrite (Z.mod_small (Z.land _ _)); [reflexivity|].
        pose proof (Z.mod_pos_bound x' (2^64) ltac:(lia)). pose proof (Z.mod_pos_bound y' (2^64) ltac:(lia)).
        apply AS.PropExec.Z_land_range; lia. }
      destruct (leafv a) as [x|] eqn:Ea.
      * destruct (leafv b) as [y|] eqn:Eb.
        -- injection H as <-. destruct (leafv_sound a x Ea) as [Ha Ra]. destruct (leafv_sound b y Eb) as [Hb Rb].
           cbn [AX2.edenot]. rewrite AX2S.u_and64, Ha, Hb. rewrite Z.mod_small; [reflexivity|].
           apply AS.PropExec.Z_land_range; lia.
        -- destruct (zev a) as [x'|]; [| discriminate]. destruct (zev b) as [y'|]; [| discriminate]. injection H as <-. apply G; reflexivity.
      * destruct (zev a) as [x'|]; [| discriminate]. destruct (zev b) as [y'|]; [| discriminate]. injection H as <-. apply G; reflexivity.
  - destruct op; try discriminate.
    destruct (zev a) as [x|] eqn:Ea; [| discriminate]. destruct (zev b) as [y|] eqn:Eb; [| discriminate]. injection H as <-.
    cbn [AX2.edenot]. rewrite AX2S.u_mul64, (IHa x eq_refl), (IHb y eq_refl). rewrite <- Zmult_mod. reflexivity.
Qed.

Lemma jval_zev : forall e z v, zev e = Some z -> 0 <= z < 2^64 -> z = v -> jval e v.
Proof. intros e z v Hz Hr ->. unfold jval. rewrite (zev_sound e v Hz). apply Z.mod_small. exact Hr. Qed.

Lemma jvalm_zev : forall e z v, zev e = Some z -> z = v -> bv_unsigned (AX2.edenot E e) = v mod 2^64.
Proof. intros e z v Hz ->. apply zev_sound. exact Hz. Qed.

Lemma jaddr_zev : forall sa z A, zev (AX2.a_base sa) = Some z -> 0 <= z < 2^64 -> z + AX2.a_off sa = A -> jaddr sa A.
Proof. intros sa z A Hz Hr HA. unfold jaddr. rewrite (zev_sound _ z Hz), Z.mod_small by exact Hr. exact HA. Qed.

(* [comment removed for export] *)
Lemma jrange : forall e lo hi v, AX2S.kentry_ok segs E M (AX2.KRange e lo hi) -> jval e v -> lo <= v <= hi.
Proof. intros e lo hi v [H1 H2] Hv. unfold jval in Hv. rewrite Hv in *. lia. Qed.

(* [comment removed for export] *)
Lemma jrange_wrap : forall e lo hi z, AX2S.kentry_ok segs E M (AX2.KRange e lo hi) ->
  bv_unsigned (AX2.edenot E e) = z mod 2^64 -> hi - 2^64 < z < 2^64 -> lo <= z <= hi.
Proof.
  intros e lo hi z [H1 H2] Hz Hr. rewrite Hz in *.
  destruct (Z.lt_ge_cases z 0).
  - rewrite <- (Z.mod_add z 1 (2^64)) in H1, H2 by lia. rewrite Z.mod_small in H1, H2 by lia. lia.
  - rewrite Z.mod_small in H1, H2 by lia. lia.
Qed.

Lemma jalign : forall e k v, AX2S.kentry_ok segs E M (AX2.KAlign e k) -> jval e v -> v mod k = 0.
Proof. intros e k v [H1 H2] Hv. unfold jval in Hv. rewrite Hv in *. exact H2. Qed.

Lemma jdisj : forall a1 n1 a2 n2 A1 N1 A2 N2, AX2S.kentry_ok segs E M (AX2.KDisj a1 n1 a2 n2) ->
  jaddr a1 A1 -> jval n1 N1 -> jaddr a2 A2 -> jval n2 N2 -> A1 + N1 <= A2 \/ A2 + N2 <= A1.
Proof.
  intros a1 n1 a2 n2 A1 N1 A2 N2 H Ha1 Hn1 Ha2 Hn2. cbn [AX2S.kentry_ok] in H. unfold AX2S.elenZ in H.
  unfold jval in *. rewrite (estart_jaddr a1 A1 Ha1), (estart_jaddr a2 A2 Ha2), Hn1, Hn2 in H. exact H.
Qed.
End K.
End WithSegs.
