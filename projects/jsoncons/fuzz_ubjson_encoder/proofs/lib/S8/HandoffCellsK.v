(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec AgentLib MemSplit AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK HandoffBridgeK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition chk_word (k : list kentry) (b : expr) (off : Z) (w : nat) (v : expr) : bool :=
  match kfind_word k b off w with Some v' => expr_eqb v' v | None => false end.

Definition covers (b : expr) (off n : Z) (a : saddr) (len : expr) : bool :=
  match len with
  | ELit L => (expr_eqb (a_base a) b && Z.leb (a_off a) off && Z.leb (off + n) (a_off a + L) && Z.leb 0 n && Z.ltb L (2 ^ 64))%bool
  | _ => false
  end.
Definition chk_zero (k : list kentry) (b : expr) (off n : Z) : bool :=
  existsb (fun K => match K with KZero a len => covers b off n a len | _ => false end) k.
Definition chk_wr (k : list kentry) (b : expr) (off n : Z) : bool :=
  existsb (fun K => match K with KWr a len => covers b off n a len | _ => false end) k.

Definition bytes_eqb (x y : list byte) : bool :=
  (Nat.eqb (length x) (length y) && forallb (fun p => Z.eqb (bv_unsigned (fst p)) (bv_unsigned (snd p))) (combine x y))%bool.
Lemma bytes_eqb_eq : forall x y, bytes_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; try reflexivity; unfold bytes_eqb in H; cbn in H; try discriminate.
  apply andb_prop in H as [H1 H2]. apply andb_prop in H2 as [H2 H3]. apply Z.eqb_eq in H2. apply bv_eq in H2. subst b. f_equal.
  apply IH. unfold bytes_eqb. rewrite H1, H3. reflexivity.
Qed.

Section Cells.
Variable SEGS : list Segment.
Variable A : atable.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.

#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).

Definition chk_img (k : list kentry) (a : Z) (w : nat) (v : Z) : bool :=
  match kfind_img k a with
  | Some (lo, hi) =>
      (Z.leb lo a && Z.leb (a + Z.of_nat w) hi && Z.leb (img_lo A) a && Z.leb (a + Z.of_nat w) (img_hi A) && Z.leb 0 a && Z.ltb (a + Z.of_nat w) (2 ^ 64)
       && match rdn SEGS (fun _ => None) (Z_to_bv 64 a) w with
          | Some bs => bytes_eqb bs (word_to_le_bytes w (Z_to_bv 64 v))
          | None => false
          end)%bool
  | None => false
  end.

Lemma hc_word : forall E cs R FULL model b off w v,
  CSOK E cs R FULL model -> chk_word (kn cs) b off w v = true ->
  flat E (SA b off) (Z.of_nat w)
  /\ rdn SEGS FULL (Z_to_bv 64 (uE E b + off)) w = Some (word_to_le_bytes w (Z_to_bv 64 (uE E v))).
Proof.
  intros E cs R FULL model b off w v HC H. unfold chk_word in H.
  destruct (kfind_word (kn cs) b off w) as [v'|] eqn:Hk; [|discriminate]. apply expr_eqb_eq in H. subst v'.
  destruct (hb_word_at SEGS A LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E cs R FULL model b off w v HC Hk) as (_ & Hf & Hr & _).
  split; [exact Hf|].
  pose proof (flat_u E _ _ Hf) as Hu. unfold estart in Hu; cbn [a_base a_off] in Hu.
  unfold uE. rewrite <- Hu, !Z_to_bv_bv_unsigned. exact Hr.
Qed.

Lemma covers_sound : forall E b off n a len, covers b off n a len = true -> flat E a (elenZ E len) ->
  exists L, elenZ E len = L /\ a_base a = b /\ a_off a <= off /\ off + n <= a_off a + L /\ 0 <= n.
Proof.
  intros E b off n a len H Hf. unfold covers in H. destruct len as [L|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?]; try discriminate.
  repeat (apply andb_prop in H as [H ?]). apply expr_eqb_eq in H.
  repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in X end.
  exists L. unfold elenZ. cbn [edenot]. destruct Hf as (_ & _ & F3 & _). unfold elenZ in F3. cbn [edenot] in F3.
  rewrite u64_lit by (pose proof (u64_range (Z_to_bv 64 L)); split; [|assumption]; destruct (Z_lt_dec L 0); [|lia];
                      exfalso; lia).
  repeat split; assumption || lia.
Qed.

Lemma hc_zero : forall E cs R FULL model b off n,
  CSOK E cs R FULL model -> chk_zero (kn cs) b off n = true ->
  0 <= uE E b + off /\ uE E b + off + n <= 2 ^ 64
  /\ forall i, 0 <= i < n -> FULL (Z_to_bv 64 (uE E b + off + i)) = Some (Z_to_bv 8 0).
Proof.
  intros E cs R FULL model b off n HC H. unfold chk_zero in H. apply existsb_exists in H as (K & Hin & Hc).
  destruct K as [| a len | | | | | | | |]; try discriminate.
  destruct (hb_zero_k SEGS A LIMIT SINV argH FS0 E cs R FULL model a len HC Hin) as [Hf Hz].
  destruct (covers_sound E b off n a len Hc Hf) as (L & HL & Hb & H1 & H2 & H3).
  destruct Hf as (F1 & F2 & F3 & F4). unfold estart in *. rewrite Hb in *. rewrite HL in *. unfold uE.
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E b) + a_off a + (off - a_off a + i)) by ring.
  apply Hz. lia.
Qed.

Lemma wleb_zero : forall w, (w <= 8)%nat -> word_to_le_bytes w (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) w.
Proof.
  intros w Hw. do 9 (destruct w as [|w]; [vm_compute; repeat f_equal; apply bv_eq; reflexivity|]). lia.
Qed.

Lemma hc_zero_cell : forall E cs R FULL model b off n,
  CSOK E cs R FULL model -> chk_zero (kn cs) b off n = true ->
  forall a (w : nat), (w <= 8)%nat -> uE E b + off <= a -> a + Z.of_nat w <= uE E b + off + n ->
    rdn SEGS FULL (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 0)).
Proof.
  intros E cs R FULL model b off n HC H a w Hw Ha1 Ha2.
  destruct (hc_zero E cs R FULL model b off n HC H) as (Z1 & Z2 & Hz).
  rewrite (wleb_zero w Hw). destruct w as [|w']; [reflexivity|]. apply rdn_const.
  - rewrite u64_lit by lia. lia.
  - intros x Hx. rewrite u64_lit in Hx by lia.
    replace x with (Z_to_bv 64 (uE E b + off + (bv_unsigned x - (uE E b + off)))).
    + apply Hz. lia.
    + replace (uE E b + off + (bv_unsigned x - (uE E b + off))) with (bv_unsigned x) by ring. apply Z_to_bv_bv_unsigned.
Qed.

Lemma hc_wr : forall E cs R FULL model b off n,
  CSOK E cs R FULL model -> chk_wr (kn cs) b off n = true ->
  forall d (m : nat), 0 <= d -> d + Z.of_nat m <= n -> store_ok SEGS FULL (Z_to_bv 64 (uE E b + off + d)) m = true.
Proof.
  intros E cs R FULL model b off n HC H d m Hd Hm. unfold chk_wr in H. apply existsb_exists in H as (K & Hin & Hc).
  destruct K as [| | | | | | a len | | |]; try discriminate.
  pose proof (hb_kn SEGS A LIMIT SINV argH FS0 E cs R FULL model _ HC Hin) as HK. cbn [kentry_ok] in HK. destruct HK as [Hf HW].
  destruct (covers_sound E b off n a len Hc Hf) as (L & HL & Hb & H1 & H2 & H3).
  unfold estart in *. rewrite Hb in *. rewrite HL in *.
  pose proof (HW (off - a_off a + d) m ltac:(lia) ltac:(lia)) as Hs.
  replace (bv_unsigned (edenot E b) + a_off a + (off - a_off a + d)) with (uE E b + off + d) in Hs by (unfold uE; ring).
  exact (proj1 (hb_mr_store_ok SEGS A argH SEGS_in_hull HULL_ok argH_high E cs model FULL _ m Hs)).
Qed.

Lemma hc_img : forall E cs R FULL model a w v,
  CSOK E cs R FULL model -> chk_img (kn cs) a w v = true ->
  rdn SEGS FULL (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)).
Proof.
  intros E cs R FULL model a w v HC H. unfold chk_img in H.
  destruct (kfind_img (kn cs) a) as [[lo hi]|] eqn:Hk; [|discriminate].
  repeat (apply andb_prop in H as [H ?]).
  repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in X end.
  destruct (rdn SEGS (fun _ => None) (Z_to_bv 64 a) w) as [bs|] eqn:Hr; [|discriminate].
  match goal with X : bytes_eqb _ _ = true |- _ => apply bytes_eqb_eq in X; subst bs end.
  rewrite <- Hr. apply rdn_ext.
  - rewrite u64_lit by lia. lia.
  - intros x Hx. rewrite u64_lit in Hx by lia.
    cbn beta. replace x with (Z_to_bv 64 (bv_unsigned x)) by apply Z_to_bv_bv_unsigned.
    apply (hb_img_at SEGS A LIMIT SINV argH FS0 HULL_ok argH_high E cs R FULL model a lo hi HC Hk); [lia|].
    unfold in_hull. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Definition chk_sub (k : list kentry) (a : Z) (w : nat) (v : Z) : bool :=
  existsb (fun K => match K with
                    | KWord (SA (ELit 0) a0) w0 (ELit v0) =>

                        if (Z.leb 0 a0 && Z.leb a0 a && Z.leb (a + Z.of_nat w) (a0 + Z.of_nat w0) && Z.ltb 0 (Z.of_nat w))%bool
                        then bytes_eqb (firstn w (skipn (Z.to_nat (a - a0)) (word_to_le_bytes w0 (Z_to_bv 64 v0)))) (word_to_le_bytes w (Z_to_bv 64 v))
                        else false
                    | _ => false
                    end) k.

Lemma hc_sub : forall E cs R FULL model a w v,
  CSOK E cs R FULL model -> chk_sub (kn cs) a w v = true ->
  rdn SEGS FULL (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)).
Proof.
  intros E cs R FULL model a w v HC H. unfold chk_sub in H. apply existsb_exists in H as (K & Hin & Hc).
  destruct K as [[b a0] w0 v0| | | | | | | | |]; try discriminate.
  destruct b as [z| | | | | | |]; try discriminate. destruct z; try discriminate.
  destruct v0 as [v0| | | | | | |]; try discriminate.
  match type of Hc with (if ?c then _ else _) = true => destruct c eqn:Hg; [|discriminate] end.
  apply bytes_eqb_eq in Hc. rename Hc into Hb. rename Hg into Hc.
  repeat (apply andb_prop in Hc as [Hc ?]).
  repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in X end.
  destruct (hb_word SEGS A LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E cs R FULL model _ w0 _ HC Hin) as (Hw & Hf & Hr & _).
  pose proof (flat_u E _ _ Hf) as Hu. unfold estart in Hu; cbn [a_base a_off edenot] in Hu.
  destruct Hf as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4; cbn [a_base a_off edenot] in F1, F2, F4.
  rewrite u64_lit in Hu, F1, F2, F4 by lia. rewrite Z.add_0_l in Hu, F1, F2, F4.
  cbn [edenot] in Hr.
  pose proof (rdn_slice SEGS FULL w0 _ _ (Z.to_nat (a - a0)) w Hr ltac:(lia)) as Hs.
  rewrite Hb in Hs. rewrite <- Hs. f_equal.
  apply bv_eq. rewrite u64_lit by lia.
  unfold nat_to_word. rewrite bv_add_unsigned, Hu. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite (Z.mod_small (Z.of_nat (Z.to_nat (a - a0)))) by lia. rewrite Z.mod_small by lia. lia.
Qed.
End Cells.
