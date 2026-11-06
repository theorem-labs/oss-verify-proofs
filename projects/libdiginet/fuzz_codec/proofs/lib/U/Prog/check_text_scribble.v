(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 552 of its 576 lines of code are new or changed and 120 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/diginet_sysex_encode.v, with its addresses changed; 621 of its 734 lines of code are new or changed and 463 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells
  memset_c bcmp_c diginet_scribble_text_c check_text_scribble_c.
Import ListNotations.
Open Scope Z_scope.

(** check_text_scribble of the UBSan image (fuzz_codec.c:431-452; 364 bytes at 0x14e00, frame 0x30)
    against check_text_scribble_contract, given the contracts of memset, diginet_scribble_text and bcmp. The
    frame holds want[8] at sp-48 and the saved s3, s2, s1, s0, ra above it. The walk: a prologue, the inlined
    owed_scribble_text loop (a fuel-indexed lemma over the output slots left, with the invariant tying
    want[0..o) and the bytes used to scr_owe on the rest of the text), the inline pad loop, the 0xa5 memset,
    the two checked calls, the inlined fuzz_all loop over chars[n..24) and the epilogue. Each
    pointer-overflow trap branch (to the unimp at 0x14eb0) compares a pointer's complement with an offset
    that the stack, text and chars bounds keep small, so none is taken. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- list and cell lemmas ---- *)

Lemma scr_app_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hl, Hw.
  rewrite cells_bytes_length in B2 by exact W1.
  split.
  - split; [split; [exact W1 | exact B1] |]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [exact W2 | exact B2] |]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

Lemma scr_app_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (Ha1 & Hl1 & Hw1)] [[W2 B2] (Ha2 & Hl2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

Lemma scr_byte : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma scr_CB_split : forall m A k l1 l2, rw_cells rsegs m A [CB k (l1 ++ l2)] ->
  forall B k1 k2, k = (k1 + k2)%nat -> length l1 = k1 -> B = A + Z.of_nat k1 ->
  rw_cells rsegs m A [CB k1 l1] /\ rw_cells rsegs m B [CB k2 l2].
Proof.
  intros m A k l1 l2 [[Hwf Hb] Hw] B k1 k2 Hk H1 HB. subst k k1 B.
  cbn [cells_wf cell_wf] in Hwf. rewrite app_length in Hwf.
  assert (H' : rw_cells rsegs m A ([CB (length l1) l1] ++ [CB k2 l2])).
  { split; [split|].
    - cbn [app cells_wf cell_wf]. split; [reflexivity|]. split; [lia | exact I].
    - cbn [app cells_bytes cbytes] in Hb |- *. rewrite !app_nil_r in Hb |- *. exact Hb.
    - cbn [app cells_size csize] in Hw |- *. replace (length l1 + (k2 + 0))%nat with (length l1 + k2 + 0)%nat by lia.
      exact Hw. }
  destruct (scr_app_split m A _ _ H') as [R1 R2]. split; [exact R1|].
  cbn [cells_size csize] in R2. replace (A + Z.of_nat (length l1 + 0)) with (A + Z.of_nat (length l1)) in R2 by lia.
  exact R2.
Qed.

Lemma scr_CB_join : forall m A k1 l1, rw_cells rsegs m A [CB k1 l1] ->
  forall B k2 l2, rw_cells rsegs m B [CB k2 l2] -> B = A + Z.of_nat k1 ->
  rw_cells rsegs m A [CB (k1 + k2) (l1 ++ l2)].
Proof.
  intros m A k1 l1 R1 B k2 l2 R2 HB. subst B.
  assert (R2' : rw_cells rsegs m (A + Z.of_nat (cells_size [CB k1 l1])) [CB k2 l2]).
  { cbn [cells_size csize]. replace (A + Z.of_nat (k1 + 0)) with (A + Z.of_nat k1) by lia. exact R2. }
  destruct (scr_app_join m A _ _ R1 R2') as [[Hwf Hb] Hw].
  cbn [app cells_wf cell_wf] in Hwf. destruct Hwf as [L1 [L2 _]].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite app_length; lia | exact I].
  - cbn [app cells_bytes cbytes] in Hb |- *. rewrite !app_nil_r in Hb |- *. exact Hb.
  - cbn [app cells_size csize] in Hw |- *. replace (k1 + k2 + 0)%nat with (k1 + (k2 + 0))%nat by lia. exact Hw.
Qed.

Lemma scr_CB_size : forall m A k l, rw_cells rsegs m A [CB k l] -> forall k', k = k' -> rw_cells rsegs m A [CB k' l].
Proof. intros; subst; assumption. Qed.

Lemma scr_repeat_app : forall {A} (x : A) a b, repeat x (a + b) = repeat x a ++ repeat x b.
Proof. intros A x a b. induction a as [|a IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma scr_repeat_split : forall {A} (x : A) k K, (k <= K)%nat -> repeat x K = repeat x k ++ repeat x (K - k).
Proof. intros A x k K H. rewrite <- scr_repeat_app. f_equal. lia. Qed.

Lemma scr_bz_app : forall a b, bz (a ++ b) = bz a ++ bz b.
Proof. intros a b. unfold bz. apply map_app. Qed.

Lemma scr_bz_repeat : forall x k, bz (repeat x k) = repeat (b8 x) k.
Proof. intros x k. unfold bz. induction k as [|k IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma scr_bz_length : forall l, length (bz l) = length l.
Proof. intros l. unfold bz. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma scr_zb_length : forall l, length (zb l) = length l.
Proof. intros l. unfold zb. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma scr_firstn_app : forall {A} (l1 l2 : list A) k, length l1 = k -> firstn k (l1 ++ l2) = l1.
Proof. intros A l1 l2 k <-. apply firstn_app_exact. Qed.

Lemma scr_skipn_app : forall {A} (l1 l2 : list A) k, skipn (length l1 + k) (l1 ++ l2) = skipn k l2.
Proof. intros A l1 l2 k. induction l1 as [|x l1 IH]; cbn; [reflexivity|]. exact IH. Qed.

Lemma scr_nth_repeat : forall {A} k i (x d : A), (i < k)%nat -> nth i (repeat x k) d = x.
Proof. intros A k. induction k as [|k IH]; intros i x d Hi; [lia|]. destruct i; cbn; [reflexivity|]. apply IH. lia. Qed.

Lemma scr_le1 : forall v, le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof.
  intros v. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite ?unsigned_lit_wrap. apply mod_mod8_of_modw. lia.
Qed.

Lemma scr_memcmp_self : forall l r, StrFun.memcmp_model l (l ++ r) (length l) = Some 0.
Proof. induction l as [|x l IH]; intros r; cbn; [reflexivity|]. rewrite Z.eqb_refl. apply IH. Qed.

Lemma scr_memcmp_ok : forall l w k, firstn k w = l -> length l = k -> StrFun.memcmp_model l w k = Some 0.
Proof.
  intros l w k H1 H2. rewrite <- (firstn_skipn k w), H1. rewrite <- H2. apply scr_memcmp_self.
Qed.

Lemma scr_land255 : forall z, Z.land z 255 = z mod 256.
Proof. intros z. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma scr_mod64_256 : forall z, (z mod 18446744073709551616) mod 256 = z mod 256.
Proof. intros z. change 18446744073709551616 with (2^64). change 256 with (2^8). apply mod_mod8_of_modw. lia. Qed.

(** ---- the model: scr_owe one step at a time ---- *)

Lemma scr_cstring : forall l, In 0 l ->
  (length (cstring l) < length l)%nat /\ nth (length (cstring l)) l 0 = 0 /\
  forall j, (j < length (cstring l))%nat -> nth j l 0 <> 0.
Proof.
  induction l as [|x l IH]; cbn; intros H; [contradiction|].
  destruct (Z.eqb_spec x 0) as [E|E].
  - subst x. cbn. split; [lia|]. split; [reflexivity|]. intros; lia.
  - destruct H as [H|H]; [congruence|]. destruct (IH H) as (A & B & C). cbn.
    split; [lia|]. split; [exact B|]. intros [|j] Hj; [exact E|]. apply C. lia.
Qed.

Lemma scr_skipn_cons : forall (l : list Z) k, (k < length l)%nat -> skipn k l = nth k l 0 :: skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k] Hk; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma scr_hd_skipn : forall (l : list Z) k, match skipn k l with y :: _ => y | [] => 0 end = nth k l 0.
Proof. induction l as [|x l IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.

Lemma scr_tl_skipn : forall (l : list Z) k, tl (skipn k l) = skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.

Lemma scr_owe_0 : forall t, scr_owe t 0 = ([], 0).
Proof. intros [|x t]; reflexivity. Qed.

Lemma scr_owe_len : forall k t, length (fst (scr_owe t k)) = k.
Proof.
  induction k as [|k IH]; intros t; [rewrite scr_owe_0; reflexivity|].
  destruct t as [|x t']; cbn [scr_owe]; [cbn [fst]; apply repeat_length|].
  destruct (x =? 0); [cbn [fst]; apply repeat_length|].
  cbv iota.
  match goal with |- context [if ?c then _ else _] => destruct c end.
  - destruct (scr_owe (tl t') k) as [o u] eqn:E. cbn [fst length]. specialize (IH (tl t')). rewrite E in IH. cbn [fst] in IH. lia.
  - destruct (scr_owe t' k) as [o u] eqn:E. cbn [fst length]. specialize (IH t'). rewrite E in IH. cbn [fst] in IH. lia.
Qed.

Lemma scr_owe_step : forall t j k, (j < length t)%nat -> nth j t 0 <> 0 ->
  scr_owe (skipn j t) (S k) =
   (if (nth j t 0 =? 46) && (49 <=? nth (S j) t 0) && (nth (S j) t 0 <=? 57)
    then ((nth (S j) t 0 - 26) :: fst (scr_owe (skipn (S (S j)) t) k), snd (scr_owe (skipn (S (S j)) t) k) + 2)
    else ((if nth j t 0 <? 128 then nth j t 0 else 63) :: fst (scr_owe (skipn (S j) t) k),
          snd (scr_owe (skipn (S j) t) k) + 1)).
Proof.
  intros t j k Hj Hx. rewrite (scr_skipn_cons t j Hj). cbn [scr_owe].
  rewrite (proj2 (Z.eqb_neq _ _) Hx). rewrite scr_hd_skipn, scr_tl_skipn.
  destruct ((nth j t 0 =? 46) && (49 <=? nth (S j) t 0) && (nth (S j) t 0 <=? 57)).
  - destruct (scr_owe (skipn (S (S j)) t) k); reflexivity.
  - destruct (scr_owe (skipn (S j) t) k); reflexivity.
Qed.

Lemma scr_owe_zero : forall t j k, (j < length t)%nat -> nth j t 0 = 0 ->
  scr_owe (skipn j t) k = (repeat 32 k, 0).
Proof.
  intros t j k Hj Hx. rewrite (scr_skipn_cons t j Hj), Hx.
  destruct k as [|k]; reflexivity.
Qed.

Lemma scr_cond_true : forall y, 49 <= y <= 57 -> (46 =? 46) && (49 <=? y) && (y <=? 57) = true.
Proof. intros y Hy. rewrite (proj2 (Z.leb_le 49 y)), (proj2 (Z.leb_le y 57)) by lia. reflexivity. Qed.

Lemma scr_cond_false : forall x y, ~ (x = 46 /\ 49 <= y <= 57) -> (x =? 46) && (49 <=? y) && (y <=? 57) = false.
Proof.
  intros x y H. destruct (Z.eqb_spec x 46); destruct (Z.leb_spec 49 y); destruct (Z.leb_spec y 57); cbn; try reflexivity.
  exfalso. apply H. split; [assumption | lia].
Qed.

Ltac scr_ranges sp a0 a1 a2 :=
  pose proof (bv_unsigned_in_range 64 sp) as Rsp; pose proof (bv_unsigned_in_range 64 a0) as Ra0;
  pose proof (bv_unsigned_in_range 64 a1) as Ra1; pose proof (bv_unsigned_in_range 64 a2) as Ra2;
  unfold bv_modulus in Rsp, Ra0, Ra1, Ra2.

Ltac clean_unsigned :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
  end.

(* [call] with the callee post unfolded and the bv_unsigned of literal registers cleaned first, so the
   footprints of the callee are plain Z terms when [post_call] transports the facts. *)
Tactic Notation "callz" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [ eapply SPEC | cbv beta delta [memset_post memcmp_post]; clean_unsigned; post_call segs m ]
  end.

Section Scr.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo : Z) (a0 a1 a2 : word) (n : Z) (tb cj : list byte).
Hypothesis HMEMS : memset_contract.
Hypothesis HDST : diginet_scribble_text_contract.
Hypothesis HBCMP : bcmp_contract.
Hypothesis HT0 : bv_unsigned a0 <> 0.
Hypothesis HTB : bytes_at rsegs m (bv_unsigned a0) tb.
Hypothesis HZ : In (b8 0) tb.
Hypothesis HCJ : rw_cells rsegs m (bv_unsigned a1) [CB 24 cj].
Hypothesis HDJ : disj (bv_unsigned a0) (Z.of_nat (length tb)) (bv_unsigned a1) 24.
Hypothesis HN : bv_unsigned a2 = n.
Hypothesis HN8 : 0 <= n <= 8.
Hypothesis HSA0 : bv_unsigned sp <= bv_unsigned a0.
Hypothesis HSA1 : bv_unsigned sp <= bv_unsigned a1.
Hypothesis HMI0 : mem_inv rsegs m.
Hypothesis ST0 : stk rsegs m lo (bv_unsigned sp).
Hypothesis LO : lo + 48 <= bv_unsigned sp.
Hypothesis OWE : owed_scribble_text_spec (zb tb) n = scribble_text_spec (zb tb) n.

Local Notation tz := (zb tb).
Local Notation nn := (Z.to_nat n).
Local Notation tbz k := (bv_unsigned (nth (Z.to_nat k) tb (Z_to_bv 8 0))).
Local Notation WF := [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 24)].

Definition saved : list cell := [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition Qs (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch WF m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    rw_cells rsegs m' (bv_unsigned a1) [CB 24 (bz (scribble_bytes (zb tb) n))].

(** The frame, the text and chars, and the footprint facts the text loop keeps; w is want[0..8). *)
Definition fr (m1 : word -> option byte) (w : list byte) : Prop :=
  rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 w] /\
  rw_cells rsegs m1 (bv_unsigned sp + -40) saved /\
  bytes_at rsegs m1 (bv_unsigned a0) tb /\
  rw_cells rsegs m1 (bv_unsigned a1) [CB 24 cj] /\
  stk rsegs m1 lo (bv_unsigned sp + -48) /\
  munch WF m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1.

Lemma mk_fr : forall m1 w,
  rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 w] -> rw_cells rsegs m1 (bv_unsigned sp + -40) saved ->
  bytes_at rsegs m1 (bv_unsigned a0) tb -> rw_cells rsegs m1 (bv_unsigned a1) [CB 24 cj] ->
  stk rsegs m1 lo (bv_unsigned sp + -48) -> munch WF m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> fr m1 w.
Proof. intros m1 w H1 H2 H3 H4 H5 H6 H7 H8. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 H8))))))). Qed.

(** The text loop's model invariant: o output slots and i text bytes done, pre the bytes owed so far. *)
Definition MODEL (o i : Z) (pre : list Z) : Prop :=
  fst (scr_owe tz nn) = pre ++ fst (scr_owe (skipn (Z.to_nat i) tz) (nn - Z.to_nat o)) /\
  snd (scr_owe tz nn) = i + snd (scr_owe (skipn (Z.to_nat i) tz) (nn - Z.to_nat o)).

Definition zp : Z := Z.of_nat (length (cstring tz)).

Lemma tz_nth : forall k, nth k tz 0 = bv_unsigned (nth k tb (Z_to_bv 8 0)).
Proof. intros k. unfold zb. exact (map_nth (fun b => bv_unsigned b) tb (Z_to_bv 8 0) k). Qed.

Lemma zp_props : 0 <= zp < Z.of_nat (length tb) /\ tbz zp = 0 /\ (forall j, 0 <= j < zp -> tbz j <> 0).
Proof.
  assert (HIn : In 0 tz).
  { pose proof (in_map (fun b : byte => bv_unsigned b) _ _ HZ) as H. exact H. }
  destruct (scr_cstring tz HIn) as (A & B & C).
  pose proof (scr_zb_length tb) as Ltz.
  unfold zp. split; [lia|]. split.
  - rewrite <- tz_nth, Nat2Z.id. exact B.
  - intros j Hj. rewrite <- tz_nth. apply C. lia.
Qed.

Lemma tbz_range : forall k, 0 <= tbz k < 256.
Proof.
  intros k. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) tb (Z_to_bv 8 0))) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma model_init : MODEL 0 0 [].
Proof. unfold MODEL. cbn [Z.to_nat skipn app]. rewrite Nat.sub_0_r. split; reflexivity. Qed.

Lemma model_dot : forall o i pre, MODEL o i pre -> 0 <= o < n -> 0 <= i < zp ->
  tbz i = 46 -> 49 <= tbz (i + 1) <= 57 ->
  MODEL (o + 1) (2 + i) (pre ++ [tbz (i + 1) + -26]).
Proof.
  intros o i pre [H1 H2] Ho Hi Hx Hy.
  destruct zp_props as (Hzl & _ & _). pose proof (scr_zb_length tb) as Ltz.
  assert (Hlen : (Z.to_nat i < length tz)%nat) by lia.
  assert (Hn0 : nth (Z.to_nat i) tz 0 <> 0) by (rewrite tz_nth; lia).
  assert (Ek : (nn - Z.to_nat o)%nat = S (nn - Z.to_nat (o + 1))) by lia.
  rewrite Ek, (scr_owe_step tz (Z.to_nat i) _ Hlen Hn0) in H1, H2.
  replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in H1, H2 by lia.
  rewrite !tz_nth, Hx in H1, H2. rewrite (scr_cond_true _ Hy) in H1, H2.
  replace (S (Z.to_nat (i + 1))) with (Z.to_nat (2 + i)) in H1, H2 by lia.
  cbn [fst snd] in H1, H2. split.
  - rewrite H1, <- app_assoc. reflexivity.
  - rewrite H2. lia.
Qed.

Lemma model_one : forall o i pre, MODEL o i pre -> 0 <= o < n -> 0 <= i < zp ->
  ~ (tbz i = 46 /\ 49 <= tbz (i + 1) <= 57) ->
  MODEL (o + 1) (1 + i) (pre ++ [if tbz i <? 128 then tbz i else 63]).
Proof.
  intros o i pre [H1 H2] Ho Hi Hnd.
  destruct zp_props as (Hzl & _ & Hnz). pose proof (scr_zb_length tb) as Ltz.
  assert (Hlen : (Z.to_nat i < length tz)%nat) by lia.
  assert (Hn0 : nth (Z.to_nat i) tz 0 <> 0) by (rewrite tz_nth; apply Hnz; lia).
  assert (Ek : (nn - Z.to_nat o)%nat = S (nn - Z.to_nat (o + 1))) by lia.
  rewrite Ek, (scr_owe_step tz (Z.to_nat i) _ Hlen Hn0) in H1, H2.
  replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in H1, H2 by lia.
  rewrite !tz_nth in H1, H2. rewrite (scr_cond_false _ _ Hnd) in H1, H2.
  replace (Z.to_nat (i + 1)) with (Z.to_nat (1 + i)) in H1, H2 by lia.
  cbn [fst snd] in H1, H2. split.
  - rewrite H1, <- app_assoc. reflexivity.
  - rewrite H2. lia.
Qed.

Lemma model_end : forall o i pre, MODEL o i pre -> 0 <= o <= n -> 0 <= i <= zp -> (o = n \/ i = zp) ->
  fst (scr_owe tz nn) = pre ++ repeat 32 (nn - Z.to_nat o) /\ snd (scr_owe tz nn) = i.
Proof.
  intros o i pre [H1 H2] Ho Hi Hend.
  destruct zp_props as (Hzl & Hz0 & _). pose proof (scr_zb_length tb) as Ltz.
  destruct Hend as [E|E].
  - subst o. replace (nn - Z.to_nat n)%nat with 0%nat in * by lia.
    rewrite scr_owe_0 in H1, H2. cbn [fst snd repeat] in H1, H2 |- *. rewrite ?app_nil_r in H1 |- *.
    split; [exact H1 | lia].
  - subst i. rewrite (scr_owe_zero tz (Z.to_nat zp)) in H1, H2 by (try rewrite tz_nth; lia).
    cbn [fst snd] in H1, H2. split; [exact H1 | lia].
Qed.

(** ---- the frame store of the text loop ---- *)

Lemma want_store : forall m1 A pre wj o v,
  rw_cells rsegs m1 A [CB 8 (bz pre ++ wj)] -> length pre = Z.to_nat o -> length wj = (8 - Z.to_nat o)%nat ->
  0 <= o < 8 ->
  rw_cells rsegs (write_to_mem m1 (wa (A + o)) [Z_to_bv 8 v]) A [CB 8 (bz (pre ++ [v]) ++ skipn 1 wj)].
Proof.
  intros m1 A pre wj o v [[Hwf Hb] Hw] Hp Hj Ho.
  pose proof (scr_bz_length pre) as Lb.
  assert (EU : upd_bytes (bz pre ++ wj) (Z.to_nat o) [Z_to_bv 8 v] = bz (pre ++ [v]) ++ skipn 1 wj).
  { unfold upd_bytes. rewrite scr_bz_app. cbn [length].
    rewrite (scr_firstn_app (bz pre) wj (Z.to_nat o)) by lia.
    replace (Z.to_nat o + 1)%nat with (length (bz pre) + 1)%nat by lia. rewrite scr_skipn_app.
    rewrite <- app_assoc. reflexivity. }
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite app_length, scr_bz_length, app_length, skipn_length. cbn [length]. lia.
  - cbn [cells_bytes cbytes] in Hb |- *. rewrite app_nil_r in Hb |- *. rewrite <- EU.
    apply bytes_at_write_inside; [exact Hb | lia |]. rewrite app_length. cbn [length]. lia.
  - cbn [cells_size csize] in Hw |- *. apply wr_at_write. exact Hw.
Qed.

Lemma fr_store : forall m1 pre wj o v,
  fr m1 (bz pre ++ wj) -> length pre = Z.to_nat o -> length wj = (8 - Z.to_nat o)%nat -> 0 <= o < 8 ->
  fr (write_to_mem m1 (wa (bv_unsigned sp + -48 + o)) [Z_to_bv 8 v]) (bz (pre ++ [v]) ++ skipn 1 wj).
Proof.
  intros m1 pre wj o v (HW & HSV & HT & HC & ST & MU & WM & HMI) Hp Hj Ho.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST0 as (Hlo & Hhi & _).
  pose proof (bytes_at_bound _ _ _ _ HT) as BT.
  pose proof (rw_cells_bound _ _ _ _ HC) as BC. cbn in BC.
  assert (HS : store_ok rsegs m1 (wa (bv_unsigned sp + -48 + o)) (length [Z_to_bv 8 v]) = true).
  { destruct HW as [_ HWR]. cbn [length].
    apply (wr_at_store_ok rsegs m1 _ _ o 1 HWR); cbn; lia. }
  apply mk_fr.
  - apply want_store; assumption.
  - apply rw_cells_frame; [exact HSV | lia | cbn [length]; lia | unfold saved; cbn [cells_size csize length Nat.add]; lia].
  - apply bytes_at_write_other; [exact HT | lia | cbn [length]; lia | cbn [length]; lia].
  - apply rw_cells_frame; [exact HC | lia | cbn [length]; lia | cbn [cells_size csize length Nat.add]; lia].
  - apply stk_write; [exact ST | lia | cbn [length]; lia].
  - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact HMI | exact HS].
Qed.

(** ---- the epilogue at 0x14f48 ---- *)

Lemma scr_exit : forall (ra' t0' t1' t2' x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 t3' t4' t5' t6' : word)
    (w : list byte) (m1 : word -> option byte),
  rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 w] ->
  rw_cells rsegs m1 (bv_unsigned sp + -40) saved ->
  rw_cells rsegs m1 (bv_unsigned a1) [CB 24 (bz (scribble_bytes (zb tb) n))] ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  munch WF m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qs
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x14f48) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 t3' t4' t5' t6' w m1
    HW HSV HC ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST0 as (Hlo & Hhi & _).
  unfold saved in HSV.
  do 6 zstep.
  assert (FR : rw_cells rsegs m1 (bv_unsigned sp + -48) ([CB 8 w] ++ saved)).
  { apply scr_app_join; [exact HW|]. cbn [cells_size csize Nat.add].
    replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) by lia. exact HSV. }
  eapply stk_release in FR; [ | exact ST | lia ].
  cbn [cells_size csize Nat.add saved app] in FR.
  replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in FR by lia.
  clear ST.
  zstep.
  finish.
Qed.

(** ---- fuzz_all over chars[n..24) at 0x14f30 (j counts from chars + n) ---- *)

Lemma sb_nth : forall j, (nn <= j < 24)%nat -> nth j (bz (scribble_bytes tz n)) (Z_to_bv 8 0) = Z_to_bv 8 165.
Proof.
  intros j Hj. unfold scribble_bytes. rewrite scr_bz_app, scr_bz_repeat.
  pose proof (scr_owe_len nn tz) as L. unfold owed_scribble_text_spec.
  rewrite app_nth2 by (rewrite scr_bz_length; lia).
  rewrite scr_bz_length, L. apply scr_nth_repeat. lia.
Qed.

Lemma sb_length : length (bz (scribble_bytes tz n)) = 24%nat.
Proof.
  unfold scribble_bytes. rewrite scr_bz_length, app_length, repeat_length.
  pose proof (scr_owe_len nn tz) as L. unfold owed_scribble_text_spec. rewrite L. lia.
Qed.

Lemma scr_fuzz : forall fuel (j : Z) (ra' t0' t1' t2' x8 pw cw lw nw x13 x14 x15 x16 x17 x18 x19 t3' t4' t5' t6' : word)
    (w : list byte) (m1 : word -> option byte),
  (Z.to_nat (24 - n - j) <= fuel)%nat -> 0 <= j < 24 - n ->
  pw = Z_to_bv 64 (bv_unsigned a1 + n) -> cw = Z_to_bv 64 j -> lw = Z_to_bv 64 (24 - n) ->
  bv_unsigned nw = 18446744073709551615 - (bv_unsigned a1 + n) -> x13 = Z_to_bv 64 165 ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 w] ->
  rw_cells rsegs m1 (bv_unsigned sp + -40) saved ->
  rw_cells rsegs m1 (bv_unsigned a1) [CB 24 (bz (scribble_bytes (zb tb) n))] ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  munch WF m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qs
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' x8 pw cw lw nw x13 x14 x15 x16 x17
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x14f30) fc None m1 (seg_rom rsegs)).
Proof.
  induction fuel as [|fuel IH];
    intros j ra' t0' t1' t2' x8 pw cw lw nw x13 x14 x15 x16 x17 x18 x19 t3' t4' t5' t6' w m1
      Hf Hj Epw Ecw Elw Hnw E13 HW HSV HC ST MU WM HMI; [lia|].
  subst pw cw lw x13.
  scr_ranges sp a0 a1 a2.
  pose proof (rw_cells_bound _ _ _ _ HC) as BC. cbn [cells_size csize Nat.add] in BC.
  assert (HR : ov_read_bytes rsegs m1 (wa (bv_unsigned a1 + (n + j))) 1 = Some [Z_to_bv 8 165]).
  { pose proof HC as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    rewrite (scr_byte m1 _ _ (n + j) HB) by (rewrite sb_length; lia).
    rewrite sb_nth by lia. reflexivity. }
  zstep.
  if_cases ET; zify_cond ET; [ exfalso; lia | ].
  zstep. zstep. zstep. try if_false. zstep. zstep.
  if_cases EZ; zify_cond EZ.
  - eapply (IH (j + 1)); try eassumption; try lia; try reflexivity.
  - eapply scr_exit; eassumption.
Qed.

(** ---- the checked calls at 0x14ed4 ---- *)

Lemma scr_after : forall (ra' t0' t1' t2' x10 x11 x12 x13 x14 x15 x16 x17 t3' t4' t5' t6' : word)
    (w : list byte) (used : Z) (m1 : word -> option byte),
  length w = 8%nat -> firstn nn w = bz (fst (scr_owe tz nn)) -> used = snd (scr_owe tz nn) ->
  fr m1 w ->
  evt rsegs Qs
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' a2 a1 x10 x11 x12 x13 x14 x15 x16 x17
             a0 (Z_to_bv 64 used) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x14ed4) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' x10 x11 x12 x13 x14 x15 x16 x17 t3' t4' t5' t6' w used m1 HL HF HU
    (HW & HSV & HT & HC & ST & MU & WM & HMI).
  scr_ranges sp a0 a1 a2.
  pose proof ST0 as (Hlo & Hhi & _).
  pose proof (rw_cells_bound _ _ _ _ HC) as BC. cbn [cells_size csize Nat.add] in BC.
  pose proof (bytes_at_bound _ _ _ _ HT) as BT.
  pose proof HDJ as HDJ'. unfold disj in HDJ'.
  pose proof HDST as DST. unfold diginet_scribble_text_contract, DIGINET_SCRIBBLE_TEXT in DST.
  unfold saved in HSV.
  do 4 zstep.
  callz HMEMS; [ exact HC | exact HMI | ].
  match goal with H : rw_cells rsegs ?mm (bv_unsigned a1) _ |- _ =>
    change (rw_cells rsegs mm (bv_unsigned a1) [CB 24 (repeat (Z_to_bv 8 165) 24)]) in H;
    rewrite (scr_repeat_split (Z_to_bv 8 165) nn 24 ltac:(lia)) in H;
    destruct (scr_CB_split _ _ _ _ _ H (bv_unsigned a1 + n) nn (24 - nn) ltac:(lia) (repeat_length _ _) ltac:(lia))
      as [HC1 HC2];
    clear H
  end.
  do 4 zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply DST;
      unfold diginet_scribble_text_pre;
      split; [exact HT0|]; split; [split; [eassumption | exact HZ]|]; split; [lia|]; split; [exact HN|];
      split; [exact HC1|]; split; [unfold disj; lia|]; eassumption
    | cbv beta; clean_unsigned; post_call rsegs mm ]
  end.
  match goal with H : ?x = Z_to_bv 64 (snd (scribble_text_spec _ _)) |- _ => subst x end.
  rewrite <- OWE. unfold owed_scribble_text_spec. subst used.
  zstep. try if_false.
  do 4 zstep.
  match goal with H : rw_cells rsegs ?mm (bv_unsigned a1) [CB nn _] |- _ => rename H into HD3 end.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HBCMP;
      [ exact (proj2 (proj1 HD3))
      | clean_unsigned; exact (proj2 (proj1 HW))
      | cbn [cells_bytes cbytes]; rewrite !app_nil_r, HN; rewrite <- OWE; unfold owed_scribble_text_spec;
        apply scr_memcmp_ok; [exact HF | rewrite scr_bz_length; apply scr_owe_len]
      | eassumption ]
    | cbv beta delta [memcmp_post]; clean_unsigned; post_call rsegs mm ]
  end.
  zstep. try if_false.
  zstep. zstep.
  if_cases ET; zify_cond ET.
  { exfalso. rewrite zb_lxor_ones in ET by lia. lia. }
  zstep. zstep.
  if_cases EZ; zify_cond EZ.
  { exfalso. lia. }
  do 5 zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HCF : rw_cells rsegs mm (bv_unsigned a1) [CB 24 (bz (scribble_bytes (zb tb) n))])
  end.
  { replace (bz (scribble_bytes tz n)) with (bz (fst (scribble_text_spec tz n)) ++ repeat (Z_to_bv 8 165) (24 - nn)).
    - exact (scr_CB_size _ _ _ _ (scr_CB_join _ _ _ _ HD3 _ _ _ HC2 ltac:(lia)) 24%nat ltac:(lia)).
    - unfold scribble_bytes. rewrite <- OWE. rewrite scr_bz_app, scr_bz_repeat. f_equal.
      replace (Z.to_nat (24 - n)) with (24 - nn)%nat by lia. reflexivity. }
  eapply (scr_fuzz (Z.to_nat (24 - n)) 0); try eassumption; try lia; try (rewrite HN; reflexivity);
    try reflexivity.
  rewrite unsigned_lit by (apply Z_lxor_range; lia). rewrite zb_lxor_ones by lia. lia.
Qed.

(** ---- the inline pad loop at 0x14ec0: want[o..n) = ' ' ---- *)

Lemma scr_padl : forall fuel (ra' t0' t1' t2' x14 x15 x16 x17 t3' t4' t5' t6' ns : word)
    (o used : Z) (pre : list Z) (wj : list byte) (m1 : word -> option byte),
  (Z.to_nat (n - o) <= fuel)%nat -> 0 <= o < n ->
  bv_unsigned ns = 18446744073709551615 - (bv_unsigned sp + -48) ->
  length pre = Z.to_nat o -> length wj = (8 - Z.to_nat o)%nat ->
  fst (scr_owe tz nn) = pre ++ repeat 32 (nn - Z.to_nat o) -> used = snd (scr_owe tz nn) ->
  fr m1 (bz pre ++ wj) ->
  evt rsegs Qs
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' a2 a1 (Z_to_bv 64 o) ns
             (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 32) x14 x15 x16 x17
             a0 (Z_to_bv 64 used) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x14ec0) fc None m1 (seg_rom rsegs)).
Proof.
  induction fuel as [|fuel IH];
    intros ra' t0' t1' t2' x14 x15 x16 x17 t3' t4' t5' t6' ns o used pre wj m1 Hf Ho Hns Hp Hj OUT HU FRm;
    [lia|].
  scr_ranges sp a0 a1 a2.
  pose proof ST0 as (Hlo & Hhi & _).
  assert (HS : store_ok rsegs m1 (wa (bv_unsigned sp + -48 + o)) 1 = true).
  { destruct FRm as ([_ HWR] & _). apply (wr_at_store_ok rsegs m1 _ _ o 1 HWR); cbn; lia. }
  pose proof (fr_store m1 pre wj o 32 FRm Hp Hj ltac:(lia)) as FR2. unfold wa in FR2.
  zstep.
  if_cases ET; zify_cond ET; [ exfalso; lia | ].
  zstep. zstep. zstep.
  rewrite scr_le1.
  remember (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + -48 + o)) [Z_to_bv 8 32]) as m2 eqn:Em2.
  clear Em2 HS FRm.
  assert (OUT' : fst (scr_owe tz nn) = (pre ++ [32]) ++ repeat 32 (nn - Z.to_nat (o + 1))).
  { rewrite OUT, <- app_assoc. replace (nn - Z.to_nat o)%nat with (S (nn - Z.to_nat (o + 1))) by lia. reflexivity. }
  zstep.
  if_cases EN; zify_cond EN.
  - eapply IH with (o := o + 1) (used := used) (pre := pre ++ [32]) (wj := skipn 1 wj);
      try eassumption; try lia.
    + rewrite app_length. cbn [length]. lia.
    + rewrite skipn_length. lia.
  - eapply scr_after with (w := bz (pre ++ [32]) ++ skipn 1 wj) (used := used); try eassumption.
    + rewrite app_length, scr_bz_length, app_length, skipn_length. cbn [length]. lia.
    + rewrite OUT'. replace (nn - Z.to_nat (o + 1))%nat with 0%nat by lia. cbn [repeat]. rewrite app_nil_r.
      apply scr_firstn_app. rewrite scr_bz_length, app_length. cbn [length]. lia.
Qed.

(** ---- the loop exit at 0x14eb4 ---- *)

Lemma scr_pad : forall (ra' t0' t1' t2' x12 x13 x14 x15 x16 x17 t3' t4' t5' t6' ns : word)
    (o i : Z) (pre : list Z) (wj : list byte) (m1 : word -> option byte),
  0 <= o <= n -> 0 <= i <= zp -> (o = n \/ i = zp) ->
  bv_unsigned ns = 18446744073709551615 - (bv_unsigned sp + -48) ->
  length pre = Z.to_nat o -> length wj = (8 - Z.to_nat o)%nat ->
  MODEL o i pre -> fr m1 (bz pre ++ wj) ->
  evt rsegs Qs
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' a2 a1 (Z_to_bv 64 o) ns x12 x13 x14 x15 x16 x17
             a0 (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x14eb4) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' x12 x13 x14 x15 x16 x17 t3' t4' t5' t6' ns o i pre wj m1 Ho Hi Hend Hns Hp Hj HM FRm.
  destruct (model_end o i pre HM Ho Hi Hend) as [OUT USED].
  pose proof (scr_bz_length pre) as Lb.
  scr_ranges sp a0 a1 a2.
  zstep.
  if_cases EB; zify_cond EB.
  - eapply scr_after with (w := bz pre ++ wj) (used := i); [ | | symmetry; exact USED | exact FRm ].
    + rewrite app_length. lia.
    + rewrite OUT. replace (nn - Z.to_nat o)%nat with 0%nat by lia. cbn [repeat]. rewrite app_nil_r.
      apply scr_firstn_app. lia.
  - zstep. zstep.
    eapply (scr_padl (Z.to_nat (n - o))); try eassumption; try lia. all: symmetry; exact USED.
Qed.

(** ---- the text loop ---- *)

Definition loop_ok (fuel : nat) : Prop :=
  forall (ra' t0' t1' t2' a6' a7' t3' t4' t5' t6' nt ns : word) (o i : Z) (pre : list Z) (wj : list byte)
         (m1 : word -> option byte),
  (Z.to_nat (n - o) < fuel)%nat -> 0 <= o <= n -> 0 <= i <= zp ->
  bv_unsigned nt = 18446744073709551615 - bv_unsigned a0 ->
  bv_unsigned ns = 18446744073709551615 - (bv_unsigned sp + -48) ->
  length pre = Z.to_nat o -> length wj = (8 - Z.to_nat o)%nat ->
  MODEL o i pre -> fr m1 (bz pre ++ wj) ->
  evt rsegs Qs
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' a2 a1
             (Z_to_bv 64 o) ns nt (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 46) (Z_to_bv 64 8)
             a6' a7' a0 (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x14e40) fc None m1 (seg_rom rsegs)).

(** One character done at 0x14ea4: k text bytes and one output slot. *)
Lemma scr_tail : forall fuel, loop_ok fuel ->
  forall (ra' t0' t1' t2' a7' t3' t4' t5' t6' nt ns : word) (o i k : Z) (pre : list Z) (wj : list byte)
         (m1 : word -> option byte),
  (Z.to_nat (n - o) < S fuel)%nat -> 0 <= o < n -> 0 <= i -> (k = 1 \/ k = 2) -> k + i <= zp ->
  bv_unsigned nt = 18446744073709551615 - bv_unsigned a0 ->
  bv_unsigned ns = 18446744073709551615 - (bv_unsigned sp + -48) ->
  length pre = Z.to_nat (o + 1) -> length wj = (8 - Z.to_nat (o + 1))%nat ->
  MODEL (o + 1) (k + i) pre -> fr m1 (bz pre ++ wj) ->
  evt rsegs Qs
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' a2 a1
             (Z_to_bv 64 o) ns nt (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 46) (Z_to_bv 64 8)
             (Z_to_bv 64 k) a7' a0 (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x14ea4) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel LOOP ra' t0' t1' t2' a7' t3' t4' t5' t6' nt ns o i k pre wj m1 Hf Ho Hi Hk Hki Hnt Hns Hp Hj HM FRm.
  destruct zp_props as (Hzl & Hz0 & Hnz).
  scr_ranges sp a0 a1 a2.
  pose proof (bytes_at_bound _ _ _ _ HTB) as BT.
  zstep. zstep. zstep.
  if_cases EL; zify_cond EL.
  - eapply LOOP; try eassumption; lia.
  - exfalso. lia.
Qed.

(** The store of a copied character at 0x14e98 (a6 = the byte). *)
Lemma scr_st : forall fuel, loop_ok fuel ->
  forall (ra' t0' t1' t2' a7' t3' t4' t5' t6' nt ns : word) (o i v : Z) (pre : list Z) (wj : list byte)
         (m1 : word -> option byte),
  (Z.to_nat (n - o) < S fuel)%nat -> 0 <= o < n -> 0 <= i < zp ->
  bv_unsigned nt = 18446744073709551615 - bv_unsigned a0 ->
  bv_unsigned ns = 18446744073709551615 - (bv_unsigned sp + -48) ->
  length pre = Z.to_nat o -> length wj = (8 - Z.to_nat o)%nat ->
  MODEL (o + 1) (1 + i) (pre ++ [v]) -> fr m1 (bz pre ++ wj) ->
  evt rsegs Qs
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' a2 a1
             (Z_to_bv 64 o) ns nt (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 46) (Z_to_bv 64 8)
             (Z_to_bv 64 v) a7' a0 (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x14e98) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel LOOP ra' t0' t1' t2' a7' t3' t4' t5' t6' nt ns o i v pre wj m1 Hf Ho Hi Hnt Hns Hp Hj HM FRm.
  scr_ranges sp a0 a1 a2.
  pose proof ST0 as (Hlo & Hhi & _).
  assert (HS : store_ok rsegs m1 (wa (bv_unsigned sp + -48 + o)) 1 = true).
  { destruct FRm as ([_ HWR] & _). apply (wr_at_store_ok rsegs m1 _ _ o 1 HWR); cbn; lia. }
  pose proof (fr_store m1 pre wj o v FRm Hp Hj ltac:(lia)) as FR2. unfold wa in FR2.
  zstep. zstep.
  rewrite scr_le1.
  remember (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + -48 + o)) [Z_to_bv 8 v]) as m2 eqn:Em2.
  clear Em2 HS FRm.
  zstep.
  eapply (scr_tail fuel LOOP) with (k := 1); try eassumption; try lia.
  - rewrite app_length. cbn [length]. lia.
  - rewrite skipn_length. lia.
Qed.

(** A character copied as it is (or '?') at 0x14e88. *)
Lemma scr_ascii : forall fuel, loop_ok fuel ->
  forall (ra' t0' t1' t2' a7' t3' t4' t5' t6' nt ns : word) (o i : Z) (pre : list Z) (wj : list byte)
         (m1 : word -> option byte),
  (Z.to_nat (n - o) < S fuel)%nat -> 0 <= o < n -> 0 <= i < zp ->
  ~ (tbz i = 46 /\ 49 <= tbz (i + 1) <= 57) ->
  bv_unsigned nt = 18446744073709551615 - bv_unsigned a0 ->
  bv_unsigned ns = 18446744073709551615 - (bv_unsigned sp + -48) ->
  length pre = Z.to_nat o -> length wj = (8 - Z.to_nat o)%nat ->
  MODEL o i pre -> fr m1 (bz pre ++ wj) ->
  evt rsegs Qs
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' a2 a1
             (Z_to_bv 64 o) ns nt (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 46) (Z_to_bv 64 8)
             (Z_to_bv 64 (tbz i)) a7' a0 (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x14e88) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel LOOP ra' t0' t1' t2' a7' t3' t4' t5' t6' nt ns o i pre wj m1 Hf Ho Hi Hnd Hnt Hns Hp Hj HM FRm.
  pose proof (model_one o i pre HM ltac:(lia) Hi Hnd) as HM1.
  pose proof (tbz_range i) as Rx.
  scr_ranges sp a0 a1 a2.
  zstep.
  if_cases ET; zify_cond ET; [ exfalso; lia | ].
  zstep. zstep.
  if_cases ES; zify_cond ES.
  - assert (Hx : tbz i < 128).
    { rewrite Z.shiftl_mul_pow2 in ES by lia. change (2 ^ 56) with 72057594037927936 in ES.
      try rewrite Z.mod_small in ES by lia. lia. }
    rewrite (proj2 (Z.ltb_lt _ _) Hx) in HM1. cbv beta iota in HM1.
    eapply (scr_st fuel LOOP); eassumption.
  - assert (Hx : 128 <= tbz i).
    { rewrite Z.shiftl_mul_pow2 in ES by lia. change (2 ^ 56) with 72057594037927936 in ES.
      try rewrite Z.mod_small in ES by lia. lia. }
    rewrite (proj2 (Z.ltb_ge _ _) Hx) in HM1. cbv beta iota in HM1.
    zstep.
    eapply (scr_st fuel LOOP); eassumption.
Qed.

(** The loop head at 0x14e40. *)
Lemma scr_loop : forall fuel, loop_ok fuel.
Proof.
  induction fuel as [|fuel IH]; unfold loop_ok;
    intros ra' t0' t1' t2' a6' a7' t3' t4' t5' t6' nt ns o i pre wj m1 Hf Ho Hi Hnt Hns Hp Hj HM FRm.
  { exfalso. lia. }
  destruct zp_props as (Hzl & Hz0 & Hnz).
  scr_ranges sp a0 a1 a2.
  pose proof ST0 as (Hlo & Hhi & _).
  pose proof (bytes_at_bound _ _ _ _ HTB) as BT.
  pose proof (tbz_range i) as Rx.
  assert (HB0 : ov_read_bytes rsegs m1 (wa (bv_unsigned a0 + i)) 1 = Some [nth (Z.to_nat i) tb (Z_to_bv 8 0)]).
  { destruct FRm as (_ & _ & HT & _). apply scr_byte; [exact HT | lia]. }
  zstep. zstep. zstep.
  if_cases EZ; zify_cond EZ.
  { assert (Ei : i = zp) by (destruct (Z.eq_dec i zp) as [E|E]; [exact E | exfalso; apply (Hnz i); [lia | exact EZ]]).
    eapply scr_pad; try eassumption; lia. }
  assert (Hiz : i < zp) by (destruct (Z.eq_dec i zp) as [E|E]; [rewrite E in EZ; lia | lia]).
  zstep.
  if_cases EO; zify_cond EO.
  { eapply scr_pad; try eassumption; lia. }
  zstep.
  if_cases ED; zify_cond ED.
  { eapply (scr_ascii fuel IH); try eassumption; try lia. }
  assert (HB1 : ov_read_bytes rsegs m1 (wa (bv_unsigned a0 + (i + 1))) 1 = Some [nth (Z.to_nat (i + 1)) tb (Z_to_bv 8 0)]).
  { destruct FRm as (_ & _ & HT & _). apply scr_byte; [exact HT | lia]. }
  pose proof (tbz_range (i + 1)) as Ry.
  zstep. zstep.
  if_cases ET; zify_cond ET; [ exfalso; lia | ].
  do 5 zstep.
  if_cases EG; zify_cond EG; rewrite scr_land255, scr_mod64_256 in EG.
  { eapply (scr_ascii fuel IH); try eassumption; try lia; try (intros [_ Ey]; Z.div_mod_to_equations; lia). }
  assert (Ey : 49 <= tbz (i + 1) <= 57) by (Z.div_mod_to_equations; lia).
  assert (Hy0 : i + 1 <> zp) by (intros E; rewrite <- E in Hz0; lia).
  zstep.
  if_cases ES; zify_cond ES; [ exfalso; lia | ].
  assert (HS : store_ok rsegs m1 (wa (bv_unsigned sp + -48 + o)) 1 = true).
  { destruct FRm as ([_ HWR] & _). apply (wr_at_store_ok rsegs m1 _ _ o 1 HWR); cbn; lia. }
  pose proof (fr_store m1 pre wj o (tbz (i + 1) + -26) FRm Hp Hj ltac:(lia)) as FR2. unfold wa in FR2.
  zstep. zstep. zstep.
  rewrite scr_le1.
  remember (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + -48 + o)) [Z_to_bv 8 (tbz (i + 1) + -26)]) as m2 eqn:Em2.
  clear Em2 HS FRm.
  zstep. zstep.
  eapply (scr_tail fuel IH) with (k := 2); try eassumption; try lia.
  - rewrite app_length. cbn [length]. lia.
  - rewrite skipn_length. lia.
  - apply model_dot; [exact HM | lia | lia | lia | exact Ey].
Qed.

(** ---- the entry at 0x14e00 ---- *)

Lemma scr_entry : forall m1, m1 = m -> forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt rsegs Qs
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14e00) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 Em t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
  assert (MU : munch WF m m1) by (rewrite Em; apply munch_refl).
  assert (WM : wmono rsegs m m1) by (rewrite Em; apply wmono_refl).
  pose proof HMI0 as HMI. rewrite <- Em in HMI.
  pose proof ST0 as ST. rewrite <- Em in ST.
  pose proof HTB as HT. rewrite <- Em in HT.
  pose proof HCJ as HC. rewrite <- Em in HC.
  scr_ranges sp a0 a1 a2.
  pose proof ST as (Hlo & Hhi & _).
  pose proof (rw_cells_bound _ _ _ _ HC) as BC. cbn [cells_size csize Nat.add] in BC.
  pose proof (bytes_at_bound _ _ _ _ HT) as BT.
  destruct zp_props as (Hzl & Hz0 & Hnz).
  carve_frame 48%nat ST.
  do 16 zstep.
  destruct (scr_app_split _ _ [CB 8 _] saved FR) as [HW HSV].
  cbn [cells_size csize Nat.add] in HSV.
  replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) in HSV by lia.
  clear FR.
  match type of HW with rw_cells _ _ _ [CB 8 ?jj] => set (j8 := jj) in HW end.
  assert (Hj8 : length j8 = 8%nat) by (destruct HW as [[Hwf _] _]; cbn in Hwf; tauto).
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FRm : fr mm j8) by (apply mk_fr; assumption) end.
  eapply (scr_loop (S (Z.to_nat n))) with (o := 0) (i := 0) (pre := []) (wj := j8);
    try eassumption; try exact model_init; try reflexivity; try (clearbody j8; lia);
    rewrite unsigned_lit by (apply Z_lxor_range; lia); rewrite zb_lxor_ones by lia; lia.
Qed.

End Scr.

Theorem check_text_scribble_holds : memset_contract -> diginet_scribble_text_contract -> bcmp_contract ->
  check_text_scribble_contract.
Proof.
  intros HMEMS HDST HBCMP.
  unfold check_text_scribble_contract, check_text_scribble_pre, CHECK_TEXT_SCRIBBLE, CHECK_TEXT_SCRIBBLE_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n tb cj
    (HT0 & [HTB HZ] & HCJ & HDJ & HN & HN8 & HSA0 & HSA1 & HMI & ST & LO & OWE).
  eapply scr_entry; first [ exact eq_refl | eassumption ].
Qed.
