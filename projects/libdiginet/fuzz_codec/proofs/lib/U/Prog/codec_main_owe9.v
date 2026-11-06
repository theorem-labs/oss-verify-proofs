(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 509 of its 532 lines of code are new or changed and 121 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe5.v, with its numbers changed; 353 of its 434 lines of code are new or changed and 451 lines of the source are left out. *)
(** Segment OWE9 (the SCRIBBLE case of owe()) of the walk of LLVMFuzzerTestOneInput in the UBSan
    image: the range test, the alignment trap on the desk, the seven_bit loop over d->chars bytes,
    the pl[] buffer, the memcpy of the characters into it, the call of owe_sysex and the want_key
    store. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img memcpy_c
  owe_sysex_c codec_main_inv codec_main_lib.
Import ListNotations.
Open Scope Z_scope.

(** A one-byte store of a symbolic register: Lib's rule for [le1 (zxb b)] does not fire on it. *)
Local Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Local Ltac zc G := zify_cond G; repeat (rewrite Z.mod_small in G by lia).

(** ---- list, byte and register facts ---- *)

Lemma firstn_S_nth : forall (A : Type) (l : list A) j d, (j < length l)%nat ->
  firstn (S j) l = firstn j l ++ [nth j l d].
Proof.
  intros A l. induction l as [|x l IH]; intros j d H; cbn in H; [lia|].
  destruct j as [|j]; [reflexivity|]. cbn [firstn nth app]. rewrite (IH j d) by lia. reflexivity.
Qed.

Lemma seven_bit_snoc : forall l x, seven_bit (l ++ [x]) = seven_bit l && negb (Z.testbit x 7).
Proof. intros l x. unfold seven_bit. rewrite forallb_app. cbn [forallb]. rewrite andb_true_r. reflexivity. Qed.

Lemma In_nth_firstn : forall (l : list Z) j n d, (j < n)%nat -> (j < length l)%nat -> In (nth j l d) (firstn n l).
Proof.
  induction l as [|x l IH]; intros j n d Hn Hl; cbn in Hl; [lia|].
  destruct n as [|n]; [lia|]. destruct j as [|j]; cbn [firstn nth]; [left; reflexivity | right; apply IH; lia].
Qed.

Lemma seven_bit_bad : forall l n j, (j < n)%nat -> (j < length l)%nat -> Z.testbit (nth j l 0) 7 = true ->
  seven_bit (firstn n l) = false.
Proof.
  intros l n j Hj Hl Ht. destruct (seven_bit (firstn n l)) eqn:E; [|reflexivity].
  unfold seven_bit in E. rewrite forallb_forall in E. specialize (E _ (In_nth_firstn l j n 0 Hj Hl)).
  rewrite Ht in E. discriminate E.
Qed.

Lemma zb_nth : forall l j, nth j (zb l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof. intros l j. exact (map_nth (fun b : byte => bv_unsigned b) l (Z_to_bv 8 0) j). Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma sxb_lts0 : forall b : byte, bv_lts (sxb b) (Z_to_bv 64 0) = Z.testbit (bv_unsigned b) 7.
Proof.
  intros b. rewrite bv_lts_zero_r. unfold sxb. pose proof (byte_range b) as Hb.
  rewrite tb7_byte by lia. rewrite unsigned_lit_wrap.
  unfold bv_signed, bv_swrap, bv_wrap.
  replace (bv_half_modulus 8) with 128 by reflexivity. replace (bv_modulus 8) with 256 by reflexivity.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 63) with 9223372036854775808.
  remember (bv_unsigned b) as u eqn:Eu. clear Eu.
  destruct (Z.ltb_spec 127 u) as [H|H].
  - rewrite <- (Z.mod_unique (u + 128) 256 1 (u - 128)) by lia.
    rewrite <- (Z.mod_unique (u - 128 - 128) 18446744073709551616 (-1) (u - 256 + 18446744073709551616)) by lia.
    apply Z.leb_le. lia.
  - rewrite (Z.mod_small (u + 128) 256) by lia.
    rewrite (Z.mod_small (u + 128 - 128) 18446744073709551616) by lia.
    apply Z.leb_gt. lia.
Qed.

Lemma firstn_len_app : forall (X : Type) (A B : list X) n, length A = n -> firstn n (A ++ B) = A.
Proof. intros X A B n <-. apply firstn_app_exact. Qed.

Lemma zxb_lit : forall x, 0 <= x < 256 -> zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  replace (bv_modulus 8) with 256 by reflexivity. apply Z.mod_small. lia.
Qed.

Lemma zx32_lit : forall v, 0 <= v < 2 ^ 32 -> zx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(** lw of an unsigned field in [2^31, 2^32): the register holds it sign-extended. *)
Lemma sx32_big : forall v, 2 ^ 31 <= v < 2 ^ 32 ->
  sx32 (Z_to_bv 64 v) = Z_to_bv 64 (v + 18446744069414584320).
Proof.
  intros v Hv. unfold sx32. rewrite (unsigned_lit v) by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (v + 18446744069414584320) (2 ^ 64)) by lia.
  replace ((v + 2 ^ 31) mod 2 ^ 32) with (v + 2 ^ 31 - 2 ^ 32) by (apply Z.mod_unique with 1; lia).
  symmetry. apply Z.mod_unique with (-1); lia.
Qed.

Lemma mod16_8 : forall x c, x mod 16 = 0 -> c mod 8 = 0 -> (x + c) mod 8 = 0.
Proof.
  intros x c Hx Hc. rewrite Z.add_mod by lia. rewrite Hc.
  assert (x mod 8 = 0).
  { pose proof (Z.div_mod x 16 ltac:(lia)) as D. rewrite Hx, Z.add_0_r in D. rewrite D.
    replace (16 * (x / 16)) with ((2 * (x / 16)) * 8) by lia. apply Z.mod_mul. lia. }
  rewrite H. reflexivity.
Qed.

(** want_key = (a & 0xffff) | 0x70000 (fuzz_codec.c:217) as the registers compute it. *)
Lemma key7_reg : forall a, 0 <= a < 2 ^ 32 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (zx32 (Z_to_bv 64 a))) 65535))) 458752)
  = Z_to_bv 64 (KEY 7 a).
Proof.
  intros a Ha. rewrite (zx32_lit a Ha). rewrite (unsigned_lit a) by lia.
  rewrite unsigned_lit by (pose proof (Z_land_range a 65535 ltac:(lia) ltac:(lia)); lia).
  unfold KEY. rewrite Z.lor_comm. reflexivity.
Qed.

(** The payload owe_sysex reads: pl[0] = a, pl[1] = 0, then the copied characters. *)
Lemma zb_pl : forall (x0 x1 : byte) a n bs, bv_unsigned x0 = u8 a -> bv_unsigned x1 = 0 ->
  zb ([x0; x1] ++ firstn n bs) = [u8 a; 0] ++ firstn n (zb bs).
Proof.
  intros x0 x1 a n bs H0 H1. unfold zb. rewrite map_app, firstn_map. cbn [map]. rewrite H0, H1.
  reflexivity.
Qed.

(** ---- the frame ---- *)

Lemma rw_cells_pick : forall m A cs (i : nat), rw_cells rsegs m A cs ->
  rw_cells rsegs m A (firstn i cs) /\ rw_cells rsegs m (A + Z.of_nat (cells_size (firstn i cs))) (skipn i cs).
Proof. intros m A cs i H. apply rw_cells_app_split. rewrite firstn_skipn. exact H. Qed.

(** Two adjacent byte blocks as one. *)
Lemma rw_cells_CB2 : forall m A n1 n2 l1 l2,
  rw_cells rsegs m A [CB n1 l1] -> rw_cells rsegs m (A + Z.of_nat n1) [CB n2 l2] ->
  rw_cells rsegs m A [CB (n1 + n2) (l1 ++ l2)].
Proof.
  intros m A n1 n2 l1 l2 H1 H2.
  pose proof H1 as [[W1 _] _]. pose proof H2 as [[W2 _] _].
  cbn [cells_wf cell_wf] in W1, W2. destruct W1 as [W1 _]. destruct W2 as [W2 _].
  apply (rw_cells_same_bytes m A ([CB n1 l1] ++ [CB n2 l2])).
  - cbn. split; [rewrite length_app; lia | exact I].
  - cbn. rewrite !app_nil_r. reflexivity.
  - cbn. lia.
  - apply rw_cells_app_join; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2.
Qed.

Ltac unfold_kc H :=
  unfold kcall_cells, k_run, with_rc, with_out in H;
  cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
       k_want_len k_want_key k_want_display] in H.

Ltac kproj := cbn [with_want_rc with_want_key set_want k_run with_rc with_out
                   k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
                   k_want_len k_want_key k_want_display].

(** ---- the record and the model ---- *)

Lemma desk9 : forall k, desk_at k -> k_desk k <> 0 ->
  exists d, od_of k = Some d /\ ((k_desk k = SDESK_C24 /\ d = c24) \/ (k_desk k = SDESK_PC /\ d = pc)).
Proof.
  intros k [[_ E]|[[_ E]|[_ E]]] H; [contradiction | exists c24 | exists pc];
    (split; [unfold od_of; rewrite E; reflexivity | auto]).
Qed.

(** d->device (offset 8) and d->chars (offset 10) of SPEC_C24 / SPEC_PC. *)
Lemma desk_rd9 : forall m2 k d, relro_img m2 ->
  ((k_desk k = SDESK_C24 /\ d = c24) \/ (k_desk k = SDESK_PC /\ d = pc)) ->
  ov_read_bytes rsegs m2 (Z_to_bv 64 (k_desk k + 8)) 1 = Some [Z_to_bv 8 (d_dev d)] /\
  ov_read_bytes rsegs m2 (Z_to_bv 64 (k_desk k + 10)) 1 = Some [Z_to_bv 8 (d_chars d)].
Proof.
  intros m2 k d HR [[E ->] | [E ->]]; rewrite E; unfold SDESK_C24, SDESK_PC.
  - pose proof (codec_SPEC_C24_at m2 HR) as DK. unfold codec_SPEC_C24_cells in DK. split.
    + exact (ro_cells_read_at rsegs m2 0x1f690 _ 8 (C1 (Z_to_bv 8 1)) 1 _ DK eq_refl eq_refl eq_refl).
    + exact (ro_cells_read_at rsegs m2 0x1f690 _ 10 (C1 (Z_to_bv 8 4)) 1 _ DK eq_refl eq_refl eq_refl).
  - pose proof (codec_SPEC_PC_at m2 HR) as DK. unfold codec_SPEC_PC_cells in DK. split.
    + exact (ro_cells_read_at rsegs m2 0x1f6a0 _ 8 (C1 (Z_to_bv 8 0)) 1 _ DK eq_refl eq_refl eq_refl).
    + exact (ro_cells_read_at rsegs m2 0x1f6a0 _ 10 (C1 (Z_to_bv 8 8)) 1 _ DK eq_refl eq_refl eq_refl).
Qed.

Lemma owe_k9 : forall k d, k_kind k = 9 -> od_of k = Some d ->
  owe_k k = if (0x7f <? k_a k) || negb (seven_bit (firstn (Z.to_nat (d_chars d)) (zb (k_bytes k))))
            then (E_RANGE, noc)
            else let '(bs, dp) := owe_sx (d_dev d) 0x40
                                    ([u8 (k_a k); 0] ++ firstn (Z.to_nat (d_chars d)) (zb (k_bytes k))) in
                 (0, (bs, KEY 7 (k_a k), dp)).
Proof. intros k d HK HO. unfold owe_k. rewrite HK, HO. reflexivity. Qed.

Lemma enc_rc9 : forall k d, rec_wf k -> od_of k = Some d -> (d = c24 \/ d = pc) ->
  fst (enc_k k) = fst (owe_k k).
Proof.
  intros k d (HK & _ & _ & _ & _ & _ & _ & _ & _ & HRD) HO Hd.
  assert (OD : od_ok (od_of k)) by (unfold od_ok; rewrite HO; destruct Hd as [-> | ->]; auto).
  pose proof (agree_all (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k)
                HK OD HRD) as A.
  unfold agrees in A. revert A. unfold enc_k, owe_k.
  destruct (enc_of_call (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k))
    as [rc o].
  intros [A _]. cbn [fst]. symmetry. exact A.
Qed.

Lemma desk_range : forall k, desk_at k -> 0 <= k_p k < 2 ^ 64 /\ 0 <= k_desk k < 2 ^ 64.
Proof.
  intros k [[E1 E2]|[[E1 E2]|[E1 E2]]]; rewrite E1, E2; unfold PERS, SDESK_C24, SDESK_PC; lia.
Qed.

(** The record owe_sysex is called with: k.rc is the encoder's code, 0 or E_RANGE. *)
Lemma kwf_run9 : forall k d, rec_wf k -> k_kind k = 9 -> od_of k = Some d -> (d = c24 \/ d = pc) ->
  kcall_wf (k_run k).
Proof.
  intros k d WF HK HO Hd.
  pose proof WF as (HK' & HDA & HBF & HOUT & HRC0 & HWRC0 & HWL0 & HWK0 & HWD0 & HRD).
  pose proof HRD as (Ra & Rb & Rc & Rdl & _ & _ & Rn & _).
  pose proof (desk_range k HDA) as [Rp Rd].
  pose proof (enc_rc9 k d WF HO Hd) as EC.
  assert (OR : fst (owe_k k) = 0 \/ fst (owe_k k) = E_RANGE).
  { rewrite (owe_k9 k d HK HO).
    lazymatch goal with |- context [if ?c then _ else _] => destruct c end; [right; reflexivity |].
    lazymatch goal with |- context [owe_sx ?x ?y ?z] => destruct (owe_sx x y z) end. left. reflexivity. }
  unfold kcall_wf. kproj. rewrite HK, HWRC0, HWL0, HWK0, HWD0, EC. unfold E_RANGE in OR. lia.
Qed.

Lemma chk_wf_err9 : forall k d, rec_wf k -> k_kind k = 9 -> od_of k = Some d -> (d = c24 \/ d = pc) ->
  (0x7f < k_a k \/ seven_bit (firstn (Z.to_nat (d_chars d)) (zb (k_bytes k))) = false) ->
  chk_wf (with_want_rc (k_run k) E_RANGE).
Proof.
  intros k d WF HK HO Hd Hbad.
  pose proof WF as (HK' & HDA & HBF & HOUT & HRC0 & HWRC0 & HWL0 & HWK0 & HWD0 & HRD).
  assert (OW : owe_k k = (E_RANGE, noc)).
  { rewrite (owe_k9 k d HK HO). destruct Hbad as [Hb | Hs].
    - replace (0x7f <? k_a k) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - rewrite Hs. rewrite orb_true_r. reflexivity. }
  pose proof (enc_rc9 k d WF HO Hd) as EC. rewrite OW in EC. cbn [fst] in EC.
  assert (E1 : enc_k (with_want_rc (k_run k) E_RANGE) = enc_k k) by reflexivity.
  assert (E2 : owe_k (with_want_rc (k_run k) E_RANGE) = owe_k k) by reflexivity.
  unfold chk_wf. rewrite E1, E2, OW. kproj.
  pose proof (desk_range k HDA) as [Rp Rd].
  pose proof HRD as (Ra & Rb & Rc & Rdl & _ & _ & Rn & _).
  split; [lia|]. split; [exact HDA|]. split.
  { unfold kcall_wf. kproj. rewrite HK, EC, HWL0, HWK0, HWD0. unfold E_RANGE. lia. }
  split; [exact HBF|]. split; [exact HRD|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. cbn [fst]. unfold E_RANGE. intros H. discriminate H.
Qed.

Lemma chk_wf_ok9 : forall k d w dp, rec_wf k -> k_kind k = 9 -> od_of k = Some d -> (d = c24 \/ d = pc) ->
  k_a k <= 0x7f -> seven_bit (firstn (Z.to_nat (d_chars d)) (zb (k_bytes k))) = true ->
  owe_sx (d_dev d) 64 ([u8 (k_a k); 0] ++ firstn (Z.to_nat (d_chars d)) (zb (k_bytes k))) = (w, dp) ->
  chk_wf (with_want_key (set_want (k_run k) (bz w ++ skipn (length w) (k_want k)) (Z.of_nat (length w)) dp)
                        (KEY 7 (k_a k))).
Proof.
  intros k d w dp WF HK HO Hd Ha H7 EW.
  pose proof WF as (HK' & HDA & HBF & HOUT & HRC0 & HWRC0 & HWL0 & HWK0 & HWD0 & HRD).
  pose proof HRD as (Ra & Rb & Rc & Rdl & Rlen & _ & Rn & _).
  assert (OW : owe_k k = (0, (w, KEY 7 (k_a k), dp))).
  { rewrite (owe_k9 k d HK HO).
    replace (0x7f <? k_a k) with false by (symmetry; apply Z.ltb_ge; lia). rewrite H7. cbn [orb negb].
    rewrite EW. reflexivity. }
  pose proof (enc_rc9 k d WF HO Hd) as EC. rewrite OW in EC. cbn [fst] in EC.
  assert (HCH : 4 <= d_chars d <= 8) by (destruct Hd as [-> | ->]; cbn; lia).
  pose proof (f_equal fst EW) as Ew. pose proof (f_equal snd EW) as Edp. cbn [fst snd] in Ew, Edp.
  unfold owe_sx in Ew, Edp. cbn [fst snd] in Ew, Edp.
  assert (LW : length w = (7 + Z.to_nat (d_chars d))%nat).
  { rewrite <- Ew. cbn [length app]. rewrite ?length_app, length_firstn, Rlen. cbn [length]. lia. }
  assert (DP : dp = 1) by (rewrite <- Edp; vm_compute; reflexivity).
  assert (E1 : enc_k (with_want_key (set_want (k_run k) (bz w ++ skipn (length w) (k_want k))
                                       (Z.of_nat (length w)) dp) (KEY 7 (k_a k))) = enc_k k)
    by reflexivity.
  assert (E2 : owe_k (with_want_key (set_want (k_run k) (bz w ++ skipn (length w) (k_want k))
                                       (Z.of_nat (length w)) dp) (KEY 7 (k_a k))) = owe_k k)
    by reflexivity.
  assert (KR : 0 <= KEY 7 (k_a k) < 2 ^ 32) by (apply KEY_range; lia).
  unfold chk_wf. rewrite E1, E2, OW. kproj.
  pose proof (desk_range k HDA) as [Rp Rd].
  split; [lia|]. split; [exact HDA|]. split.
  { unfold kcall_wf. kproj. rewrite HK, EC, HWRC0, LW, DP. lia. }
  split; [exact HBF|]. split; [exact HRD|]. split; [reflexivity|]. split; [reflexivity|].
  split; [cbn [fst]; exact HWRC0|]. intros _. cbn [snd].
  split; [apply firstn_len_app; unfold bz; apply length_map |].
  split; [reflexivity|]. split; [rewrite LW; lia|]. split; reflexivity.
Qed.

(** ---- the machine state of the segment ---- *)

Definition st9 (E : cenv) (ks : Z) (ra' t0' t1' t2' a0 a1 a2 a3 a4 a5 a6 a7 s5' t3' t4' t5' t6' : word)
  (ops pcv : Z) (m1 : word -> option byte) : machine_state :=
  MS (mkR ra' (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) (c_gp E) (c_tp E) t0' t1' t2'
          (Z_to_bv 64 (bv_unsigned (c_sp E) + -308)) (Z_to_bv 64 0x1f678)
          a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 0x104d4) (Z_to_bv 64 254) (Z_to_bv 64 18446744073709422983)
          s5' (Z_to_bv 64 ops) (Z_to_bv 64 ks) (Z_to_bv 64 (bv_unsigned (c_sp E) + -216)) (Z_to_bv 64 1)
          (Z_to_bv 64 18446744073709484843) (Z_to_bv 64 10) t3' t4' t5' t6')
     (c_F E) (Z_to_bv 64 pcv) (c_fc E) None m1 (seg_rom rsegs).

Lemma codec_main_owe9 : seg_owe9_stmt.
Proof.
  unfold seg_owe9_stmt.
  intros E n ENV MEMCPY OSX CHK k WF K9.
  unfold owe_sysex_contract, owe_sysex_pre, OWE_SYSEX, OWE_SYSEX_DEPTH in OSX.
  unfold owe_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s5' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
    _ ND HN HOPS HCUR HC0 HREM FR ST MU WM HMI.
  destruct (ND ltac:(rewrite K9; reflexivity)) as [-> HD0]. clear ND.
  rewrite K9. change (pc_owe 9) with 0x145d0.
  pose proof (bv_unsigned_in_range 64 (c_sp E)) as Rsp. unfold bv_modulus in Rsp.
  pose proof ENV as (_ & _ & _ & HLO & SPA & _).
  pose proof ST as (Hlo0 & _).
  unfold fr in FR. destruct FR as (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV). clear HS.
  pose proof WF as (HK & HDA & HBF & HOUT & HRC0 & HWRC0 & HWL0 & HWK0 & HWD0 & HRD).
  pose proof HRD as (Ra & Rb & Rc & Rd & Rlen & _ & Rn & _).
  assert (LBY : length (k_bytes k) = 24%nat) by (unfold zb in Rlen; rewrite length_map in Rlen; exact Rlen).
  destruct (desk9 k HDA HD0) as (d & HOD & HDK).
  assert (Hd : d = c24 \/ d = pc) by (destruct HDK as [[_ ->] | [_ ->]]; auto).
  assert (HDV : 0 <= d_dev d < 2) by (destruct Hd as [-> | ->]; cbn; lia).
  assert (HCH : 4 <= d_chars d <= 8) by (destruct Hd as [-> | ->]; cbn; lia).
  assert (LAND7 : Z.land (k_desk k) 7 = 0) by (destruct HDK as [[-> _] | [-> _]]; reflexivity).
  assert (KDR : 0 <= k_desk k < 2 ^ 63) by (destruct HDK as [[-> _] | [-> _]]; unfold SDESK_C24, SDESK_PC; lia).
  assert (UDK : bv_unsigned (Z_to_bv 64 (k_desk k)) = k_desk k) by (apply unsigned_lit; lia).
  assert (U416 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) = bv_unsigned (c_sp E) + -416)
    by (apply unsigned_lit; lia).
  assert (U384 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -384)) = bv_unsigned (c_sp E) + -384)
    by (apply unsigned_lit; lia).
  assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -344)) = bv_unsigned (c_sp E) + -344)
    by (apply unsigned_lit; lia).
  assert (U114 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -114)) = bv_unsigned (c_sp E) + -114)
    by (apply unsigned_lit; lia).
  assert (U112 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -112)) = bv_unsigned (c_sp E) + -112)
    by (apply unsigned_lit; lia).
  assert (UCH : bv_unsigned (Z_to_bv 64 (d_chars d)) = d_chars d) by (apply unsigned_lit; lia).
  pose proof (kwf_run9 k d WF K9 HOD Hd) as KWF.
  unfold_kc FK.
  assert (BY : bytes_at rsegs m1 (bv_unsigned (c_sp E) + -344) (k_bytes k)).
  { pose proof (rw_cells_pick _ _ _ 8 FK) as [_ X]. cbn [firstn skipn cells_size csize Nat.add] in X.
    apply rw_cells_app_split with (cs1 := [CB 24 (k_bytes k)]) in X. destruct X as [X _].
    apply rw_cells_bytes_at in X.
    replace (bv_unsigned (c_sp E) + -344) with (bv_unsigned (c_sp E) + -384 + Z.of_nat 40) by lia.
    exact X. }
  (* 0x14a2c-0x14a30: want_rc = E_RANGE, then the checks *)
  assert (ERANGE : forall a0v a1v a2v a3v a4v a7v s5v,
    (0x7f < k_a k \/ seven_bit (firstn (Z.to_nat (d_chars d)) (zb (k_bytes k))) = false) ->
    evt rsegs (Qk E) (st9 E (k_desk k) ra' t0' t1' t2' a0v a1v a2v a3v a4v a5' a6' a7v s5v
                         t3' t4' t5' t6' ops 0x14a2c m1)).
  { intros a0v a1v a2v a3v a4v a7v s5v Hbad. clear BY. unfold st9. step. step.
    eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (with_want_rc (k_run k) E_RANGE) cur rem u0 pj tj plj c ops);
      [ exact (chk_wf_err9 k d WF K9 HOD Hd Hbad) | exact HN | exact HOPS | exact HCUR | exact HC0 | exact HREM
      | | eassumption | eassumption | eassumption | eassumption ].
    exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))). }
  (* 0x1461c-0x14684, 0x14a00-0x14a08: pl[], memcpy, owe_sysex, want_key, then the checks *)
  assert (AFTER : forall a0v a2v a3v a4v, k_a k <= 0x7f ->
    seven_bit (firstn (Z.to_nat (d_chars d)) (zb (k_bytes k))) = true ->
    evt rsegs (Qk E) (st9 E (k_desk k) ra' t0' t1' t2' a0v (Z_to_bv 64 (k_a k)) a2v a3v a4v a5' a6'
                         (Z_to_bv 64 (bv_unsigned (c_sp E) + -114)) (Z_to_bv 64 (d_chars d))
                         t3' t4' t5' t6' ops 0x1461c m1)).
  { intros a0v a2v a3v a4v Ha H7.
    unfold st9. do 10 step.
    (* pl[0] = a, pl[1..9] = 0, as [CB 2 _] at sp - 114 and [CB 8 _] at sp - 112 *)
    lazymatch type of FPL with rw_cells _ ?mm ?A ?l =>
      pose proof (rw_cells_merge rsegs mm A [] l [] FPL) as PL1 end.
    clear FPL. cbn [app cells_size cells_bytes csize cbytes Nat.add firstn skipn] in PL1.
    lazymatch type of PL1 with rw_cells _ ?mm ?A [CB _ ?bs] =>
      pose proof (rw_cells_CB_split mm A 10 2 bs eq_refl ltac:(lia) PL1) as [PLa PLb] end.
    clear PL1. cbn [firstn skipn Nat.sub] in PLa, PLb.
    replace (bv_unsigned (c_sp E) + -114 + Z.of_nat 2) with (bv_unsigned (c_sp E) + -112) in PLb by lia.
    lazymatch type of PLb with rw_cells _ _ _ [CB _ ?l] => remember l as L8 eqn:EL8 end.
    assert (LL8 : length L8 = 8%nat) by (rewrite EL8; reflexivity).
    lazymatch type of PLa with rw_cells _ _ _ [CB _ [?y0; ?y1]] =>
      remember y0 as x0 eqn:Ex0; remember y1 as x1 eqn:Ex1 end.
    assert (BX0 : bv_unsigned x0 = u8 (k_a k)).
    { rewrite Ex0. rewrite unsigned_lit by lia. rewrite Z_to_bv_unsigned. reflexivity. }
    assert (BX1 : bv_unsigned x1 = 0) by (rewrite Ex1; reflexivity).
    pose proof (rw_cells_CB_split _ _ 8 (Z.to_nat (d_chars d)) L8 LL8 ltac:(lia) PLb) as [PLb1 PLb2].
    clear PLb.
    (* 0x14644-0x14648: the pointer trap on pl + 2 *)
    step. step. if_cases T; [refute_trap T|].
    (* 0x1464c-0x14658: memcpy(pl + 2, k.bytes, d->chars) *)
    step. step. step. step.
    lazymatch type of PLb1 with rw_cells _ _ _ [CB _ ?junk] =>
      call (MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (firstn (Z.to_nat (d_chars d)) (k_bytes k)) junk) end.
    1: (rewrite U344; rewrite <- (firstn_skipn (Z.to_nat (d_chars d)) (k_bytes k)) in BY;
        apply bytes_at_app in BY; exact (proj1 BY)).
    1: (rewrite UCH, length_firstn, LBY; lia).
    1: (rewrite U112, UCH; exact PLb1).
    1: (rewrite U344, U112, UCH; lia).
    1: assumption.
    match goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => rename H into PLc end.
    rewrite U112, UCH in PLc. try clear POST.
    (* 0x1465c-0x14670: owe_sysex(&k, d->device, 0x40, pl, d->chars + 2) *)
    pose proof (desk_rd9 _ k d (relro_at E _ ENV MU) HDK) as [HDEV _].
    step. clear HDEV.
    step. step. step. step. step.
    call (OSX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (c_lo E) (d_dev d) 64 (k_run k) ([x0; x1] ++ firstn (Z.to_nat (d_chars d)) (k_bytes k))).
    { rewrite ?U416, ?U384, ?U114, ?UCH.
      assert (LPL : length ([x0; x1] ++ firstn (Z.to_nat (d_chars d)) (k_bytes k))
                    = (2 + Z.to_nat (d_chars d))%nat)
        by (rewrite length_app, length_firstn, LBY; cbn [length]; lia).
      refine (conj FK (conj KWF (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
               (conj _ (conj _ (conj ST _))))))))))))).
      - apply mod16_8; [exact SPA | reflexivity].
      - split; [lia | apply zxb_lit; lia].
      - split; [lia | reflexivity].
      - apply bytes_at_app. split; [exact (rw_cells_bytes_at _ _ _ _ PLa) |].
        cbn [length]. replace (bv_unsigned (c_sp E) + -114 + Z.of_nat 2) with (bv_unsigned (c_sp E) + -112) by lia.
        exact (rw_cells_bytes_at _ _ _ _ PLc).
      - rewrite LPL. rewrite unsigned_lit by lia. lia.
      - rewrite LPL. lia.
      - rewrite LPL. unfold disj. lia.
      - lia.
      - lia.
      - assumption.
      - lia. }
    rewrite ?U416 in *.
    rewrite (zb_pl x0 x1 (k_a k) (Z.to_nat (d_chars d)) (k_bytes k) BX0 BX1) in POST.
    revert POST.
    destruct (owe_sx (d_dev d) 64 ([u8 (k_a k); 0] ++ firstn (Z.to_nat (d_chars d)) (zb (k_bytes k))))
      as [w dp] eqn:EW.
    intros POST. cbv beta iota in POST.
    rewrite U384 in POST.
    unfold kcall_cells, set_want, k_run, with_rc, with_out in POST.
    cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
         k_want_len k_want_key k_want_display] in POST.
    (* 0x14674-0x14684, 0x14a00-0x14a08: want_key = (a & 0xffff) | 0x70000 *)
    step. step. step. step. step. step.
    rewrite (key7_reg (k_a k)) by lia.
    step. step.
    (* pl[] back as one block *)
    pose proof (rw_cells_CB2 _ _ _ _ _ _ PLc PLb2) as PL8.
    replace (Z.to_nat (d_chars d) + (8 - Z.to_nat (d_chars d)))%nat with 8%nat in PL8 by lia.
    replace (bv_unsigned (c_sp E) + -112) with (bv_unsigned (c_sp E) + -114 + Z.of_nat 2) in PL8 by lia.
    pose proof (rw_cells_CB2 _ _ _ _ _ _ PLa PL8) as PLR. cbn [Nat.add] in PLR.
    eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (with_want_key (set_want (k_run k) (bz w ++ skipn (length w) (k_want k)) (Z.of_nat (length w)) dp)
                 (KEY 7 (k_a k))) cur rem u0 pj tj _ c ops);
      [ exact (chk_wf_ok9 k d w dp WF K9 HOD Hd Ha H7 EW) | exact HN | exact HOPS | exact HCUR | exact HC0
      | exact HREM | | eassumption | eassumption | eassumption | eassumption ].
    exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj POST (conj FIN (conj FPD (conj FTX
             (conj PLR FSV)))))))). }
  (* 0x14600-0x14618: seven_bit(k->bytes, d->chars) *)
  assert (LOOP1 : forall (dd j : nat) (a0v a2v a3v a4v : word),
    dd = (Z.to_nat (d_chars d) - j)%nat -> (j < Z.to_nat (d_chars d))%nat -> k_a k <= 0x7f ->
    bv_unsigned a0v = bv_unsigned (c_sp E) + -344 + Z.of_nat j ->
    bv_unsigned a2v = d_chars d - Z.of_nat j ->
    bv_unsigned a3v = bv_unsigned (c_sp E) + -344 + Z.of_nat j ->
    seven_bit (firstn j (zb (k_bytes k))) = true ->
    evt rsegs (Qk E) (st9 E (k_desk k) ra' t0' t1' t2' a0v (Z_to_bv 64 (k_a k)) a2v a3v a4v a5' a6'
                         (Z_to_bv 64 (bv_unsigned (c_sp E) + -114)) (Z_to_bv 64 (d_chars d))
                         t3' t4' t5' t6' ops 0x14600 m1)).
  { induction dd as [|dd IH]; intros j a0v a2v a3v a4v Hdd Hj Ha HA0 HA2 HA3 H7; [lia|].
    pose proof (bytes_at_byte m1 (bv_unsigned (c_sp E) + -344) (k_bytes k) (Z.of_nat j) BY
                  ltac:(rewrite LBY; lia)) as HR.
    rewrite Nat2Z.id in HR.
    rewrite (wa_of_var a0v (bv_unsigned (c_sp E) + -344 + Z.of_nat j) ltac:(lia)) in HR.
    unfold st9. step.
    if_cases T; [refute_trap T|].
    step. step.
    if_cases G.
    - rewrite sxb_lts0 in G. apply ERANGE. right.
      apply (seven_bit_bad _ (Z.to_nat (d_chars d)) j);
        [lia | unfold zb; rewrite length_map; lia | rewrite zb_nth; exact G].
    - rewrite sxb_lts0 in G. step. step. step. step.
      if_cases G2.
      + zc G2. eapply (IH (S j)); [lia | lia | exact Ha | rewrite unsigned_lit by lia; lia
          | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | ].
        rewrite (firstn_S_nth _ _ j 0) by (unfold zb; rewrite length_map; lia).
        rewrite seven_bit_snoc, H7, zb_nth, G. reflexivity.
      + zc G2. assert (j = Z.to_nat (d_chars d) - 1)%nat by lia. subst j. apply AFTER; [exact Ha|].
        replace (Z.to_nat (d_chars d)) with (S (Z.to_nat (d_chars d) - 1)) at 1 by lia.
        rewrite (firstn_S_nth _ _ _ 0) by (unfold zb; rewrite length_map; lia).
        rewrite seven_bit_snoc, H7, zb_nth, G. reflexivity. }
  (* 0x145d0-0x145fc: the range test, the alignment trap, d->chars *)
  step.
  destruct (Z.ltb_spec (k_a k) (2 ^ 31)) as [HA31 | HA31].
  2: { rewrite (sx32_big (k_a k)) by lia. step. step.
       if_cases G1; [ apply ERANGE; left; lia | exfalso; zc G1; lia ]. }
  rewrite (sx32_small (k_a k)) by lia. step. step.
  if_cases G1.
  { zc G1. apply ERANGE. left. lia. }
  zc G1.
  step. rewrite UDK, LAND7. step.
  replace (v_sltiu (Z_to_bv 64 0) 1) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
  step. step.
  if_cases T; [refute_trap T|].
  pose proof (desk_rd9 m1 k d (relro_at E m1 ENV MU) HDK) as [_ HCHR].
  step. clear HCHR.
  replace (zxb (Z_to_bv 8 (d_chars d))) with (Z_to_bv 64 (d_chars d)) by (symmetry; apply zxb_lit; lia).
  step. step. step. step.
  if_cases T2; [refute_trap T2|].
  apply (LOOP1 (Z.to_nat (d_chars d)) 0%nat);
    [ lia | lia | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; lia | reflexivity ].
Qed.
