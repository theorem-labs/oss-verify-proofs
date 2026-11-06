(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootLayout.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLin AxEntryRel AsanWEntry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition enc (inp : ProcInput) (sp : word) (draw : EntryDraw) (ρ0 : valuation) : valuation :=
  fun v =>
    let z := to_Z v in
    let av := in_argv inp in
    let ev := in_envp inp in
    let s := bv_unsigned sp in
    let R := bv_unsigned (ed_random draw) in
    if z =? 0 then (s / 16) mod 4
    else if z =? 1 then (s / 64) mod 64
    else if z =? 2 then (s / 4096) mod 8
    else if z =? 3 then s / 32768
    else if z =? 5 then R mod 2 ^ 64
    else if z =? 6 then R / 2 ^ 64
    else if z =? 7 then bv_unsigned (in_hwcap inp)
    else if z =? 8 then bv_unsigned (in_uid inp)
    else if z =? 9 then Z.of_nat (length av)
    else if z =? 10 then Z.of_nat (length ev)
    else if z =? 11 then total_arg_bytes av
    else if z =? 12 then total_arg_bytes ev
    else if z =? 13 then (total_arg_bytes av + total_arg_bytes ev + 7) / 8
    else if (2 ^ 40 <=? z) && (z <? 2 ^ 41) then
      bv_unsigned (nth (Z.to_nat ((z - 2 ^ 40) mod 2 ^ 17)) (nth (Z.to_nat ((z - 2 ^ 40) / 2 ^ 17)) av []) (Z_to_bv 8 0))
    else if (2 ^ 41 <=? z) && (z <? 2 ^ 42) then Z.of_nat (length (nth (Z.to_nat (z - 2 ^ 41)) av []))
    else if (2 ^ 42 <=? z) && (z <? 2 ^ 42 + 2 ^ 20) then Z.of_nat (length (nth (Z.to_nat (z - 2 ^ 42)) ev []))
    else if (2 ^ 42 + 2 ^ 20 <=? z) && (z <? 2 ^ 43) then
      bv_unsigned (nth (Z.to_nat ((z - 2 ^ 42 - 2 ^ 20) mod 2 ^ 17))
                       (nth (Z.to_nat ((z - 2 ^ 42 - 2 ^ 20) / 2 ^ 17)) ev []) (Z_to_bv 8 0))
    else ρ0 v.

(* [comment removed for export] *)
Local Ltac zbool :=
  repeat match goal with
  | |- context [?a =? ?b] => first [ rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia ]
  | |- context [?a <=? ?b] => first [ rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia ]
  | |- context [?a <? ?b] => first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
  end; cbn [andb orb].

Section Enc.
Variables (inp : ProcInput) (sp : word) (draw : EntryDraw) (ρ0 : valuation).
Let ρ := enc inp sp draw ρ0.
Let av := in_argv inp.
Let ev := in_envp inp.

Lemma enc_x0 : ρ v_x0 = (bv_unsigned sp / 16) mod 4. Proof. reflexivity. Qed.
Lemma enc_x1 : ρ v_x1 = (bv_unsigned sp / 64) mod 64. Proof. reflexivity. Qed.
Lemma enc_x2 : ρ v_x2 = (bv_unsigned sp / 4096) mod 8. Proof. reflexivity. Qed.
Lemma enc_x3 : ρ v_x3 = bv_unsigned sp / 32768. Proof. reflexivity. Qed.
Lemma enc_r0 : ρ v_r0 = bv_unsigned (ed_random draw) mod 2 ^ 64. Proof. reflexivity. Qed.
Lemma enc_r1 : ρ v_r1 = bv_unsigned (ed_random draw) / 2 ^ 64. Proof. reflexivity. Qed.
Lemma enc_hw : ρ v_hw = bv_unsigned (in_hwcap inp). Proof. reflexivity. Qed.
Lemma enc_uid : ρ v_uid = bv_unsigned (in_uid inp). Proof. reflexivity. Qed.
Lemma enc_argc : ρ v_argc = Z.of_nat (length av). Proof. reflexivity. Qed.
Lemma enc_envc : ρ v_envc = Z.of_nat (length ev). Proof. reflexivity. Qed.
Lemma enc_ta : ρ v_ta = total_arg_bytes av. Proof. reflexivity. Qed.
Lemma enc_te : ρ v_te = total_arg_bytes ev. Proof. reflexivity. Qed.
Lemma enc_q : ρ v_q = (total_arg_bytes av + total_arg_bytes ev + 7) / 8. Proof. reflexivity. Qed.

Lemma to_Z_of_small : forall z, 0 <= z < 2 ^ 63 -> to_Z (of_Z z) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small. change wB with (2 ^ 63). lia. Qed.

Lemma div_mod17 : forall k j, 0 <= k -> 0 <= j < 2 ^ 17 -> (k * 2 ^ 17 + j) / 2 ^ 17 = k /\ (k * 2 ^ 17 + j) mod 2 ^ 17 = j.
Proof.
  intros k j Hk Hj. split.
  - rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  - rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma enc_lenvar : forall k, 0 <= k < 2 ^ 20 -> ρ (lenvar k) = Z.of_nat (length (nth (Z.to_nat k) av [])).
Proof.
  intros k Hk. unfold ρ, enc, lenvar. rewrite to_Z_of_small by lia. cbv zeta. zbool.
  replace (2 ^ 41 + k - 2 ^ 41) with k by lia. reflexivity.
Qed.

Lemma enc_elenvar : forall k, 0 <= k < 2 ^ 20 -> ρ (elenvar k) = Z.of_nat (length (nth (Z.to_nat k) ev [])).
Proof.
  intros k Hk. unfold ρ, enc, elenvar. rewrite to_Z_of_small by lia. cbv zeta. zbool.
  replace (2 ^ 42 + k - 2 ^ 42) with k by lia. reflexivity.
Qed.

Lemma enc_strvar : forall k j, 0 <= k < 2 ^ 20 -> 0 <= j < 2 ^ 17 ->
  ρ (strvar k j) = bv_unsigned (nth (Z.to_nat j) (nth (Z.to_nat k) av []) (Z_to_bv 8 0)).
Proof.
  intros k j Hk Hj. unfold ρ, enc, strvar. rewrite to_Z_of_small by lia. cbv zeta. zbool.
  replace (2 ^ 40 + k * 2 ^ 17 + j - 2 ^ 40) with (k * 2 ^ 17 + j) by lia.
  destruct (div_mod17 k j ltac:(lia) Hj) as [E1 E2]. rewrite E1, E2. reflexivity.
Qed.

Lemma enc_estrvar : forall k j, 0 <= k < 2 ^ 20 -> 0 <= j < 2 ^ 17 ->
  ρ (estrvar k j) = bv_unsigned (nth (Z.to_nat j) (nth (Z.to_nat k) ev []) (Z_to_bv 8 0)).
Proof.
  intros k j Hk Hj. unfold ρ, enc, estrvar. rewrite to_Z_of_small by lia. cbv zeta. zbool.
  replace (2 ^ 42 + 2 ^ 20 + k * 2 ^ 17 + j - 2 ^ 42 - 2 ^ 20) with (k * 2 ^ 17 + j) by lia.
  destruct (div_mod17 k j ltac:(lia) Hj) as [E1 E2]. rewrite E1, E2. reflexivity.
Qed.

End Enc.

Lemma nth_map_seq0 : forall {A} (f : nat -> A) (n k : nat) (d : A), (k < n)%nat -> nth k (map f (seq 0 n)) d = f k.
Proof.
  intros A f n k d Hk. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hk).
  rewrite map_nth, seq_nth by exact Hk. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma map_seq_nth : forall {A} (l : list A) (d : A) (f : nat -> A),
  (forall i, (i < length l)%nat -> f i = nth i l d) -> map f (seq 0 (length l)) = l.
Proof.
  intros A l d f Hf. apply (nth_ext _ _ d d).
  - rewrite length_map, length_seq. reflexivity.
  - intros i Hi. rewrite length_map, length_seq in Hi.
    rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
    rewrite map_nth, seq_nth by exact Hi. cbn [Nat.add]. apply Hf. exact Hi.
Qed.

Lemma u8_roundtrip : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply Z_to_bv_bv_unsigned. Qed.

Lemma nth_Forall : forall {A} (P : A -> Prop) (l : list A) (d : A) i, Forall P l -> (i < length l)%nat -> P (nth i l d).
Proof. intros A P l d i H Hi. rewrite Forall_forall in H. apply H. apply nth_In. exact Hi. Qed.

Lemma dec_strs_enc : forall (L : list (list byte)) (ρ : valuation) (cnt : int) (len : Z -> int) (bytev : Z -> Z -> int),
  ρ cnt = Z.of_nat (length L) ->
  (forall k, (k < length L)%nat -> ρ (len (Z.of_nat k)) = Z.of_nat (length (nth k L []))) ->
  (forall k j, (k < length L)%nat -> (j < length (nth k L []))%nat ->
     ρ (bytev (Z.of_nat k) (Z.of_nat j)) = bv_unsigned (nth j (nth k L []) (Z_to_bv 8 0))) ->
  dec_strs ρ cnt len bytev = L.
Proof.
  intros L ρ cnt len bytev Hc Hl Hb. unfold dec_strs. rewrite Hc, Nat2Z.id.
  apply (map_seq_nth L []). intros k Hk. rewrite Hl, Nat2Z.id by exact Hk.
  apply (map_seq_nth (nth k L []) (Z_to_bv 8 0)). intros j Hj. rewrite Hb by assumption. apply u8_roundtrip.
Qed.

Lemma dec_argv_enc : forall inp sp draw ρ0, valid_argv (in_argv inp) -> dec_argv (enc inp sp draw ρ0) = in_argv inp.
Proof.
  intros inp sp draw ρ0 ([H1 H2] & _ & H3 & _). unfold dec_argv. apply dec_strs_enc.
  - apply enc_argc.
  - intros k Hk. rewrite enc_lenvar by lia. rewrite Nat2Z.id. reflexivity.
  - intros k j Hk Hj. pose proof (nth_Forall _ _ [] k H3 Hk) as HL. cbn beta in HL.
    rewrite enc_strvar by lia. rewrite !Nat2Z.id. reflexivity.
Qed.

Lemma dec_envp_enc : forall inp sp draw ρ0, valid_envp (in_envp inp) -> dec_envp (enc inp sp draw ρ0) = in_envp inp.
Proof.
  intros inp sp draw ρ0 (H1 & _ & H3 & _). unfold dec_envp. apply dec_strs_enc.
  - apply enc_envc.
  - intros k Hk. rewrite enc_elenvar by lia. rewrite Nat2Z.id. reflexivity.
  - intros k j Hk Hj. pose proof (nth_Forall _ _ [] k H3 Hk) as HL. cbn beta in HL.
    rewrite enc_estrvar by lia. rewrite !Nat2Z.id. reflexivity.
Qed.

Lemma sp_val_enc : forall inp sp draw ρ0, bv_unsigned sp mod 16 = 0 -> sp_val (enc inp sp draw ρ0) = bv_unsigned sp.
Proof.
  intros inp sp draw ρ0 H16. unfold sp_val, sp_terms. cbn [teval].
  rewrite enc_x0, enc_x1, enc_x2, enc_x3. set (s := bv_unsigned sp) in *. pose proof (u64_range sp) as Hs. fold s in Hs.
  pose proof (Z.div_mod s 16 ltac:(lia)) as D1. rewrite H16 in D1.
  pose proof (Z.div_mod (s / 16) 4 ltac:(lia)) as D2. rewrite Z.div_div in D2 by lia.
  pose proof (Z.div_mod (s / 64) 64 ltac:(lia)) as D3. rewrite Z.div_div in D3 by lia.
  pose proof (Z.div_mod (s / 4096) 8 ltac:(lia)) as D4. rewrite Z.div_div in D4 by lia.
  change (16 * 4) with 64 in D2. change (64 * 64) with 4096 in D3. change (4096 * 8) with 32768 in D4. lia.
Qed.

Lemma ed_random_enc : forall inp sp draw ρ0, ed_random (dec_draw (enc inp sp draw ρ0)) = ed_random draw.
Proof.
  intros inp sp draw ρ0. cbn [dec_draw ed_random]. unfold dec_random. rewrite enc_r0, enc_r1.
  pose proof (bv_unsigned_in_range _ (ed_random draw)) as HR. change (bv_modulus 128) with (2 ^ 128) in HR.
  set (R := bv_unsigned (ed_random draw)) in *.
  rewrite Z.mod_mod by lia. rewrite (Z.mod_small (R / 2 ^ 64) (2 ^ 64)).
  2:{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 64 * 2 ^ 64) with (2 ^ 128). lia. }
  rewrite Z.add_comm, <- Z.div_mod by lia. unfold R. apply Z_to_bv_bv_unsigned.
Qed.

Lemma uid_enc : forall inp sp draw ρ0, Z_to_bv 64 (enc inp sp draw ρ0 v_uid) = in_uid inp.
Proof. intros. rewrite enc_uid. apply Z_to_bv_bv_unsigned. Qed.

Lemma hw_enc : forall inp sp draw ρ0, Z_to_bv 64 (enc inp sp draw ρ0 v_hw) = in_hwcap inp.
Proof. intros. rewrite enc_hw. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Lemma bsb_draw : forall ph sp av ev uid hw d1 d2, ed_random d1 = ed_random d2 ->
  build_stack_bytes ph sp av ev uid hw d1 = build_stack_bytes ph sp av ev uid hw d2.
Proof. intros ph sp av ev uid hw d1 d2 E. unfold build_stack_bytes. rewrite E. reflexivity. Qed.

Lemma eb_image_enc : forall ph inp sp draw ρ0, valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  bv_unsigned sp mod 16 = 0 ->
  eb_image ph (enc inp sp draw ρ0) = build_stack_bytes ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw.
Proof.
  intros ph inp sp draw ρ0 Ha He H16. unfold eb_image.
  rewrite dec_argv_enc, dec_envp_enc, sp_val_enc, uid_enc, hw_enc by assumption. rewrite Z_to_bv_bv_unsigned.
  apply bsb_draw. apply ed_random_enc.
Qed.

(* [comment removed for export] *)
Lemma ROn_span : forall av ev, (Z.of_nat (ROn av ev) + 16 <= entry_stack_span av ev)%Z.
Proof.
  intros av ev. unfold ROn, SBn, entry_stack_span, auxv_size. rewrite !tab_Z.
  pose proof (Nat.div_mod (tab av + tab ev + 7) 8 ltac:(lia)). pose proof (Nat.mod_upper_bound (tab av + tab ev + 7) 8 ltac:(lia)).
  lia.
Qed.

Lemma length_eb_image : forall ph ρ, Z.of_nat (length (eb_image ph ρ)) = Z.of_nat (ROn (dec_argv ρ) (dec_envp ρ)) + 16.
Proof. intros ph ρ. unfold eb_image. rewrite E0_length. lia. Qed.

Lemma eb_facts_enc : forall inp sp draw ρ0, valid_input inp -> valid_sp sp -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  eb_facts (enc inp sp draw ρ0).
Proof.
  intros inp sp draw ρ0 Hv Hsp Hfit.
  destruct Hv as (Ha & He & _ & _ & Hcred & _).  (* [comment removed for export] *)
  pose proof Ha as Ha'. pose proof He as He'.
  destruct Ha as ([Ha1 Ha2] & _ & Ha3 & Ha4 & _). destruct He as (He1 & _ & He3 & He4).
  destruct Hsp as (Hs1 & Hs2 & Hs3).
  pose proof (bv_unsigned_in_range _ (ed_random draw)) as HR. change (bv_modulus 128) with (2 ^ 128) in HR.
  unfold eb_facts.
  rewrite (dec_argv_enc inp sp draw ρ0 Ha'), (dec_envp_enc inp sp draw ρ0 He'), (sp_val_enc inp sp draw ρ0 Hs3).
  rewrite enc_argc, enc_envc, enc_ta, enc_te, enc_q, enc_r0, enc_r1, enc_uid, enc_hw.
  split; [lia|]. split; [lia|]. split; [|split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]]].
  - intros k Hk. assert (Hk' : (Z.to_nat k < length (in_argv inp))%nat) by lia.
    pose proof (nth_Forall _ _ [] _ Ha3 Hk') as HL. cbn beta in HL.
    rewrite enc_lenvar by lia. split; [lia|].
    intros j Hj. rewrite enc_strvar by lia. set (b := nth (Z.to_nat j) (nth (Z.to_nat k) (in_argv inp) []) (Z_to_bv 8 0)).
    pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
    assert (Hnz : b <> Z_to_bv 8 0).
    { intros E. pose proof (nth_Forall _ _ [] _ Ha4 Hk') as HN. cbn beta in HN. apply HN. rewrite <- E. apply nth_In. lia. }
    assert (bv_unsigned b <> 0).
    { intros E. apply Hnz. apply bv_eq. rewrite E. reflexivity. }
    lia.
  - intros k Hk. assert (Hk' : (Z.to_nat k < length (in_envp inp))%nat) by lia.
    pose proof (nth_Forall _ _ [] _ He3 Hk') as HL. cbn beta in HL.
    rewrite enc_elenvar by lia. split; [lia|].
    intros j Hj. rewrite enc_estrvar by lia. set (b := nth (Z.to_nat j) (nth (Z.to_nat k) (in_envp inp) []) (Z_to_bv 8 0)).
    pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
    assert (Hnz : b <> Z_to_bv 8 0).
    { intros E. pose proof (nth_Forall _ _ [] _ He4 Hk') as HN. cbn beta in HN. apply HN. rewrite <- E. apply nth_In. lia. }
    assert (bv_unsigned b <> 0).
    { intros E. apply Hnz. apply bv_eq. rewrite E. reflexivity. }
    lia.
  - split; [apply Z.mod_pos_bound; lia|]. split.
    + split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 64 * 2 ^ 64) with (2 ^ 128). lia.
    + split; [unfold valid_creds, valid_id in Hcred; pose proof (u64_range (in_uid inp)); lia|].
      split; [apply u64_range|]. split; [lia|].
      rewrite length_eb_image, (dec_argv_enc inp sp draw ρ0 Ha'), (dec_envp_enc inp sp draw ρ0 He').
      pose proof (ROn_span (in_argv inp) (in_envp inp)). unfold entry_stack_fits in Hfit. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem eb_rel_init : forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp : word) (draw : EntryDraw)
                              (inp : ProcInput) (ρ0 : valuation),
  valid_input inp -> valid_sp sp -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  eb_rel ph (enc inp sp draw ρ0)
    (ms_mem (init_machine_state segs pc ph sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)))
    (bv_unsigned sp) 2238672.
Proof.
  intros segs pc ph sp draw inp ρ0 Hv Hsp Hfit.
  pose proof (eb_facts_enc inp sp draw ρ0 Hv Hsp Hfit) as HF.
  destruct Hv as (Ha & He & _). destruct Hsp as (Hs1 & Hs2 & Hs3).
  pose proof (entry_stack_span_bound _ _ Ha He) as Hspan. pose proof (ROn_span (in_argv inp) (in_envp inp)) as Hro.
  unfold entry_stack_fits in Hfit. unfold sp_window_lo, sp_window_hi, entry_stack_span_max in *.
  unfold eb_rel. rewrite (eb_image_enc ph inp sp draw ρ0 Ha He Hs3).
  pose proof (E0_length ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw) as HL.
  split; [exact HF|]. split; [symmetry; apply sp_val_enc; exact Hs3|]. split; [rewrite HL; lia|].
  intros z Hz. rewrite HL in Hz.
  rewrite (E7_block segs pc ph sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) by lia.
  f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Read.
Variables (ph : PhdrInfo) (ρ : valuation).
Hypothesis HF : eb_facts ρ.

Let av := dec_argv ρ.
Let ev := dec_envp ρ.
Let B := eb_image ph ρ.
Let SB : Z := 184 + 8 * ρ v_argc + 8 * ρ v_envc.

Lemma len_dec_strs : forall cnt len bytev, 0 <= ρ cnt -> length (dec_strs ρ cnt len bytev) = Z.to_nat (ρ cnt).
Proof. intros. unfold dec_strs. rewrite length_map, length_seq. reflexivity. Qed.

Lemma nth_dec_strs : forall cnt len bytev k, (k < Z.to_nat (ρ cnt))%nat ->
  nth k (dec_strs ρ cnt len bytev) [] = map (fun j => Z_to_bv 8 (ρ (bytev (Z.of_nat k) (Z.of_nat j)))) (seq 0 (Z.to_nat (ρ (len (Z.of_nat k))))).
Proof.
  intros cnt len bytev k Hk. unfold dec_strs. rewrite nth_map_seq0 by exact Hk. reflexivity.
Qed.

Lemma facts_argc : 1 <= ρ v_argc <= 1024. Proof. apply HF. Qed.
Lemma facts_envc : 0 <= ρ v_envc <= 256. Proof. apply HF. Qed.

Lemma len_av : Z.of_nat (length av) = ρ v_argc.
Proof. unfold av, dec_argv. rewrite len_dec_strs by (pose proof facts_argc; lia). pose proof facts_argc. lia. Qed.
Lemma len_ev : Z.of_nat (length ev) = ρ v_envc.
Proof. unfold ev, dec_envp. rewrite len_dec_strs by (pose proof facts_envc; lia). pose proof facts_envc. lia. Qed.

Lemma len_k : forall k, 0 <= k < ρ v_argc -> Z.of_nat (length (nth (Z.to_nat k) av [])) = ρ (lenvar k).
Proof.
  intros k Hk. destruct HF as (_ & _ & Hs & _). destruct (Hs k Hk) as [HL _].
  unfold av, dec_argv. rewrite nth_dec_strs by lia. rewrite length_map, length_seq, (Z2Nat.id k) by lia.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma nth_k : forall k j, 0 <= k < ρ v_argc -> 0 <= j < ρ (lenvar k) ->
  nth (Z.to_nat j) (nth (Z.to_nat k) av []) (Z_to_bv 8 0) = Z_to_bv 8 (ρ (strvar k j)).
Proof.
  intros k j Hk Hj. destruct HF as (_ & _ & Hs & _). destruct (Hs k Hk) as [HL _].
  unfold av, dec_argv. rewrite nth_dec_strs by lia.
  rewrite (Z2Nat.id k) by lia. rewrite nth_map_seq0 by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma SB_SBn : Z.of_nat (SBn av ev) = SB.
Proof. unfold SBn, SB. rewrite <- len_av, <- len_ev. lia. Qed.

Lemma tab_av : Z.of_nat (tab av) = ρ v_ta.
Proof. destruct HF as (_ & _ & _ & _ & Ht & _). rewrite Ht. symmetry. apply tab_Z. Qed.
Lemma tab_ev : Z.of_nat (tab ev) = ρ v_te.
Proof. destruct HF as (_ & _ & _ & _ & _ & Ht & _). rewrite Ht. symmetry. apply tab_Z. Qed.

Lemma ROn_RO : Z.of_nat (ROn av ev) = SB + 8 * ρ v_q.
Proof.
  destruct HF as (_ & _ & _ & _ & _ & _ & Hq & _). unfold ROn. rewrite Nat2Z.inj_add, SB_SBn, Hq.
  rewrite <- tab_av, <- tab_ev. rewrite Nat2Z.inj_mul, Nat2Z.inj_div. f_equal. f_equal. f_equal. lia.
Qed.

Lemma sp_range : sp_window_lo <= sp_val ρ /\ sp_val ρ + Z.of_nat (length (eb_image (mkPhdrInfo 0 0 0) ρ)) <= sp_window_hi.
Proof. destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2). split; assumption. Qed.

Lemma len_B : Z.of_nat (length B) = SB + 8 * ρ v_q + 16.
Proof. unfold B. rewrite length_eb_image. fold av ev. rewrite ROn_RO. lia. Qed.

Lemma zadd : forall a b : Z, (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
Proof. intros a b. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. symmetry. apply Zplus_mod. Qed.

(* [comment removed for export] *)
Theorem R7_length : Z.of_nat (length B) = SB + 8 * ρ v_q + 16.
Proof. exact len_B. Qed.



(* [comment removed for export] *)
Lemma B_eq : B = build_stack_bytes ph (Z_to_bv 64 (sp_val ρ)) av ev (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_hw)) (dec_draw ρ).
Proof. reflexivity. Qed.

Lemma pre0 : forall L, pre 0 L = 0%nat.
Proof. reflexivity. Qed.
Lemma pre1 : forall (L : list (list byte)), L <> [] -> pre 1 L = (length (nth 0 L []) + 1)%nat.
Proof.
  intros [|x L] H; [contradiction|]. unfold pre, total_arg_bytes_nat. cbn.
  replace (firstn 0 L) with (@nil (list byte)) by reflexivity. cbn. lia.
Qed.

(* [comment removed for export] *)
Theorem R1_argc : rdB B 0 8 = word_le8 (Z_to_bv 64 (ρ v_argc)).
Proof. rewrite B_eq, E1_argc, len_av. reflexivity. Qed.

(* [comment removed for export] *)
Theorem R2_argv0 : rdB B 8 8 = word_le8 (Z_to_bv 64 (sp_val ρ + SB)).
Proof.
  pose proof facts_argc. pose proof len_av.
  pose proof (E2_argv ph (Z_to_bv 64 (sp_val ρ)) av ev (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_hw)) (dec_draw ρ) 0 ltac:(lia)) as E.
  cbn [Nat.mul Nat.add] in E. rewrite B_eq, E, pre0, Nat.add_0_r, SB_SBn, zadd. reflexivity.
Qed.

Theorem R2_argv1 : 2 <= ρ v_argc -> rdB B 16 8 = word_le8 (Z_to_bv 64 (sp_val ρ + SB + ρ (lenvar 0) + 1)).
Proof.
  intros H2. pose proof len_av. pose proof (len_k 0 ltac:(lia)) as L0.
  pose proof (E2_argv ph (Z_to_bv 64 (sp_val ρ)) av ev (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_hw)) (dec_draw ρ) 1 ltac:(lia)) as E.
  cbn [Nat.mul Nat.add] in E. rewrite B_eq, E, zadd. rewrite pre1 by (intros Hn; rewrite Hn in *; cbn in *; lia).
  f_equal. f_equal. rewrite !Nat2Z.inj_add, SB_SBn. change (Z.to_nat 0) with 0%nat in L0. lia.
Qed.

Theorem R2_argv1_null : ρ v_argc = 1 -> rdB B 16 8 = word_le8 (Z_to_bv 64 0).
Proof.
  intros H1. pose proof len_av as La. assert (Ha : length av = 1%nat) by lia.
  pose proof (E2_argv_null ph (Z_to_bv 64 (sp_val ρ)) av ev (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_hw)) (dec_draw ρ)) as E.
  rewrite Ha in E. cbn [Nat.mul Nat.add] in E. rewrite B_eq, E. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem R2_argv : forall (i : nat), (Z.of_nat i < ρ v_argc)%Z ->
  rdB B (8 + 8 * i) 8 = word_le8 (Z_to_bv 64 (sp_val ρ + SB + Z.of_nat (pre i av))).
Proof.
  intros i Hi. pose proof len_av.
  rewrite B_eq, (E2_argv ph (Z_to_bv 64 (sp_val ρ)) av ev (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_hw)) (dec_draw ρ) i)
    by lia.
  rewrite zadd. f_equal. f_equal. rewrite Nat2Z.inj_add, SB_SBn. lia.
Qed.

Theorem R2_null : rdB B (8 + 8 * Z.to_nat (ρ v_argc)) 8 = word_le8 (Z_to_bv 64 0).
Proof.
  pose proof len_av. replace (Z.to_nat (ρ v_argc)) with (length av) by lia.
  rewrite B_eq. apply E2_argv_null.
Qed.

Theorem R3_envp : forall (j : nat), (Z.of_nat j < ρ v_envc)%Z ->
  rdB B (16 + 8 * Z.to_nat (ρ v_argc) + 8 * j) 8 = word_le8 (Z_to_bv 64 (sp_val ρ + SB + ρ v_ta + Z.of_nat (pre j ev))).
Proof.
  intros j Hj. pose proof len_av. pose proof len_ev. replace (Z.to_nat (ρ v_argc)) with (length av) by lia.
  rewrite B_eq, (E3_envp ph (Z_to_bv 64 (sp_val ρ)) av ev (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_hw)) (dec_draw ρ) j)
    by lia.
  rewrite zadd. f_equal. f_equal. rewrite !Nat2Z.inj_add, SB_SBn, tab_av. lia.
Qed.

Theorem R3_null : rdB B (16 + 8 * Z.to_nat (ρ v_argc) + 8 * Z.to_nat (ρ v_envc)) 8 = word_le8 (Z_to_bv 64 0).
Proof.
  pose proof len_av. pose proof len_ev.
  replace (Z.to_nat (ρ v_argc)) with (length av) by lia. replace (Z.to_nat (ρ v_envc)) with (length ev) by lia.
  rewrite B_eq. apply E3_envp_null.
Qed.

(* [comment removed for export] *)
Definition auxv_keys : list Z := [3; 4; 5; 16; 6; 11; 12; 23; 25; 0].
Definition auxv_vals : list word :=
  [Z_to_bv 64 (Z.of_N (ph_addr ph)); Z_to_bv 64 (Z.of_N (ph_ent ph)); Z_to_bv 64 (Z.of_N (ph_num ph));
   Z_to_bv 64 (ρ v_hw); Z_to_bv 64 4096; Z_to_bv 64 (ρ v_uid); Z_to_bv 64 (ρ v_uid); Z_to_bv 64 0;
   Z_to_bv 64 (sp_val ρ + SB + 8 * ρ v_q); Z_to_bv 64 0].

Lemma auxv_nth : forall (i : nat), (i < 10)%nat ->
  nth i (auxv_entries ph (Z_to_bv 64 (sp_val ρ + SB + 8 * ρ v_q)) (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_hw)))
      (Z_to_bv 64 0, Z_to_bv 64 0)
  = (Z_to_bv 64 (nth i auxv_keys 0), nth i auxv_vals (Z_to_bv 64 0)).
Proof.
  intros i Hi. do 10 (destruct i as [|i]; [reflexivity|]). lia.
Qed.

Lemma rnd_ptr : (Z_to_bv 64 (sp_val ρ) + Z_to_bv 64 (Z.of_nat (ROn av ev)))%bv = Z_to_bv 64 (sp_val ρ + SB + 8 * ρ v_q).
Proof. rewrite zadd, ROn_RO. f_equal. lia. Qed.

Theorem R4_key : forall (i : nat), (i < 10)%nat ->
  rdB B (24 + 8 * Z.to_nat (ρ v_argc) + 8 * Z.to_nat (ρ v_envc) + 16 * i) 8 = word_le8 (Z_to_bv 64 (nth i auxv_keys 0)).
Proof.
  intros i Hi. pose proof len_av. pose proof len_ev.
  replace (Z.to_nat (ρ v_argc)) with (length av) by lia. replace (Z.to_nat (ρ v_envc)) with (length ev) by lia.
  rewrite B_eq. destruct (E4_auxv ph (Z_to_bv 64 (sp_val ρ)) av ev (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_hw)) (dec_draw ρ) i Hi)
    as [E _].
  rewrite E, rnd_ptr, auxv_nth by exact Hi. reflexivity.
Qed.

Theorem R4_val : forall (i : nat), (i < 10)%nat ->
  rdB B (32 + 8 * Z.to_nat (ρ v_argc) + 8 * Z.to_nat (ρ v_envc) + 16 * i) 8 = word_le8 (nth i auxv_vals (Z_to_bv 64 0)).
Proof.
  intros i Hi. pose proof len_av. pose proof len_ev.
  replace (Z.to_nat (ρ v_argc)) with (length av) by lia. replace (Z.to_nat (ρ v_envc)) with (length ev) by lia.
  rewrite B_eq. destruct (E4_auxv ph (Z_to_bv 64 (sp_val ρ)) av ev (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_hw)) (dec_draw ρ) i Hi)
    as [_ E].
  rewrite E, rnd_ptr, auxv_nth by exact Hi. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem R5_str : forall k j, 0 <= k < ρ v_argc -> 0 <= j <= ρ (lenvar k) ->
  nth (Z.to_nat (SB + Z.of_nat (pre (Z.to_nat k) av) + j)) B (Z_to_bv 8 0)
  = if j <? ρ (lenvar k) then Z_to_bv 8 (ρ (strvar k j)) else Z_to_bv 8 0.
Proof.
  intros k j Hk Hj. pose proof len_av. pose proof (len_k k Hk) as Lk.
  replace (Z.to_nat (SB + Z.of_nat (pre (Z.to_nat k) av) + j)) with (SBn av ev + pre (Z.to_nat k) av + Z.to_nat j)%nat
    by (pose proof SB_SBn; lia).
  rewrite B_eq, E5_argv_str by lia.
  destruct (Z.ltb_spec j (ρ (lenvar k))) as [Hl|Hl].
  - rewrite app_nth1 by lia. apply nth_k; lia.
  - rewrite app_nth2 by lia. replace (Z.to_nat j - length (nth (Z.to_nat k) av []))%nat with 0%nat by lia. reflexivity.
Qed.

Theorem R5_str0 : forall j, 0 <= j <= ρ (lenvar 0) ->
  nth (Z.to_nat (SB + j)) B (Z_to_bv 8 0) = if j <? ρ (lenvar 0) then Z_to_bv 8 (ρ (strvar 0 j)) else Z_to_bv 8 0.
Proof.
  intros j Hj. pose proof facts_argc. rewrite <- (R5_str 0 j) by lia. f_equal. change (Z.to_nat 0) with 0%nat. rewrite pre0. lia.
Qed.

Theorem R5_str1 : 2 <= ρ v_argc -> forall j, 0 <= j <= ρ (lenvar 1) ->
  nth (Z.to_nat (SB + ρ (lenvar 0) + 1 + j)) B (Z_to_bv 8 0) = if j <? ρ (lenvar 1) then Z_to_bv 8 (ρ (strvar 1 j)) else Z_to_bv 8 0.
Proof.
  intros H2 j Hj. pose proof len_av. pose proof (len_k 0 ltac:(lia)) as L0. change (Z.to_nat 0) with 0%nat in L0.
  rewrite <- (R5_str 1 j) by lia. f_equal. change (Z.to_nat 1) with 1%nat.
  rewrite pre1 by (intros Hn; rewrite Hn in *; cbn in *; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma lo_byte : forall r0 r1 (s : Z), 0 <= r0 < 2 ^ 64 -> 0 <= r1 -> 0 <= s -> s + 8 <= 64 ->
  bv_wrap 8 (Z.shiftr (r0 + 2 ^ 64 * r1) s) = bv_wrap 8 (Z.shiftr r0 s).
Proof.
  intros r0 r1 s H0 H1 Hs Hs8. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
  rewrite !Z.shiftr_div_pow2 by lia.
  replace (r0 + 2 ^ 64 * r1) with (r0 + (2 ^ (64 - s) * r1) * 2 ^ s).
  2:{ rewrite <- Z.mul_assoc, (Z.mul_comm r1), Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. f_equal. lia. }
  rewrite Z.div_add by (apply Z.pow_nonzero; lia).
  replace (2 ^ (64 - s) * r1) with ((2 ^ (56 - s) * r1) * 2 ^ 8).
  2:{ rewrite <- Z.mul_assoc, (Z.mul_comm r1), Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. lia. }
  apply Z_mod_plus_full.
Qed.

Lemma hi_byte : forall r0 r1 (s : Z), 0 <= r0 < 2 ^ 64 -> 0 <= r1 -> 64 <= s ->
  bv_wrap 8 (Z.shiftr (r0 + 2 ^ 64 * r1) s) = bv_wrap 8 (Z.shiftr r1 (s - 64)).
Proof.
  intros r0 r1 s H0 H1 Hs. f_equal. rewrite !Z.shiftr_div_pow2 by lia.
  replace s with (64 + (s - 64)) at 1 by lia. rewrite Z.pow_add_r by lia. rewrite <- Z.div_div by (try apply Z.pow_pos_nonneg; lia).
  f_equal. rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma random_split : forall r0 r1, 0 <= r0 < 2 ^ 64 -> 0 <= r1 < 2 ^ 64 ->
  at_random_bytes (Z_to_bv 128 (r0 mod 2 ^ 64 + 2 ^ 64 * (r1 mod 2 ^ 64))) = word_le8 (Z_to_bv 64 r0) ++ word_le8 (Z_to_bv 64 r1).
Proof.
  intros r0 r1 H0 H1. rewrite !Z.mod_small by lia.
  assert (HX : bv_wrap 128 (r0 + 2 ^ 64 * r1) = r0 + 2 ^ 64 * r1).
  { apply bv_wrap_small. change (bv_modulus 128) with (2 ^ 128). lia. }
  assert (W0 : bv_wrap 64 r0 = r0) by (apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
  assert (W1 : bv_wrap 64 r1 = r1) by (apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
  unfold at_random_bytes, word_le8. cbn [app].
  Local Ltac bytegoal HX W0 W1 := apply bv_eq; rewrite !bv_extract_unsigned, !Z_to_bv_unsigned, HX, ?W0, ?W1;
    first [ apply lo_byte; cbn; lia | rewrite hi_byte by (cbn; lia); f_equal; f_equal; cbn; lia ].
  repeat match goal with
  | |- (?a :: ?l) = (?b :: ?l') => f_equal; [ bytegoal HX W0 W1 | ]
  | |- [?a] = [?b] => f_equal; bytegoal HX W0 W1
  end.
Qed.

Theorem R6_random : rdB B (Z.to_nat (SB + 8 * ρ v_q)) 16 = word_le8 (Z_to_bv 64 (ρ v_r0)) ++ word_le8 (Z_to_bv 64 (ρ v_r1)).
Proof.
  destruct HF as (_ & _ & _ & _ & _ & _ & _ & Hr0 & Hr1 & _).
  replace (Z.to_nat (SB + 8 * ρ v_q)) with (ROn av ev) by (pose proof ROn_RO; lia).
  rewrite B_eq, E6_random. cbn [dec_draw ed_random]. unfold dec_random. apply random_split; assumption.
Qed.

End Read.
