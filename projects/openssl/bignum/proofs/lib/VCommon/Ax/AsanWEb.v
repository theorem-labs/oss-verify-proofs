(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput, the CONFIG_RSEQ flag, the new auxv layout, the init stack window and the vDSO); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootLayout.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLin AxEntryRel AsanWEntry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

(* The valuation an actual launch gives: the sp digits, the AT_RANDOM halves,
   the two counts and byte tables, and, at 08b1429, the parity gap, the
   arch_align_stack pad, and the auxv values the block now carries. *)
Definition enc (inp : ProcInput) (sp mbase pcw : word) (draw : EntryDraw) (ρ0 : valuation) : valuation :=
  fun v =>
    let z := to_Z v in
    let av := in_argv inp in
    let ev := in_envp inp in
    let xfn := in_execfn inp in
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
    else if z =? 14 then (Z.of_nat (length av) + Z.of_nat (length ev) + 1) mod 2
    else if z =? 15 then
      (16 + 8 * ((Z.of_nat (length av) + Z.of_nat (length ev) + 1) mod 2)
       + Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top draw) av ev xfn))
    else if z =? 16 then bv_unsigned (in_gid inp)
    else if z =? 17 then bv_unsigned pcw
    else if z =? 18 then bv_unsigned (vdso_text_base (in_kernel inp) sp mbase)
    else if z =? 19 then min_sigframe_size (in_kernel inp) (in_hwcap inp)
    else if z =? 20 then Z.of_nat (length xfn)
    else if (2 ^ 40 <=? z) && (z <? 2 ^ 41) then
      bv_unsigned (nth (Z.to_nat ((z - 2 ^ 40) mod 2 ^ 17)) (nth (Z.to_nat ((z - 2 ^ 40) / 2 ^ 17)) av []) (Z_to_bv 8 0))
    else if (2 ^ 41 <=? z) && (z <? 2 ^ 42) then Z.of_nat (length (nth (Z.to_nat (z - 2 ^ 41)) av []))
    else if (2 ^ 42 <=? z) && (z <? 2 ^ 42 + 2 ^ 20) then Z.of_nat (length (nth (Z.to_nat (z - 2 ^ 42)) ev []))
    else if (2 ^ 42 + 2 ^ 20 <=? z) && (z <? 2 ^ 43) then
      bv_unsigned (nth (Z.to_nat ((z - 2 ^ 42 - 2 ^ 20) mod 2 ^ 17))
                       (nth (Z.to_nat ((z - 2 ^ 42 - 2 ^ 20) / 2 ^ 17)) ev []) (Z_to_bv 8 0))
    else if (2 ^ 43 <=? z) && (z <? 2 ^ 43 + 2 ^ 17) then
      bv_unsigned (nth (Z.to_nat (z - 2 ^ 43)) xfn (Z_to_bv 8 0))
    else ρ0 v.

Local Ltac zbool :=
  repeat match goal with
  | |- context [?a =? ?b] => first [ rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia ]
  | |- context [?a <=? ?b] => first [ rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia ]
  | |- context [?a <? ?b] => first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
  end; cbn [andb orb].

Section Enc.
Variables (inp : ProcInput) (sp mbase pcw : word) (draw : EntryDraw) (ρ0 : valuation).
Let ρ := enc inp sp mbase pcw draw ρ0.
Let av := in_argv inp.
Let ev := in_envp inp.
Let xfn := in_execfn inp.

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
Lemma enc_par : ρ v_par = (Z.of_nat (length av) + Z.of_nat (length ev) + 1) mod 2. Proof. reflexivity. Qed.
Lemma enc_g : ρ v_g = 16 + 8 * ((Z.of_nat (length av) + Z.of_nat (length ev) + 1) mod 2)
                      + Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top draw) av ev xfn).
Proof. reflexivity. Qed.
Lemma enc_gid : ρ v_gid = bv_unsigned (in_gid inp). Proof. reflexivity. Qed.
Lemma enc_ent : ρ v_ent = bv_unsigned pcw. Proof. reflexivity. Qed.
Lemma enc_vd : ρ v_vd = bv_unsigned (vdso_text_base (in_kernel inp) sp mbase). Proof. reflexivity. Qed.
Lemma enc_mss : ρ v_mss = min_sigframe_size (in_kernel inp) (in_hwcap inp). Proof. reflexivity. Qed.
Lemma enc_xl : ρ v_xl = Z.of_nat (length xfn). Proof. reflexivity. Qed.

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

Lemma enc_xstrvar : forall j, 0 <= j < 2 ^ 17 ->
  ρ (xstrvar j) = bv_unsigned (nth (Z.to_nat j) xfn (Z_to_bv 8 0)).
Proof.
  intros j Hj. unfold ρ, enc, xstrvar. rewrite to_Z_of_small by lia. cbv zeta. zbool.
  replace (2 ^ 43 + j - 2 ^ 43) with j by lia. reflexivity.
Qed.

End Enc.

Lemma bsb_draw : forall la ph entry sp top av ev xfn uid gid hw d1 d2, ed_random d1 = ed_random d2 ->
  build_stack_bytes la ph entry sp top av ev xfn uid gid hw d1 = build_stack_bytes la ph entry sp top av ev xfn uid gid hw d2.
Proof. intros. unfold build_stack_bytes. rewrite H. reflexivity. Qed.

Lemma nth_map_seq0 : forall {A} (f : nat -> A) (n k : nat) (d : A), (k < n)%nat -> nth k (map f (seq 0 n)) d = f k.
Proof.
  intros A f n k d Hk. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hk).
  rewrite map_nth, seq_nth by exact Hk. reflexivity.
Qed.

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

Lemma dec_argv_enc : forall inp sp mbase pcw draw ρ0, valid_argv (in_argv inp) -> dec_argv (enc inp sp mbase pcw draw ρ0) = in_argv inp.
Proof.
  intros inp sp mbase pcw draw ρ0 ([H1 H2] & _ & H3 & _). unfold dec_argv. apply dec_strs_enc.
  - apply enc_argc.
  - intros k Hk. rewrite enc_lenvar by lia. rewrite Nat2Z.id. reflexivity.
  - intros k j Hk Hj. pose proof (nth_Forall _ _ [] k H3 Hk) as HL. cbn beta in HL.
    rewrite enc_strvar by lia. rewrite !Nat2Z.id. reflexivity.
Qed.

Lemma dec_envp_enc : forall inp sp mbase pcw draw ρ0, valid_envp (in_envp inp) -> dec_envp (enc inp sp mbase pcw draw ρ0) = in_envp inp.
Proof.
  intros inp sp mbase pcw draw ρ0 (H1 & _ & H3 & _). unfold dec_envp. apply dec_strs_enc.
  - apply enc_envc.
  - intros k Hk. rewrite enc_elenvar by lia. rewrite Nat2Z.id. reflexivity.
  - intros k j Hk Hj. pose proof (nth_Forall _ _ [] k H3 Hk) as HL. cbn beta in HL.
    rewrite enc_estrvar by lia. rewrite !Nat2Z.id. reflexivity.
Qed.

Lemma sp_val_enc : forall inp sp mbase pcw draw ρ0, bv_unsigned sp mod 16 = 0 -> sp_val (enc inp sp mbase pcw draw ρ0) = bv_unsigned sp.
Proof.
  intros inp sp mbase pcw draw ρ0 H16. unfold sp_val, sp_terms. cbn [teval].
  rewrite enc_x0, enc_x1, enc_x2, enc_x3. set (s := bv_unsigned sp) in *. pose proof (u64_range sp) as Hs. fold s in Hs.
  pose proof (Z.div_mod s 16 ltac:(lia)) as D1. rewrite H16 in D1.
  pose proof (Z.div_mod (s / 16) 4 ltac:(lia)) as D2. rewrite Z.div_div in D2 by lia.
  pose proof (Z.div_mod (s / 64) 64 ltac:(lia)) as D3. rewrite Z.div_div in D3 by lia.
  pose proof (Z.div_mod (s / 4096) 8 ltac:(lia)) as D4. rewrite Z.div_div in D4 by lia.
  change (16 * 4) with 64 in D2. change (64 * 64) with 4096 in D3. change (4096 * 8) with 32768 in D4. lia.
Qed.

Lemma ed_random_enc : forall r inp sp mbase pcw draw ρ0,
  ed_random (dec_draw r (enc inp sp mbase pcw draw ρ0)) = ed_random draw.
Proof.
  intros r inp sp mbase pcw draw ρ0. cbn [dec_draw ed_random]. unfold dec_random. rewrite enc_r0, enc_r1.
  pose proof (bv_unsigned_in_range _ (ed_random draw)) as HR. change (bv_modulus 128) with (2 ^ 128) in HR.
  set (R := bv_unsigned (ed_random draw)) in *.
  rewrite Z.mod_mod by lia. rewrite (Z.mod_small (R / 2 ^ 64) (2 ^ 64)).
  2:{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 64 * 2 ^ 64) with (2 ^ 128). lia. }
  rewrite Z.add_comm, <- Z.div_mod by lia. unfold R. apply Z_to_bv_bv_unsigned.
Qed.

Lemma uid_enc : forall inp sp mbase pcw draw ρ0, Z_to_bv 64 (enc inp sp mbase pcw draw ρ0 v_uid) = in_uid inp.
Proof. intros. rewrite enc_uid. apply Z_to_bv_bv_unsigned. Qed.

Lemma hw_enc : forall inp sp mbase pcw draw ρ0, Z_to_bv 64 (enc inp sp mbase pcw draw ρ0 v_hw) = in_hwcap inp.
Proof. intros. rewrite enc_hw. apply Z_to_bv_bv_unsigned. Qed.

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

(* ------------------------------------------------------------------------- *)
(* The valuation describes the launch's own block.                            *)
(* ------------------------------------------------------------------------- *)

Lemma dec_execfn_enc : forall inp sp mbase pcw draw ρ0, (Z.of_nat (length (in_execfn inp)) < 2 ^ 17)%Z ->
  dec_execfn (enc inp sp mbase pcw draw ρ0) = in_execfn inp.
Proof.
  intros inp sp mbase pcw draw ρ0 Hx. unfold dec_execfn.
  rewrite (enc_xl inp sp mbase pcw draw ρ0), Nat2Z.id.
  apply (map_seq_nth (in_execfn inp) (Z_to_bv 8 0)). intros j Hj.
  rewrite (enc_xstrvar inp sp mbase pcw draw ρ0 (Z.of_nat j)) by lia.
  rewrite Nat2Z.id. apply u8_roundtrip.
Qed.

(* [r] is the launch's own rseq flag, so that field matches by reflexivity; the cache
   words are the one kernel field this lemma reads. *)
Lemma la_enc : forall inp sp mbase pcw draw ρ0,
  launch_cache_words (in_kernel inp) = launch_cache_words default_kernel ->
  dec_la (kb_rseq (in_kernel inp)) (enc inp sp mbase pcw draw ρ0) = launch_auxv inp sp mbase.
Proof.
  intros inp sp mbase pcw draw ρ0 Hcw. unfold dec_la, launch_auxv.
  rewrite (enc_vd inp sp mbase pcw draw ρ0), (enc_mss inp sp mbase pcw draw ρ0), Hcw.
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Section EncImage.
Local Set Default Proof Using "All".
(* [r] is the launch's own rseq flag, which is free: rseq is not pinned. *)
Variables (inp : ProcInput) (sp mbase pcw brk : word) (draw : EntryDraw) (ρ0 : valuation).
Hypothesis Hinp : valid_input inp.
(* the one kernel field the block reads besides rseq: the cache words of the auxv *)
Hypothesis Hcw : launch_cache_words (in_kernel inp) = launch_cache_words default_kernel.
Hypothesis Hlaunch : entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp.

Notation ρ := (enc inp sp mbase pcw draw ρ0).
Let av := in_argv inp.
Let ev := in_envp inp.
Let xfn := in_execfn inp.
Let r := kb_rseq (in_kernel inp).
Let PAD := block_pad_len r sp (ed_top draw) av ev xfn.

Lemma ei_va : valid_argv av /\ valid_envp ev.
Proof. destruct Hinp as (Ha & He & _). split; assumption. Qed.

Lemma ei_sp16 : bv_unsigned sp mod 16 = 0.
Proof. cbn [entry_launch_ok_va] in Hlaunch. destruct Hlaunch as (_ & (H & _) & _). exact H. Qed.

Lemma ei_arith : (bv_unsigned sp + Z.of_nat (block_head_size r av ev)
                  + Z.of_nat (launch_string_bytes av ev xfn) + 8 <= bv_unsigned (ed_top draw))%Z.
Proof.
  cbn [entry_launch_ok_va] in Hlaunch. destruct Hlaunch as (_ & (_ & _ & Hhi) & _).
  unfold launch_sp_hi, align_down16 in Hhi.
  pose proof (Z.mod_pos_bound (bv_unsigned (ed_top draw) - 8 - Z.of_nat (launch_string_bytes av ev xfn)) 16 ltac:(lia)).
  unfold r, av, ev, xfn in *. lia.
Qed.

Lemma ei_pad : Z.of_nat PAD
  = (bv_unsigned (ed_top draw) - 8 - Z.of_nat (launch_string_bytes av ev xfn)
     - bv_unsigned sp - Z.of_nat (block_head_size r av ev))%Z.
Proof. unfold PAD, block_pad_len. pose proof ei_arith. rewrite Z2Nat.id by lia. reflexivity. Qed.

Lemma ei_pad_lt : (Z.of_nat PAD <= 4110)%Z.
Proof.
  cbn [entry_launch_ok_va] in Hlaunch. destruct Hlaunch as (_ & (_ & Hlo & _) & _).
  unfold launch_sp_lo, align_down16 in Hlo. rewrite ei_pad.
  pose proof (Z.mod_pos_bound (bv_unsigned (ed_top draw) - 8 - Z.of_nat (launch_string_bytes av ev xfn) - 4095) 16 ltac:(lia)).
  unfold r, av, ev, xfn in *. lia.
Qed.

Lemma ei_str_off : str_off r ρ = (Z.of_nat (block_head_size r av ev) + Z.of_nat PAD)%Z.
Proof.
  unfold str_off. rewrite (enc_argc inp sp mbase pcw draw ρ0), (enc_envc inp sp mbase pcw draw ρ0),
    (enc_g inp sp mbase pcw draw ρ0).
  unfold PAD, r, av, ev, xfn. unfold block_head_size, block_items. cbv zeta.
  rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_mul, ?Nat2Z.inj_mod. lia.
Qed.

Lemma ei_spval : sp_val ρ = bv_unsigned sp.
Proof. apply sp_val_enc. exact ei_sp16. Qed.

Lemma ei_top : dec_top r ρ = bv_unsigned (ed_top draw).
Proof.
  unfold dec_top. rewrite ei_spval, ei_str_off, ei_pad.
  rewrite (enc_ta inp sp mbase pcw draw ρ0), (enc_te inp sp mbase pcw draw ρ0), (enc_xl inp sp mbase pcw draw ρ0).
  unfold launch_string_bytes. rewrite !Nat2Z.inj_add, !length_flatten_strings, <- !total_arg_bytes_Z.
  unfold av, ev, xfn. lia.
Qed.

(* the block reads only [ed_random] and the top, and the top is an argument *)
Lemma ei_draw_random : ed_random (dec_draw r ρ) = ed_random draw.
Proof. apply ed_random_enc. Qed.

Theorem ei_image : forall ph, eb_image r ph ρ = entry_stack_image inp mbase ph pcw sp draw.
Proof.
  intros ph. destruct ei_va as [Ha He].
  assert (Hx : (Z.of_nat (length xfn) < 2 ^ 17)%Z).
  { destruct Hinp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hv & _) & _).
    unfold xfn. destruct Hv as [(H1 & _)|[(ds & -> & Hd)|(ds & rest & -> & Hd & (Hr & _) & _)]];
      [lia | | ]; rewrite ?length_app; cbn [length dev_fd_prefix]; destruct Hd as (_ & _ & _ & Hdl); lia. }
  unfold eb_image. rewrite entry_stack_image_block.
  rewrite (dec_argv_enc inp sp mbase pcw draw ρ0 Ha), (dec_envp_enc inp sp mbase pcw draw ρ0 He),
    (dec_execfn_enc inp sp mbase pcw draw ρ0 Hx).
  (* [r] is a section [Let]; la_enc is stated over its body *)
  change (dec_la r ρ) with (dec_la (kb_rseq (in_kernel inp)) ρ).
  rewrite (la_enc inp sp mbase pcw draw ρ0 Hcw), ei_spval, ei_top.
  rewrite (enc_uid inp sp mbase pcw draw ρ0), (enc_gid inp sp mbase pcw draw ρ0),
    (enc_hw inp sp mbase pcw draw ρ0), (enc_ent inp sp mbase pcw draw ρ0).
  rewrite !Z_to_bv_bv_unsigned. apply bsb_draw. exact ei_draw_random.
Qed.

End EncImage.

(** AT_MINSIGSTKSZ of the pinned vector length: 1088 without the V extension, 1664 with it *)
Lemma mss_default : forall h, min_sigframe_size default_kernel h = if hwcap_has_v h then 1664 else 1088.
Proof. intros h. unfold min_sigframe_size, launch_vlenb. destruct (hwcap_has_v h); vm_compute; reflexivity. Qed.

Section EncFacts.
Local Set Default Proof Using "All".
Variables (inp : ProcInput) (sp mbase pcw brk : word) (draw : EntryDraw) (ρ0 : valuation).
Hypothesis Hinp : valid_input inp.
Hypothesis Hcw : launch_cache_words (in_kernel inp) = launch_cache_words default_kernel.
(* AT_MINSIGSTKSZ of the pinned vector length: the FL range 1088..1664 *)
Hypothesis Hmss : min_sigframe_size (in_kernel inp) (in_hwcap inp) = min_sigframe_size default_kernel (in_hwcap inp).
Hypothesis Hlaunch : entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp.
Hypothesis Hsp : valid_sp_va Sv48 sp.

Notation ρ := (enc inp sp mbase pcw draw ρ0).
Let r := kb_rseq (in_kernel inp).

Theorem eb_facts_enc : eb_facts r ρ.
Proof.
  pose proof (ei_va inp sp mbase pcw brk draw ρ0 Hinp Hcw Hlaunch) as [Ha' He'].
  pose proof Ha' as Ha. pose proof He' as He.
  destruct Ha as ([Ha1 Ha2] & Hat & Ha3 & Ha4 & _). destruct He as (He1 & Het & He3 & He4).
  pose proof Hinp as Hi'. destruct Hi' as (_ & _ & _ & _ & _ & Hcred & _ & _ & Hhw & _ & _ & _ & (Hxf & Hlb) & _).
  pose proof Hsp as Hsp'. destruct Hsp' as (Hs1 & Hs2 & Hs3).
  pose proof (bv_unsigned_in_range _ (ed_random draw)) as HR. change (bv_modulus 128) with (2 ^ 128) in HR.
  assert (Hx : (0 <= Z.of_nat (length (in_execfn inp)) <= 4114)%Z).
  { destruct Hxf as [(H1 & _)|[(ds & E & Hd)|(ds & rest & E & Hd & (Hr & _) & _)]];
      [lia | rewrite E | rewrite E]; rewrite ?length_app; cbn [length dev_fd_prefix];
      destruct Hd as (_ & _ & _ & Hdl); lia. }
  unfold eb_facts, r.
  rewrite (dec_argv_enc inp sp mbase pcw draw ρ0 Ha'), (dec_envp_enc inp sp mbase pcw draw ρ0 He'),
    (ei_spval inp sp mbase pcw brk draw ρ0 Hinp Hcw Hlaunch), (ei_top inp sp mbase pcw brk draw ρ0 Hinp Hcw Hlaunch).
  rewrite (enc_argc inp sp mbase pcw draw ρ0), (enc_envc inp sp mbase pcw draw ρ0),
    (enc_ta inp sp mbase pcw draw ρ0), (enc_te inp sp mbase pcw draw ρ0),
    (enc_par inp sp mbase pcw draw ρ0), (enc_g inp sp mbase pcw draw ρ0),
    (enc_xl inp sp mbase pcw draw ρ0),
    (enc_r0 inp sp mbase pcw draw ρ0), (enc_r1 inp sp mbase pcw draw ρ0),
    (enc_uid inp sp mbase pcw draw ρ0), (enc_gid inp sp mbase pcw draw ρ0),
    (enc_hw inp sp mbase pcw draw ρ0), (enc_ent inp sp mbase pcw draw ρ0),
    (enc_vd inp sp mbase pcw draw ρ0), (enc_mss inp sp mbase pcw draw ρ0).
  pose proof (ei_pad_lt inp sp mbase pcw brk draw ρ0 Hinp Hcw Hlaunch) as Hpad.
  pose proof (Nat2Z.is_nonneg (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top draw)
                                 (in_argv inp) (in_envp inp) (in_execfn inp))) as Hpad0.
  assert (Hmssr : (0 <= min_sigframe_size (in_kernel inp) (in_hwcap inp) < 2 ^ 64)%Z).
  { rewrite Hmss, mss_default. destruct (hwcap_has_v (in_hwcap inp)); lia. }
  split; [lia|]. split; [lia|].
  split; [|split].
  - intros k Hk. assert (Hk' : (Z.to_nat k < length (in_argv inp))%nat) by lia.
    pose proof (nth_Forall _ _ [] _ Ha3 Hk') as HL. cbn beta in HL.
    rewrite (enc_lenvar inp sp mbase pcw draw ρ0) by lia. split; [lia|].
    intros j Hj. rewrite (enc_strvar inp sp mbase pcw draw ρ0) by lia.
    set (b := nth (Z.to_nat j) (nth (Z.to_nat k) (in_argv inp) []) (Z_to_bv 8 0)).
    pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
    assert (Hnz : b <> Z_to_bv 8 0).
    { intros E. pose proof (nth_Forall _ _ [] _ Ha4 Hk') as HN. cbn beta in HN. apply HN. rewrite <- E. apply nth_In. lia. }
    assert (bv_unsigned b <> 0) by (intros E; apply Hnz; apply bv_eq; rewrite E; reflexivity). lia.
  - intros k Hk. assert (Hk' : (Z.to_nat k < length (in_envp inp))%nat) by lia.
    pose proof (nth_Forall _ _ [] _ He3 Hk') as HL. cbn beta in HL.
    rewrite (enc_elenvar inp sp mbase pcw draw ρ0) by lia. split; [lia|].
    intros j Hj. rewrite (enc_estrvar inp sp mbase pcw draw ρ0) by lia.
    set (b := nth (Z.to_nat j) (nth (Z.to_nat k) (in_envp inp) []) (Z_to_bv 8 0)).
    pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
    assert (Hnz : b <> Z_to_bv 8 0).
    { intros E. pose proof (nth_Forall _ _ [] _ He4 Hk') as HN. cbn beta in HN. apply HN. rewrite <- E. apply nth_In. lia. }
    assert (bv_unsigned b <> 0) by (intros E; apply Hnz; apply bv_eq; rewrite E; reflexivity). lia.
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    split; [split; [lia|]|].
    + intros j Hj. rewrite (enc_xstrvar inp sp mbase pcw draw ρ0) by lia.
      pose proof (bv_unsigned_in_range _ (nth (Z.to_nat j) (in_execfn inp) (Z_to_bv 8 0))) as Hb.
      change (bv_modulus 8) with 256 in Hb. lia.
    + split; [split; [apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia]|].
      split.
      * split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 64 * 2 ^ 64) with (2 ^ 128). lia.
      * destruct Hcred as [Hu Hg]. unfold valid_id in Hu, Hg.
        pose proof (u64_range (in_uid inp)). pose proof (u64_range (in_gid inp)).
        pose proof (u64_range (in_hwcap inp)). pose proof (u64_range pcw).
        pose proof (u64_range (vdso_text_base (in_kernel inp) sp mbase)).
        pose proof Hlaunch as Hl'. cbn [entry_launch_ok_va] in Hl'. destruct Hl' as (Htop & _ & _).
        destruct Htop as (Htop1 & Htop2 & _). cbn [va_stack_top] in Htop2. unfold page_size in Htop1.
        unfold va_sp_window_lo, va_stack_top, sp_window_lo, sp_window_hi in *.
        repeat split; try lia.
Qed.

End EncFacts.

(* ------------------------------------------------------------------------- *)
(* The launch's memory holds the block the valuation describes.               *)
(* ------------------------------------------------------------------------- *)

Theorem eb_rel_init : forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk mbase : word) (draw : EntryDraw)
                              (inp : ProcInput) (ρ0 : valuation),
  valid_input inp -> launch_cache_words (in_kernel inp) = launch_cache_words default_kernel -> min_sigframe_size (in_kernel inp) (in_hwcap inp) = min_sigframe_size default_kernel (in_hwcap inp) ->
  valid_sp_va Sv48 sp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  eb_rel (kb_rseq (in_kernel inp)) ph (enc inp sp mbase (Z_to_bv 64 (Z.of_N pc)) draw ρ0)
    (ms_mem (init_machine_state segs pc ph sp mbase draw inp))
    (bv_unsigned sp) 2238672.
Proof.
  intros segs pc ph sp brk mbase draw inp ρ0 Hv Hcw Hmss Hsp Hl.
  set (pcw := Z_to_bv 64 (Z.of_N pc)).
  pose proof (eb_facts_enc inp sp mbase pcw brk draw ρ0 Hv Hcw Hmss Hl Hsp) as HF.
  pose proof (ei_image inp sp mbase pcw brk draw ρ0 Hv Hcw Hl ph) as EI.
  pose proof (ei_pad inp sp mbase pcw brk draw ρ0 Hv Hcw Hl) as EP.
  pose proof (ei_pad_lt inp sp mbase pcw brk draw ρ0 Hv Hcw Hl) as EPl.
  pose proof (ei_spval inp sp mbase pcw brk draw ρ0 Hv Hcw Hl) as ES.
  destruct Hv as (Ha & He & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hlb) & _).
  destruct Ha as ([Ha1 _] & _). destruct He as (He1 & _).
  cbn [entry_launch_ok_va] in Hl. destruct Hl as ((_ & Htop & _) & _ & _). cbn [va_stack_top] in Htop.
  assert (HL : Z.of_nat (length (entry_stack_image inp mbase ph pcw sp draw))
               = bv_unsigned (ed_top draw) - bv_unsigned sp).
  { rewrite entry_stack_image_block, length_bsb. cbn [la_rseq launch_auxv]. rewrite !Nat2Z.inj_add. rewrite EP. lia. }
  assert (Hhs : Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
                <= 512 + 8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp))).
  { unfold block_head_size, block_items. cbv zeta.
    assert (Haux : (auxv_size (kb_rseq (in_kernel inp)) <= 464)%nat)
      by (destruct (kb_rseq (in_kernel inp)); [change (auxv_size true) with 464%nat | change (auxv_size false) with 432%nat]; lia).
    pose proof (Nat.mod_upper_bound (length (in_argv inp) + length (in_envp inp) + 3) 2 ltac:(lia)). lia. }
  unfold launch_bytes, e2big_limit in Hlb.
  pose proof (u64_range sp).
  unfold eb_rel. rewrite EI. split; [exact HF|]. split; [symmetry; exact ES|].
  split; [rewrite HL; lia|].
  intros z Hz. rewrite HL in Hz.
  (* E7_block's side goals spell the entry word out, not as [pcw] *)
  pose proof (u64_range (ed_top draw)) as Htop64.
  rewrite (E7_block segs pc ph sp mbase draw inp) by (unfold pcw in HL; rewrite HL; lia).
  f_equal. f_equal. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* Reading the block a valuation describes.                                    *)
(* ------------------------------------------------------------------------- *)

Lemma zadd : forall a b : Z, (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
Proof. intros a b. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. symmetry. apply Zplus_mod. Qed.

Lemma zsub_nat : forall (a : Z) (n : nat), (Z_to_bv 64 a - nat_to_word n)%bv = Z_to_bv 64 (a - Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word. rewrite bv_sub_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.

Section Read.
Local Set Default Proof Using "All".
Variables (r : bool) (ph : PhdrInfo) (ρ : valuation).
Hypothesis HF : eb_facts r ρ.

Let av := dec_argv ρ.
Let ev := dec_envp ρ.
Let xfn := dec_execfn ρ.
Let B := eb_image r ph ρ.
Let SB : Z := 24 + 8 * ρ v_argc + 8 * ρ v_envc.
Let SO : Z := 24 + Z.of_nat (auxv_size r) + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g.
Let spw := Z_to_bv 64 (sp_val ρ).
Let topw := Z_to_bv 64 (dec_top r ρ).

Lemma len_dec_strs : forall cnt len bytev, 0 <= ρ cnt -> length (dec_strs ρ cnt len bytev) = Z.to_nat (ρ cnt).
Proof. intros. unfold dec_strs. rewrite length_map, length_seq. reflexivity. Qed.

Lemma nth_dec_strs : forall cnt len bytev k, (k < Z.to_nat (ρ cnt))%nat ->
  nth k (dec_strs ρ cnt len bytev) [] = map (fun j => Z_to_bv 8 (ρ (bytev (Z.of_nat k) (Z.of_nat j)))) (seq 0 (Z.to_nat (ρ (len (Z.of_nat k))))).
Proof. intros cnt len bytev k Hk. unfold dec_strs. rewrite nth_map_seq0 by exact Hk. reflexivity. Qed.

Lemma facts_argc : 1 <= ρ v_argc <= 1024. Proof. apply HF. Qed.
Lemma facts_envc : 0 <= ρ v_envc <= 256. Proof. pose proof HF as (_ & H & _). exact H. Qed.
Lemma facts_par : ρ v_par = (ρ v_argc + ρ v_envc + 1) mod 2. Proof. pose proof HF as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma facts_g : 16 + 8 * ρ v_par <= ρ v_g <= 16 + 8 * ρ v_par + 4110. Proof. pose proof HF as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma facts_xl : 0 <= ρ v_xl <= 4114. Proof. pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & (H & _) & _). exact H. Qed.
Lemma facts_win : sp_window_lo <= sp_val ρ /\ dec_top r ρ <= sp_window_hi.
Proof. pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & _). split; assumption. Qed.
Lemma facts_top8 : dec_top r ρ mod 8 = 0.
Proof. pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma len_av : Z.of_nat (length av) = ρ v_argc.
Proof. unfold av, dec_argv. rewrite len_dec_strs by (pose proof facts_argc; lia). pose proof facts_argc. lia. Qed.
Lemma len_ev : Z.of_nat (length ev) = ρ v_envc.
Proof. unfold ev, dec_envp. rewrite len_dec_strs by (pose proof facts_envc; lia). pose proof facts_envc. lia. Qed.
Lemma len_xfn : Z.of_nat (length xfn) = ρ v_xl.
Proof. unfold xfn, dec_execfn. rewrite length_map, length_seq. pose proof facts_xl. lia. Qed.

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

Lemma nth_x : forall j, 0 <= j < ρ v_xl -> nth (Z.to_nat j) xfn (Z_to_bv 8 0) = Z_to_bv 8 (ρ (xstrvar j)).
Proof. intros j Hj. unfold xfn, dec_execfn. rewrite nth_map_seq0 by lia. rewrite Z2Nat.id by lia. reflexivity. Qed.

Lemma tab_av : Z.of_nat (tab av) = ρ v_ta.
Proof. destruct HF as (_ & _ & _ & _ & Ht & _). rewrite Ht, total_arg_bytes_Z. reflexivity. Qed.
Lemma tab_ev : Z.of_nat (tab ev) = ρ v_te.
Proof. destruct HF as (_ & _ & _ & _ & _ & Ht & _). rewrite Ht, total_arg_bytes_Z. reflexivity. Qed.

Lemma u_sp : bv_unsigned spw = sp_val ρ.
Proof.
  pose proof facts_win as [W1 W2]. unfold dec_top, str_off in W2. pose proof facts_g. pose proof facts_argc. pose proof facts_envc.
  destruct HF as (_ & _ & _ & _ & Ht & Hte & _). pose proof (total_arg_bytes_nonneg (dec_argv ρ)). pose proof (total_arg_bytes_nonneg (dec_envp ρ)).
  pose proof facts_xl. pose proof facts_par. pose proof (Z.mod_pos_bound (ρ v_argc + ρ v_envc + 1) 2 ltac:(lia)).
  unfold spw. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64).
  unfold sp_window_lo, sp_window_hi in *. lia.
Qed.

Lemma items_par : Z.of_nat (block_items av ev mod 2) = ρ v_par.
Proof.
  rewrite facts_par. unfold block_items. rewrite Nat2Z.inj_mod, !Nat2Z.inj_add, len_av, len_ev.
  change (Z.of_nat 2) with 2. change (Z.of_nat 3) with 3.
  replace (ρ v_argc + ρ v_envc + 3) with ((ρ v_argc + ρ v_envc + 1) + 1 * 2) by lia. apply Z_mod_plus_full.
Qed.

Lemma HSz : Z.of_nat (block_head_size r av ev) = SB + Z.of_nat (auxv_size r) + 16 + 8 * ρ v_par.
Proof.
  unfold block_head_size. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul, items_par.
  unfold block_items, SB. rewrite !Nat2Z.inj_add, len_av, len_ev. cbn [Z.of_nat Pos.of_succ_nat]. lia.
Qed.

Lemma LSBz : Z.of_nat (launch_string_bytes av ev xfn) = ρ v_ta + ρ v_te + ρ v_xl + 1.
Proof.
  unfold launch_string_bytes. rewrite !Nat2Z.inj_add, !length_flatten_strings, len_xfn.
  fold (tab av) (tab ev). rewrite tab_av, tab_ev. reflexivity.
Qed.

Lemma u_top : bv_unsigned topw = dec_top r ρ.
Proof.
  pose proof u_sp. pose proof facts_win as [W1 W2]. unfold spw in *. rewrite Z_to_bv_unsigned in H.
  unfold topw. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64).
  unfold dec_top, str_off in *. pose proof facts_g. pose proof facts_argc. pose proof facts_envc. pose proof facts_xl.
  pose proof facts_par. pose proof (Z.mod_pos_bound (ρ v_argc + ρ v_envc + 1) 2 ltac:(lia)).
  destruct HF as (_ & _ & _ & _ & Ht & Hte & _). pose proof (total_arg_bytes_nonneg (dec_argv ρ)). pose proof (total_arg_bytes_nonneg (dec_envp ρ)).
  unfold sp_window_lo, sp_window_hi in *. unfold bv_wrap in H. lia.
Qed.

Lemma SOz : SO = SB + Z.of_nat (auxv_size r) + ρ v_g.
Proof. unfold SO, SB. lia. Qed.
Lemma SO_str_off : SO = str_off r ρ.
Proof. unfold SO, str_off. lia. Qed.

Lemma PADz : Z.of_nat (block_pad_len r spw topw av ev xfn) = ρ v_g - 16 - 8 * ρ v_par.
Proof.
  unfold block_pad_len. rewrite u_top, u_sp, LSBz, HSz. unfold dec_top, str_off.
  pose proof facts_g. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma B_eq : B = build_stack_bytes (dec_la r ρ) ph (Z_to_bv 64 (ρ v_ent)) spw topw av ev xfn
                   (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_gid)) (Z_to_bv 64 (ρ v_hw)) (dec_draw r ρ).
Proof. reflexivity. Qed.

Lemma str_base_eq : str_base topw av ev xfn = Z_to_bv 64 (sp_val ρ + SO).
Proof.
  unfold str_base, string_base_addr, topw. rewrite zsub_nat. f_equal.
  rewrite Nat2Z.inj_add, LSBz. unfold dec_top, str_off. lia.
Qed.

Theorem R7_length : Z.of_nat (length B) = SO + ρ v_ta + ρ v_te + ρ v_xl + 9.
Proof.
  rewrite B_eq. rewrite length_bsb. cbn [dec_la la_rseq]. rewrite !Nat2Z.inj_add, HSz, PADz, LSBz. lia.
Qed.

Lemma pre0 : forall L, pre 0 L = 0%nat.
Proof. reflexivity. Qed.
Lemma pre1 : forall (L : list (list byte)), L <> [] -> pre 1 L = (length (nth 0 L []) + 1)%nat.
Proof.
  intros [|x L] H; [contradiction|]. unfold pre, total_arg_bytes_nat. cbn.
  replace (firstn 0 L) with (@nil (list byte)) by reflexivity. cbn. lia.
Qed.

Theorem R1_argc : rdB B 0 8 = word_le8 (Z_to_bv 64 (ρ v_argc)).
Proof. rewrite B_eq, E1_argc, len_av. reflexivity. Qed.

Theorem R2_argv0 : rdB B 8 8 = word_le8 (Z_to_bv 64 (sp_val ρ + SO)).
Proof.
  pose proof facts_argc. pose proof len_av.
  replace 8%nat with (8 + 8 * 0)%nat at 1 by reflexivity.
  rewrite B_eq, E2_argv by lia. rewrite pre0, word_add_0, str_base_eq. reflexivity.
Qed.

Theorem R2_argv1 : 2 <= ρ v_argc -> rdB B 16 8 = word_le8 (Z_to_bv 64 (sp_val ρ + SO + ρ (lenvar 0) + 1)).
Proof.
  intros H2. pose proof len_av. pose proof (len_k 0 ltac:(lia)) as L0. change (Z.to_nat 0) with 0%nat in L0.
  replace 16%nat with (8 + 8 * 1)%nat by reflexivity.
  rewrite B_eq, E2_argv by lia. rewrite str_base_eq. unfold nat_to_word. rewrite zadd.
  rewrite pre1 by (intros Hn; fold av in Hn; rewrite Hn in *; cbn in *; lia).
  f_equal. f_equal. rewrite Nat2Z.inj_add, L0. cbn. lia.
Qed.

Theorem R2_argv1_null : ρ v_argc = 1 -> rdB B 16 8 = word_le8 (Z_to_bv 64 0).
Proof.
  intros H1. pose proof len_av as La. assert (Ha : length av = 1%nat) by lia.
  pose proof (E2_argv_null (dec_la r ρ) ph (Z_to_bv 64 (ρ v_ent)) spw topw av ev xfn
                (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_gid)) (Z_to_bv 64 (ρ v_hw)) (dec_draw r ρ)) as E.
  rewrite Ha in E. cbn [Nat.mul Nat.add] in E. rewrite B_eq. exact E.
Qed.

Theorem R3_envp : forall (j : nat), (Z.of_nat j < ρ v_envc)%Z ->
  rdB B (16 + 8 * Z.to_nat (ρ v_argc) + 8 * j) 8 = word_le8 (Z_to_bv 64 (sp_val ρ + SO + ρ v_ta + Z.of_nat (pre j ev))).
Proof.
  intros j Hj. pose proof len_av. pose proof len_ev. replace (Z.to_nat (ρ v_argc)) with (length av) by lia.
  rewrite B_eq, E3_envp by lia. rewrite str_base_eq. unfold nat_to_word. rewrite zadd.
  f_equal. f_equal. rewrite Nat2Z.inj_add, tab_av. lia.
Qed.

Theorem R3_null : rdB B (16 + 8 * Z.to_nat (ρ v_argc) + 8 * Z.to_nat (ρ v_envc)) 8 = word_le8 (Z_to_bv 64 0).
Proof.
  pose proof len_av. pose proof len_ev.
  replace (Z.to_nat (ρ v_argc)) with (length av) by lia. replace (Z.to_nat (ρ v_envc)) with (length ev) by lia.
  rewrite B_eq. apply E3_envp_null.
Qed.

(** the 26 pairs both layouts share, then the two rseq pairs under [r], then AT_NULL *)
Definition auxv_keys : list Z :=
  [33; 40; 41; 42; 43; 44; 45; 46; 47; 51; 16; 6; 17; 3; 4; 5; 7; 8; 9; 11; 12; 13; 14; 23; 25; 31]
  ++ (if r then [27; 28] else []) ++ [0].

Definition rnd_addr : Z := sp_val ρ + SB + Z.of_nat (auxv_size r) + 8 * ρ v_par.
Definition xfn_addr : Z := sp_val ρ + SO + ρ v_ta + ρ v_te.

Definition auxv_vals : list word :=
  [Z_to_bv 64 (ρ v_vd); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
   Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 (ρ v_mss); Z_to_bv 64 (ρ v_hw); Z_to_bv 64 4096; Z_to_bv 64 100;
   Z_to_bv 64 (Z.of_N (ph_addr ph)); Z_to_bv 64 (Z.of_N (ph_ent ph)); Z_to_bv 64 (Z.of_N (ph_num ph));
   Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 (ρ v_ent); Z_to_bv 64 (ρ v_uid); Z_to_bv 64 (ρ v_uid);
   Z_to_bv 64 (ρ v_gid); Z_to_bv 64 (ρ v_gid); Z_to_bv 64 0; Z_to_bv 64 rnd_addr; Z_to_bv 64 xfn_addr]
  ++ (if r then [Z_to_bv 64 28; Z_to_bv 64 32] else []) ++ [Z_to_bv 64 0].

Lemma rnd_ptr : at_random_ptr spw r av ev = Z_to_bv 64 rnd_addr.
Proof.
  unfold at_random_ptr, spw, nat_to_word. rewrite zadd. f_equal.
  pose proof HSz. pose proof facts_argc. pose proof facts_envc. pose proof facts_par.
  pose proof (Z.mod_pos_bound (ρ v_argc + ρ v_envc + 1) 2 ltac:(lia)).
  unfold SB in *. rewrite Nat2Z.inj_sub by lia. unfold rnd_addr, SB. lia.
Qed.

Lemma xfn_ptr : at_execfn_ptr topw xfn = Z_to_bv 64 xfn_addr.
Proof.
  unfold at_execfn_ptr, topw. rewrite zsub_nat. f_equal.
  rewrite !Nat2Z.inj_add, len_xfn. unfold xfn_addr, SO, dec_top, str_off. change (Z.of_nat 8) with 8. change (Z.of_nat 1) with 1. lia.
Qed.

Lemma auxv_nth : forall (i : nat), (i < auxv_count r)%nat ->
  nth i (auxv_entries (dec_la r ρ) ph (Z_to_bv 64 (ρ v_ent)) (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_gid))
           (Z_to_bv 64 (ρ v_hw)) (Z_to_bv 64 rnd_addr) (Z_to_bv 64 xfn_addr)) (Z_to_bv 64 0, Z_to_bv 64 0)
  = (Z_to_bv 64 (nth i auxv_keys 0), nth i auxv_vals (Z_to_bv 64 0)).
Proof.
  (* [r] is a section variable the [Let]s depend on, so case on the goal only *)
  unfold auxv_keys, auxv_vals. cbn [dec_la la_rseq].
  case r; intros i Hi; cbn [auxv_count] in Hi;
    [do 29 (destruct i as [|i]; [reflexivity|]) | do 27 (destruct i as [|i]; [reflexivity|])]; lia.
Qed.

Lemma soff : forall i : nat, struct_nat av ev = (24 + 8 * Z.to_nat (ρ v_argc) + 8 * Z.to_nat (ρ v_envc))%nat.
Proof. intros. pose proof len_av. pose proof len_ev. unfold struct_nat. lia. Qed.

Theorem R4_key : forall (i : nat), (i < auxv_count r)%nat ->
  rdB B (24 + 8 * Z.to_nat (ρ v_argc) + 8 * Z.to_nat (ρ v_envc) + 16 * i) 8 = word_le8 (Z_to_bv 64 (nth i auxv_keys 0)).
Proof.
  intros i Hi. rewrite <- (soff i). rewrite B_eq.
  destruct (E4_auxv (dec_la r ρ) ph (Z_to_bv 64 (ρ v_ent)) spw topw av ev xfn
              (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_gid)) (Z_to_bv 64 (ρ v_hw)) (dec_draw r ρ) i Hi) as [E _].
  rewrite E. unfold aux_ent. cbn [dec_la la_rseq]. rewrite rnd_ptr, xfn_ptr, auxv_nth by exact Hi. reflexivity.
Qed.

Theorem R4_val : forall (i : nat), (i < auxv_count r)%nat ->
  rdB B (24 + 8 * Z.to_nat (ρ v_argc) + 8 * Z.to_nat (ρ v_envc) + 16 * i + 8) 8 = word_le8 (nth i auxv_vals (Z_to_bv 64 0)).
Proof.
  intros i Hi. rewrite <- (soff i). rewrite B_eq.
  destruct (E4_auxv (dec_la r ρ) ph (Z_to_bv 64 (ρ v_ent)) spw topw av ev xfn
              (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_gid)) (Z_to_bv 64 (ρ v_hw)) (dec_draw r ρ) i Hi) as [_ E].
  rewrite E. unfold aux_ent. cbn [dec_la la_rseq]. rewrite rnd_ptr, xfn_ptr, auxv_nth by exact Hi. reflexivity.
Qed.

Lemma HSPAD : (block_head_size r av ev + block_pad_len r spw topw av ev xfn)%nat = Z.to_nat SO.
Proof. pose proof HSz. pose proof PADz. pose proof facts_g. lia. Qed.

Lemma SO_pos : 0 <= SO.
Proof.
  unfold SO. pose proof facts_argc. pose proof facts_envc. pose proof facts_g. pose proof facts_par.
  pose proof (Z.mod_pos_bound (ρ v_argc + ρ v_envc + 1) 2 ltac:(lia)). lia.
Qed.

Theorem R5_str : forall k j, 0 <= k < ρ v_argc -> 0 <= j <= ρ (lenvar k) ->
  nth (Z.to_nat (SO + Z.of_nat (pre (Z.to_nat k) av) + j)) B (Z_to_bv 8 0)
  = if j <? ρ (lenvar k) then Z_to_bv 8 (ρ (strvar k j)) else Z_to_bv 8 0.
Proof.
  intros k j Hk Hj. pose proof len_av. pose proof (len_k k Hk) as Lk. pose proof HSPAD. pose proof facts_g. pose proof SO_pos.
  replace (Z.to_nat (SO + Z.of_nat (pre (Z.to_nat k) av) + j))
    with (block_head_size r av ev + block_pad_len r spw topw av ev xfn + pre (Z.to_nat k) av + Z.to_nat j)%nat
    by lia.
  rewrite B_eq. cbn [dec_la]. rewrite (E5_argv_str (dec_la r ρ)) by lia.
  destruct (Z.ltb_spec j (ρ (lenvar k))) as [Hl|Hl].
  - rewrite app_nth1 by lia. apply nth_k; lia.
  - rewrite app_nth2 by lia. replace (Z.to_nat j - length (nth (Z.to_nat k) av []))%nat with 0%nat by lia. reflexivity.
Qed.

Theorem R5_str0 : forall j, 0 <= j <= ρ (lenvar 0) ->
  nth (Z.to_nat (SO + j)) B (Z_to_bv 8 0) = if j <? ρ (lenvar 0) then Z_to_bv 8 (ρ (strvar 0 j)) else Z_to_bv 8 0.
Proof.
  intros j Hj. pose proof facts_argc. rewrite <- (R5_str 0 j) by lia. f_equal. change (Z.to_nat 0) with 0%nat. rewrite pre0. lia.
Qed.

Theorem R5_str1 : 2 <= ρ v_argc -> forall j, 0 <= j <= ρ (lenvar 1) ->
  nth (Z.to_nat (SO + ρ (lenvar 0) + 1 + j)) B (Z_to_bv 8 0) = if j <? ρ (lenvar 1) then Z_to_bv 8 (ρ (strvar 1 j)) else Z_to_bv 8 0.
Proof.
  intros H2 j Hj. pose proof len_av. pose proof (len_k 0 ltac:(lia)) as L0. change (Z.to_nat 0) with 0%nat in L0.
  rewrite <- (R5_str 1 j) by lia. f_equal. change (Z.to_nat 1) with 1%nat.
  rewrite pre1 by (intros Hn; fold av in Hn; rewrite Hn in *; cbn in *; lia). lia.
Qed.

Theorem R5_xfn : forall j, 0 <= j <= ρ v_xl ->
  nth (Z.to_nat (SO + ρ v_ta + ρ v_te + j)) B (Z_to_bv 8 0) = if j <? ρ v_xl then Z_to_bv 8 (ρ (xstrvar j)) else Z_to_bv 8 0.
Proof.
  intros j Hj. pose proof len_xfn. pose proof tab_av. pose proof tab_ev. pose proof HSPAD. pose proof facts_g. pose proof SO_pos.
  replace (Z.to_nat (SO + ρ v_ta + ρ v_te + j))
    with (block_head_size r av ev + block_pad_len r spw topw av ev xfn + tab av + tab ev + Z.to_nat j)%nat
    by lia.
  rewrite B_eq. cbn [dec_la]. rewrite (E5_execfn (dec_la r ρ)) by lia.
  destruct (Z.ltb_spec j (ρ v_xl)) as [Hl|Hl].
  - rewrite app_nth1 by lia. apply nth_x; lia.
  - rewrite app_nth2 by lia. replace (Z.to_nat j - length xfn)%nat with 0%nat by lia. reflexivity.
Qed.

Theorem R6_random : rdB B (Z.to_nat (SB + Z.of_nat (auxv_size r) + 8 * ρ v_par)) 16 = word_le8 (Z_to_bv 64 (ρ v_r0)) ++ word_le8 (Z_to_bv 64 (ρ v_r1)).
Proof.
  destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hr0 & Hr1 & _).
  pose proof len_av. pose proof len_ev. pose proof items_par. pose proof facts_par.
  replace (Z.to_nat (SB + Z.of_nat (auxv_size r) + 8 * ρ v_par)) with (struct_nat av ev + auxv_size r + gap_nat av ev)%nat
    by (unfold struct_nat, gap_nat, SB; lia).
  rewrite B_eq. cbn [dec_la]. rewrite (E6_random (dec_la r ρ)). cbn [dec_draw ed_random]. unfold dec_random.
  apply random_split; assumption.
Qed.

End Read.
