(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim SjModel AtpModel OdModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_new
  Atp_h_defsA Od_hkit0A Od_lkitA Od_setup_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma oa_lib_fp_static : forall x, in_ranges LIB_FP x -> client_static x /\ 0x647c00 <= x < 0x647d88.
Proof.
  intros x (l & h & Hin & Hr). unfold LIB_FP in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst l h; split; [apply client_static_intro; lia| lia]|]). destruct Hin.
Qed.

Lemma od_zbytes_chars : forall bs, zbytes (od_chars bs) = bs.
Proof.
  intros bs. unfold zbytes, od_chars. rewrite map_map. rewrite <- (map_id bs) at 2. apply map_ext. intros b.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma od_chars_range : forall bs, Forall (fun c => 0 <= c < 256) (od_chars bs).
Proof.
  intros bs. unfold od_chars. induction bs as [|b bs IH]; cbn [map]; constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia.
Qed.
Lemma od_chars_length : forall bs, zlength (od_chars bs) = Z.of_nat (length bs).
Proof. intros bs. unfold od_chars, zlength. rewrite length_map. reflexivity. Qed.

Definition oa_P (d' : list Z) : nat := Nat.max (length (poffs d')) 1.
Definition oa_els (D : Z) (d' : list Z) : list (Z * Z) := map (pview D) (poffs d') ++ repeat (0, 0) (oa_P d' - length (poffs d')).

Lemma oa_els_length : forall D d', length (oa_els D d') = oa_P d'.
Proof. intros D d'. unfold oa_els, oa_P. rewrite length_app, length_map, repeat_length. lia. Qed.

Lemma oa_els_shape : forall D d', exists P0 rest,
  oa_els D d' = (P0, zlength (nth 0 (atp_parts d') [])) :: rest
  /\ (P0 = 0 /\ nth 0 (atp_parts d') [] = [] /\ d' = [] \/ P0 = D /\ d' <> [])
  /\ nth 0 (atp_parts d') [] = firstn (length (nth 0 (atp_parts d') [])) d'.
Proof.
  intros D d'. unfold oa_els, oa_P.
  pose proof (poffs_length d') as PL. pose proof (poffs_parts d') as PP.
  destruct (poffs d') as [|[o0 n0] tl0] eqn:EP.
  - cbn in PP. rewrite <- PP. cbn. exists 0, []. split; [reflexivity|]. split; [| reflexivity]. left. split; [reflexivity|]. split; [reflexivity|].
    destruct d' as [|c l]; [reflexivity|]. exfalso. rewrite poffs_eq in EP. exact (poffs_of_nonnil 0 (c :: l) EP).
  - assert (O0 : o0 = 0%nat).
    { rewrite poffs_eq in EP. destruct d' as [|c l]; [discriminate|]. rewrite poffs_of_unfold in EP. destruct (find_sep (c :: l)); congruence. }
    subst o0. rewrite <- PP. cbn [map nth fst snd skipn].
    assert (LN0 : (n0 <= length d')%nat) by (pose proof (poffs_bound d' (0%nat, n0) ltac:(rewrite EP; left; reflexivity)) as B; cbn in B; lia).
    assert (ZL : zlength (firstn n0 d') = Z.of_nat n0) by (unfold zlength; rewrite firstn_length; lia).
    rewrite ZL. replace (length (firstn n0 d')) with n0 by (rewrite firstn_length; clear - LN0; lia).
    cbn [map app]. unfold pview at 1. cbn [fst snd]. exists D, (map (pview D) tl0 ++ repeat (0, 0) (Nat.max (length ((0%nat, n0) :: tl0)) 1 - length ((0%nat, n0) :: tl0))). split; [f_equal; f_equal; lia|]. split; [| reflexivity].
    right. split; [reflexivity|]. intros E. subst d'. discriminate EP.
Qed.

Lemma od_vcost_pushes_app : forall a b c s,
  vcost_pushes (a + b) c s = vcost_pushes a c s + vcost_pushes b (vcap_iter a c s) (s + Z.of_nat a).
Proof.
  induction a as [|a IH]; intros b c s.
  - cbn [Nat.add vcost_pushes vcap_iter]. rewrite Nat2Z.inj_0, Z.add_0_r. lia.
  - cbn [Nat.add]. rewrite vcost_pushes_S, vcap_iter_S0, (IH b (vcap_after c s) (s + 1)), vcost_pushes_S.
    replace (s + 1 + Z.of_nat a) with (s + Z.of_nat (S a)) by lia. lia.
Qed.

Lemma od_vcost_nogrow : forall n c s, 0 <= s -> s + Z.of_nat n <= c -> vcost_pushes n c s = 0 /\ vcap_iter n c s = c.
Proof.
  induction n as [|n IH]; intros c s S0 H; [split; reflexivity|].
  rewrite vcost_pushes_S, vcap_iter_S0.
  assert (E1 : vcost_push c s = 0) by (unfold vcost_push; destruct (Z.ltb_spec s c); [reflexivity| lia]).
  assert (E2 : vcap_after c s = c) by (unfold vcap_after; destruct (Z.ltb_spec s c); [reflexivity| lia]).
  rewrite E1, E2. destruct (IH c (s + 1) ltac:(lia) ltac:(lia)) as [-> ->]. split; reflexivity.
Qed.

Fixpoint od_sumd (k : nat) (c : Z) : Z := match k with O => 0 | S k' => mcost (16 * (2 * c)) + od_sumd k' (2 * c) end.

Lemma od_sumd_nonneg : forall k c, 1 <= c -> 0 <= od_sumd k c.
Proof. induction k as [|k IH]; intros c Hc; cbn [od_sumd]; [lia|]. pose proof (mcost_nonneg (16 * (2 * c)) ltac:(lia)). specialize (IH (2 * c) ltac:(lia)). lia. Qed.

Lemma od_vcost_grow_bound : forall k n c s, 1 <= c -> 0 <= s <= c -> s + Z.of_nat n <= c * 2 ^ (Z.of_nat k) -> vcost_pushes n c s <= od_sumd k c.
Proof.
  induction k as [|k IH]; intros n c s C1 SC H.
  - rewrite Nat2Z.inj_0, Z.pow_0_r, Z.mul_1_r in H. destruct (od_vcost_nogrow n c s ltac:(lia) H) as [-> _]. cbn [od_sumd]. lia.
  - destruct (Z_le_gt_dec (s + Z.of_nat n) c) as [LE|GT].
    + destruct (od_vcost_nogrow n c s ltac:(lia) LE) as [-> _]. apply od_sumd_nonneg. exact C1.
    + set (a := Z.to_nat (c - s)).
      assert (EA : Z.of_nat a = c - s) by (subst a; rewrite Z2Nat.id; lia).
      assert (NB : (a < n)%nat) by lia.
      replace n with (a + S (n - a - 1))%nat by lia.
      rewrite od_vcost_pushes_app. destruct (od_vcost_nogrow a c s ltac:(lia) ltac:(lia)) as [-> ->].
      rewrite vcost_pushes_S. replace (s + Z.of_nat a) with c by lia.
      assert (EP : vcost_push c c = mcost (16 * (2 * c))).
      { unfold vcost_push, vcap_next. destruct (Z.ltb_spec c c); [lia|]. f_equal. f_equal. lia. }
      assert (EC : vcap_after c c = 2 * c) by (unfold vcap_after, vcap_next; destruct (Z.ltb_spec c c); lia).
      rewrite EP, EC. cbn [od_sumd].
      assert (R : vcost_pushes (n - a - 1) (2 * c) (c + 1) <= od_sumd k (2 * c)).
      { apply IH; [lia| lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in H by lia.
        replace (Z.of_nat (n - a - 1)%nat) with (Z.of_nat n - Z.of_nat a - 1) by lia. lia. }
      lia.
Qed.

Lemma od_sumd_25_1 : od_sumd 25 1 = 2200010752.
Proof. vm_compute. reflexivity. Qed.

Lemma oa_P_bound : forall l : list Z, zlength l < 2^26 -> Z.of_nat (oa_P l) <= 2^24 + 1.
Proof.
  intros l H. unfold oa_P. rewrite poffs_length. unfold atp_parts. unfold zlength in H.
  destruct l as [|c l']; [cbn; lia|].
  pose proof (split_go_count (S (length (c :: l'))) (c :: l')) as B. change (2^24) with 16777216. change (2^26) with 67108864 in H.
  set (k := length (split_go (S (length (c :: l'))) (c :: l'))) in *. set (L := length (c :: l')) in *. lia.
Qed.

Theorem od_vcb_ok : forall l : list Z, zlength l < 2^26 -> 8 + vcost_pushes (oa_P l) 0 0 <= OD_VEC_COST.
Proof.
  intros l H. pose proof (oa_P_bound l H) as PB.
  assert (P2 : (1 <= oa_P l)%nat) by (unfold oa_P; lia).
  destruct (oa_P l) as [|n] eqn:EP; [lia|].
  rewrite vcost_pushes_S. unfold vcost_push, vcap_after, vcap_next.
  replace (0 <? 0) with false by reflexivity.
  replace (Z.max (2 * 0) (0 + 1)) with 1 by reflexivity. replace (0 + 1) with 1 by reflexivity.
  pose proof (od_vcost_grow_bound 25 n 1 1 ltac:(lia) ltac:(lia)) as G.
  rewrite Z.mul_1_l in G. specialize (G ltac:(change (2 ^ Z.of_nat 25) with 33554432; lia)).
  rewrite od_sumd_25_1 in G.
  assert (M16 : mcost (16 * 1) = 2097152) by (vm_compute; reflexivity).
  rewrite M16. unfold OD_VEC_COST. change (2 ^ 31 + 2 ^ 26) with 2214592512. lia.
Qed.

Lemma od_vcost_le : forall l : list Z, vcost_pushes (length (poffs l)) 0 0 <= vcost_pushes (oa_P l) 0 0.
Proof.
  intros l.
  assert (G : forall a b, vcost_pushes a 0 0 <= vcost_pushes (a + b) 0 0).
  { intros a b. induction b as [|b IH]; [rewrite Nat.add_0_r; lia|].
    rewrite Nat.add_succ_r, vcost_pushes_snoc.
    pose proof (vcap_iter_inv (a + b) 0 0 ltac:(lia) ltac:(lia)) as VI.
    pose proof (vcost_push_nonneg (vcap_iter (a + b) 0 0) (0 + Z.of_nat (a + b)) ltac:(lia)). lia. }
  replace (oa_P l) with (length (poffs l) + (oa_P l - length (poffs l)))%nat by (unfold oa_P; lia). apply G.
Qed.

Lemma oa_vrepA_agree : forall (m m' : mem) V A cap size els,
  vrepA m V A cap size els -> agree_on (fun x => V <= x < V + 24 \/ A <= x < A + 16 * size) m m' -> vrepA m' V A cap size els.
Proof.
  intros m m' V A cap size els (E & R & C & A0 & AH & SV & BLK) AG. unfold vrepA.
  split; [exact E|]. split; [exact R|]. split; [exact C|]. split; [exact A0|]. split; [exact AH|]. split.
  - apply (rw_cells_agree_nw asegs m m' _ _ SV). eapply agree_sub; [exact AG|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
  - destruct BLK as [L|(C1 & A16 & AP & BE)]; [left; exact L| right]. split; [exact C1|]. split; [exact A16|]. split; [exact AP|].
    apply (rw_cells_agree_nw asegs m m' _ _ BE). eapply agree_sub; [exact AG|]. intros x Hx. rewrite velts_size in Hx. cbv beta. unfold zlength in E. lia.
Qed.

Lemma z8_inj : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z_to_bv 8 a = Z_to_bv 8 b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
  rewrite !bv_wrap_small in E by (unfold bv_modulus; cbn; lia). exact E.
Qed.

Lemma strip_bom_cases : forall s : list Z, bytes_ok s -> (3 <= length s)%nat ->
  (firstn 3 (zbytes s) = BOM_BYTES /\ strip_bom s = skipn 3 s /\ zlength (strip_bom s) = zlength s - 3)
  \/ (firstn 3 (zbytes s) <> BOM_BYTES /\ strip_bom s = s).
Proof.
  intros s OK L. destruct s as [|a [|b [|c r]]]; cbn [length] in L; try lia.
  inversion OK as [|? ? Ra OK1]; subst. inversion OK1 as [|? ? Rb OK2]; subst. inversion OK2 as [|? ? Rc _]; subst.
  destruct (Z.eq_dec a 239) as [Ea|Na]; [destruct (Z.eq_dec b 187) as [Eb|Nb]; [destruct (Z.eq_dec c 191) as [Ec|Nc]|]|].
  - left. subst. split; [reflexivity|]. split; [reflexivity|]. cbn [strip_bom]. unfold zlength. cbn [length]. lia.
  - right. split.
    + cbn [zbytes map firstn]. unfold BOM_BYTES. intros E. apply Nc. apply (z8_inj c 191 Rc ltac:(lia)). exact (f_equal (fun l => nth 2 l (Z_to_bv 8 0)) E).
    + subst. cbn [strip_bom]. destruct c as [|pc|pc]; try reflexivity.
      repeat (destruct pc as [pc|pc|]; try reflexivity). contradiction Nc. reflexivity.
  - right. split.
    + cbn [zbytes map firstn]. unfold BOM_BYTES. intros E. apply Nb. apply (z8_inj b 187 Rb ltac:(lia)). exact (f_equal (fun l => nth 1 l (Z_to_bv 8 0)) E).
    + subst. cbn [strip_bom]. destruct b as [|pb|pb]; try reflexivity.
      repeat (destruct pb as [pb|pb|]; try reflexivity). contradiction Nb. reflexivity.
  - right. split.
    + cbn [zbytes map firstn]. unfold BOM_BYTES. intros E. apply Na. apply (z8_inj a 239 Ra ltac:(lia)). exact (f_equal (fun l => nth 0 l (Z_to_bv 8 0)) E).
    + cbn [strip_bom]. destruct a as [|pa|pa]; try reflexivity.
      repeat (destruct pa as [pa|pa|]; try reflexivity). contradiction Na. reflexivity.
Qed.

Lemma strip_bom_short : forall s : list Z, (length s < 3)%nat -> strip_bom s = s.
Proof. intros s L. destruct s as [|a [|b [|c r]]]; cbn [length] in L; try lia; cbn [strip_bom]; try reflexivity.
  - destruct a as [|pa|pa]; try reflexivity. repeat (destruct pa as [pa|pa|]; try reflexivity).
  - destruct a as [|pa|pa]; try reflexivity. repeat (destruct pa as [pa|pa|]; try reflexivity).
    destruct b as [|pb|pb]; try reflexivity. repeat (destruct pb as [pb|pb|]; try reflexivity).
Qed.

Lemma od_s0_ok : forall dz, bytes_ok dz -> bytes_ok (od_s0 dz).
Proof.
  intros dz OK. destruct (oa_els_shape 0 (tl dz)) as (_ & _ & _ & _ & PREF).
  unfold od_s0, od_parts, od_rest. rewrite PREF. unfold bytes_ok in *.
  assert (T : Forall (fun b => 0 <= b < 256) (tl dz)) by (destruct dz as [|c l]; cbn [tl]; [exact OK| inversion OK; assumption]).
  rewrite <- (firstn_skipn (length (nth 0 (atp_parts (tl dz)) [])) (tl dz)) in T. apply Forall_app in T. exact (proj1 T).
Qed.
