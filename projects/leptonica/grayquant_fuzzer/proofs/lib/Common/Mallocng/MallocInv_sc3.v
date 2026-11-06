(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_tables MallocInv_steps MallocInv_hints MallocInv_sc MallocInv_sc2.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cnt2_rel (sc size c1 c2 : Z) : Prop :=
  c2 = c1 \/
  (sc mod 4 = 1 /\ 8 * 4096 < size * c1 /\ c2 = 2) \/
  (sc mod 4 = 2 /\ 4 * 4096 < size * c1 /\ c2 = 3) \/
  (sc mod 4 = 0 /\ 8 * 4096 < size * c1 /\ c2 = 3) \/
  (sc mod 4 = 0 /\ 2 * 4096 < size * c1 /\ c2 = 5).

Definition chk_cnt2 (sc : Z) : bool :=
  let size := 16 * size_class sc in
  forallb (fun c => let c1 := cnt1_of size c in
     (1 <=? c1) && (c1 <=? 32)
     && (negb ((sc mod 4 =? 1) && (8 * 4096 <? size * c1)) || (2 <=? c1))
     && (negb ((sc mod 4 =? 2) && (4 * 4096 <? size * c1)) || (3 <=? c1))
     && (negb ((sc mod 4 =? 0) && (8 * 4096 <? size * c1)) || (3 <=? c1))
     && (negb ((sc mod 4 =? 0) && (2 * 4096 <? size * c1)) || (5 <=? c1))
     (* [comment removed for export] *)
     && (negb (size * c1 + 16 <=? 2048) || (2 <=? c1))
     (* [comment removed for export] *)
     && (negb ((c1 =? 1) && (2048 <? size + 16)) || ((256 <=? size_class sc) || ((size + 16) mod 4096 =? 0))))
    (cnt_cands sc).

Lemma chk_cnt2s : forallb chk_cnt2 (Zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nimp : forall a b : bool, negb a || b = true -> a = true -> b = true.
Proof. intros [] []; cbn; congruence. Qed.

Lemma cnt_facts : forall sc c, 0 <= sc < 48 -> In c (cnt_cands sc) ->
  let size := 16 * size_class sc in
  let c1 := cnt1_of size c in
  1 <= c1 <= 32 /\ size * c1 < 2^20 /\
  (forall c2, cnt2_rel sc size c1 c2 -> 1 <= c2 <= c1) /\
  (size * c1 + 16 <= 2048 -> 2 <= c1) /\
  (c1 = 1 -> 2048 < size + 16 -> 256 <= size_class sc \/ (size + 16) mod 4096 = 0).
Proof.
  intros sc c Hsc Hc size c1.
  pose proof (proj1 (forallb_forall _ _) chk_cnt2s sc (Zseq_In 48 0 sc ltac:(llia))) as H.
  unfold chk_cnt2 in H. apply (proj1 (forallb_forall _ _)) with (x := c) in H; [| exact Hc].
  cbv zeta in H. fold size in H. fold c1 in H.
  repeat (apply andb_prop in H; destruct H as [H ?X]).
  apply Z.leb_le in H. apply Z.leb_le in X5.
  pose proof (proj1 (forallb_forall _ _) chk_cnt_spans sc (Zseq_In 48 0 sc ltac:(llia))) as SP.
  unfold chk_cnt_span in SP. apply (proj1 (forallb_forall _ _)) with (x := c) in SP; [| exact Hc]. apply Z.ltb_lt in SP.
  split; [llia|]. split; [exact SP|]. split; [| split].
  - intros c2 [-> | [(E & L & ->) | [(E & L & ->) | [(E & L & ->) | (E & L & ->)]]]]; [llia| | | |].
    + assert (B : (2 <=? c1) = true) by (apply (nimp _ _ X4); rewrite (proj2 (Z.eqb_eq _ _) E), (proj2 (Z.ltb_lt _ _) L); reflexivity). apply Z.leb_le in B. llia.
    + assert (B : (3 <=? c1) = true) by (apply (nimp _ _ X3); rewrite (proj2 (Z.eqb_eq _ _) E), (proj2 (Z.ltb_lt _ _) L); reflexivity). apply Z.leb_le in B. llia.
    + assert (B : (3 <=? c1) = true) by (apply (nimp _ _ X2); rewrite (proj2 (Z.eqb_eq _ _) E), (proj2 (Z.ltb_lt _ _) L); reflexivity). apply Z.leb_le in B. llia.
    + assert (B : (5 <=? c1) = true) by (apply (nimp _ _ X1); rewrite (proj2 (Z.eqb_eq _ _) E), (proj2 (Z.ltb_lt _ _) L); reflexivity). apply Z.leb_le in B. llia.
  - intros Hn. assert (B : (2 <=? c1) = true) by (apply (nimp _ _ X0); apply Z.leb_le; exact Hn). apply Z.leb_le in B. llia.
  - intros E L. assert (B : (256 <=? size_class sc) || ((size + 16) mod 4096 =? 0) = true)
      by (apply (nimp _ _ X); rewrite (proj2 (Z.eqb_eq _ _) E), (proj2 (Z.ltb_lt _ _) L); reflexivity).
    apply Bool.orb_prop in B. destruct B as [B | B]; [left; apply Z.leb_le in B; exact B | right; apply Z.eqb_eq in B; exact B].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pow2_le32 : forall k, 0 <= k <= 32 -> 0 < 2^k <= 2^32.
Proof. intros k Hk. split; [apply Z.pow_pos_nonneg; llia | apply Z.pow_le_mono_r; llia]. Qed.

Lemma mod32_of_mod64 : forall x, (x mod 2^64) mod 2^32 = x mod 2^32.
Proof. intros x. apply Z.mod_mod_divide. exists (2^32). reflexivity. Qed.

(* [comment removed for export] *)
Lemma tail_av_word : forall adx, 0 <= adx < 32 ->
  bv_unsigned (v_addi (v_sllw (wlit 2) (Z_to_bv 64 adx)) (-1)) mod 2^32 = 2^(adx+1) - 1.
Proof.
  intros adx Ha. rewrite v_sllw_2 by llia. rewrite (Z.mod_small adx 32) by llia.
  pose proof (pow2_le32 (adx + 1) ltac:(llia)) as Hp.
  rewrite w32_eq, v_addi_Z, uZ_mod, mod32_of_mod64.
  replace (sx32 (2 ^ (adx + 1)) + -1) with (sx32 (2 ^ (adx + 1)) - 1) by llia.
  rewrite <- Zminus_mod_idemp_l, sx32_eqmod, Zminus_mod_idemp_l.
  destruct (Z.eq_dec (adx + 1) 32) as [E | NE].
  - rewrite E. reflexivity.
  - assert (2^(adx+1) < 2^32) by (apply Z.pow_lt_mono_r; llia). apply Z.mod_small. llia.
Qed.

(* [comment removed for export] *)
Lemma lxor_all_ones : forall a, 0 <= a < 2^64 -> Z.lxor a (2^64 + -1) = 2^64 - 1 - a.
Proof.
  intros a Hr. pose proof (Z.add_nocarry_lxor a (2^64 - 1 - a)) as X.
  assert (D : Z.land a (2^64 - 1 - a) = 0).
  { change (2^64) with (2 ^ Z.of_nat 64). apply land_compl. change (2 ^ Z.of_nat 64) with (2^64). llia. }
  specialize (X D). replace (2^64 + -1) with (2^64 - 1) by llia.
  assert (E : Z.lxor a (2^64 - 1 - a) = 2^64 - 1) by llia.
  apply (f_equal (Z.lxor a)) in E. rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in E. symmetry. exact E.
Qed.

Lemma sx32_decomp : forall x, exists k, sx32 x = x mod 2^32 + k * 2^32.
Proof.
  intros x. unfold sx32. destruct (x mod 2^32 <? 2^31); [exists 0; llia | exists (2^32 - 1); llia].
Qed.

Lemma tail_fr_word : forall c adx, 0 <= adx -> adx + 1 <= c <= 32 ->
  bv_unsigned (v_add (v_sllw (wlit 2) (v_addi (Z_to_bv 64 c) (-1))) (v_xori (w32 (2^(adx+1) - 1)) (-1))) mod 2^32
  = 2^c - 2^(adx+1).
Proof.
  intros c adx Ha Hc. rewrite v_addi_Z. rewrite v_sllw_2 by llia.
  replace ((c + -1) mod 32 + 1) with c by (rewrite Z.mod_small by llia; llia).
  pose proof (pow2_le32 (adx + 1) ltac:(llia)) as Hp. pose proof (pow2_le32 c ltac:(llia)) as Hc2.
  assert (Hlt : 2^(adx+1) <= 2^c) by (apply Z.pow_le_mono_r; llia).
  rewrite !w32_eq. pose proof (sx32_range (2^c)) as R1. pose proof (sx32_range (2^(adx+1) - 1)) as R2.
  rewrite v_xori_negZ by llia. rewrite v_add_Z, uZ_mod, mod32_of_mod64.
  rewrite lxor_all_ones by llia.
  destruct (sx32_decomp (2^c)) as [k1 E1]. destruct (sx32_decomp (2^(adx+1) - 1)) as [k2 E2].
  rewrite (Z.mod_small (2^(adx+1) - 1) (2^32)) in E2 by llia.
  rewrite E1, E2.
  replace (2^c mod 2^32 + k1 * 2^32 + (2^64 - 1 - (2^(adx+1) - 1 + k2 * 2^32)))
    with ((2^c mod 2^32 - 2^(adx+1)) + (k1 - k2 + 2^32) * 2^32) by llia.
  rewrite Z.mod_add by llia. rewrite Zminus_mod_idemp_l. apply Z.mod_small. llia.
Qed.

(* [comment removed for export] *)
Lemma tail_aib_word : forall b adx, 0 <= b < 256 -> 0 <= adx < 32 ->
  v_or (v_andi (Z_to_bv 64 b) 224) (v_andi (Z_to_bv 64 adx) 31) = Z_to_bv 64 (Z.lor adx (Z.land b 224)) /\
  0 <= Z.lor adx (Z.land b 224) < 256 /\ Z.lor adx (Z.land b 224) mod 32 = adx.
Proof.
  intros b adx Hb Ha. destruct (aib_byte_facts adx b Ha Hb) as [R M].
  pose proof (land_lt_pow2 b 224 8 ltac:(llia) ltac:(llia) ltac:(llia)) as Hx. change (2^8) with 256 in Hx.
  split; [| auto]. rewrite !v_andi_Z by llia. rewrite land_31, (Z.mod_small adx 32) by llia.
  rewrite v_or_Z by llia. rewrite Z.lor_comm. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tail_w32_word : forall sc c wm, 0 <= sc < 48 -> 1 <= c <= 32 -> 0 <= wm < 2^62 ->
  v_addi (v_or (v_or (v_srli (v_slli (Z_to_bv 64 sc) 58) 52) (v_andi (v_addi (Z_to_bv 64 c) (-1)) 31)) (v_and (Z_to_bv 64 wm) PAGEMASK)) 32
  = Z_to_bv 64 (4096 * (wm / 4096) + 64 * sc + 32 + (c - 1)).
Proof.
  intros sc c wm Hsc Hc Hwm.
  rewrite v_slli_Z by llia. rewrite <- (ZZ_mod (sc * 2^58)).
  pose proof (Z.mod_pos_bound (sc * 2^58) (2^64) ltac:(llia)) as M1.
  rewrite v_srli_Z by llia.
  assert (E1 : (sc * 2^58) mod 2^64 / 2^52 = 64 * sc).
  { change (2^64) with (2^6 * 2^58). rewrite Z.mul_mod_distr_r by llia. rewrite (Z.mod_small sc (2^6)) by llia.
    change (2^58) with (2^6 * 2^52). rewrite Z.mul_assoc, Z.div_mul by llia. llia. }
  rewrite E1. rewrite v_addi_Z, v_andi_Z by llia. rewrite land_31 by llia. rewrite (Z.mod_small (c + -1) 32) by llia.
  rewrite v_or_Z by llia.
  assert (E2 : Z.lor (64 * sc) (c + -1) = 64 * sc + (c - 1)).
  { rewrite Z.lor_comm. replace (64 * sc) with (sc * 2^6) by llia. rewrite lor_low_high by llia. llia. }
  rewrite E2. rewrite PAGEMASK_eq, v_and_Z by llia. rewrite land_pagemask by llia.
  pose proof (Z.div_pos wm 4096 ltac:(llia) ltac:(llia)). assert (4096 * (wm / 4096) <= wm) by (apply Z.mul_div_le; llia).
  rewrite v_or_Z by llia.
  assert (E3 : Z.lor (64 * sc + (c - 1)) (4096 * (wm / 4096)) = 64 * sc + (c - 1) + 4096 * (wm / 4096)).
  { replace (4096 * (wm / 4096)) with ((wm / 4096) * 2^12) by llia. rewrite lor_low_high by llia. llia. }
  rewrite E3. rewrite v_addi_Z. f_equal. llia.
Qed.

Lemma grp_word_decode : forall q sc c, 0 <= q -> 0 <= sc < 48 -> 1 <= c <= 32 ->
  let W := 4096 * q + 64 * sc + 32 + (c - 1) in
  w_last W = c - 1 /\ w_freeable W = 1 /\ w_sc W = sc /\ w_maplen W = q /\ 0 <= W.
Proof.
  intros q sc c Hq Hsc Hc W. unfold w_last, w_freeable, w_sc, w_maplen. subst W.
  split; [| split; [| split; [| split; [| llia]]]].
  - replace (4096 * q + 64 * sc + 32 + (c - 1)) with ((c - 1) + (128 * q + 2 * sc + 1) * 32) by llia. rewrite Z.mod_add by llia. apply Z.mod_small. llia.
  - replace (4096 * q + 64 * sc + 32 + (c - 1)) with ((32 + (c - 1)) + (64 * q + sc) * 64) by llia.
    replace ((32 + (c - 1) + (64 * q + sc) * 64) / 32) with (1 + (64 * q + sc) * 2).
    2:{ symmetry. replace ((32 + (c - 1) + (64 * q + sc) * 64)) with ((c - 1) + (1 + (64 * q + sc) * 2) * 32) by llia. rewrite Z.div_add by llia. rewrite Z.div_small by llia. llia. }
    rewrite Z.mod_add by llia. reflexivity.
  - replace ((4096 * q + 64 * sc + 32 + (c - 1)) / 64) with (sc + q * 64).
    2:{ symmetry. replace (4096 * q + 64 * sc + 32 + (c - 1)) with ((32 + (c - 1)) + (sc + q * 64) * 64) by llia. rewrite Z.div_add by llia. rewrite Z.div_small by llia. llia. }
    rewrite Z.mod_add by llia. apply Z.mod_small. llia.
  - replace (4096 * q + 64 * sc + 32 + (c - 1)) with ((64 * sc + 32 + (c - 1)) + q * 4096) by llia. rewrite Z.div_add by llia. rewrite Z.div_small by llia. llia.
Qed.

(* [comment removed for export] *)
Lemma tail_avdec_word : forall av, 1 <= av < 2^32 ->
  bv_unsigned (v_addi (w32 av) (-1)) mod 2^32 = av - 1.
Proof.
  intros av Hav. rewrite w32_eq, v_addi_Z, uZ_mod, mod32_of_mod64.
  destruct (sx32_decomp av) as [k E]. rewrite E. rewrite (Z.mod_small av (2^32)) by llia.
  replace (av + k * 2^32 + -1) with ((av - 1) + k * 2^32) by llia. rewrite Z.mod_add by llia. apply Z.mod_small. llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma half_word : v_srli (Z_to_bv 64 4096) 1 = Z_to_bv 64 2048.
Proof. rewrite v_srli_Z by llia. reflexivity. Qed.

Lemma cnt1_word : forall c szc, 1 <= c <= 32 -> 1 <= szc <= 8191 ->
  (if c_eq (Z_to_bv 64 c) (wlit 1) then v_subw (wlit 2) (v_sltu (v_srli (Z_to_bv 64 4096) 1) (v_addi (Z_to_bv 64 (16 * szc)) 16)) else Z_to_bv 64 c)
  = Z_to_bv 64 (cnt1_of (16 * szc) c).
Proof.
  intros c szc Hc Hs. unfold wlit, cnt1_of. rewrite c_eq_Z by llia.
  destruct (c =? 1) eqn:E; [| reflexivity].
  rewrite half_word, v_addi_Z, v_sltu_Z by llia. rewrite v_subw_Z by (destruct (2048 <? 16 * szc + 16); llia).
  destruct (2048 <? 16 * szc + 16); rewrite swrap32_small by llia; reflexivity.
Qed.

Lemma nest_test_word : forall szc c1, 1 <= szc <= 8191 -> 1 <= c1 <= 32 ->
  negb (c_ltu (v_srli (Z_to_bv 64 4096) 1) (v_addi (v_mul (Z_to_bv 64 (16 * szc)) (Z_to_bv 64 c1)) 16)) = (16 * szc * c1 + 16 <=? 2048).
Proof.
  intros szc c1 Hs Hc. rewrite half_word, v_mul_Z, v_addi_Z, c_ltu_Z by lnia.
  destruct (Z.leb_spec (16 * szc * c1 + 16) 2048); [rewrite (proj2 (Z.ltb_ge _ _)) by llia | rewrite (proj2 (Z.ltb_lt _ _)) by llia]; reflexivity.
Qed.

Definition cnt2w (sc usage2 pg a4 cnt1 : word) (nosmall : bool) : word :=
  if negb (c_ltu usage2 (v_slliw cnt1 2)) then cnt1
  else if nosmall then cnt1
  else let a5 := v_andi sc 3 in
       let a6 := v_slli pg 3 in
       if c_eq a5 (wlit 1) && c_ltu a6 a4 then wlit 2
       else if c_eq a5 (wlit 2) && c_ltu (v_slli pg 2) a4 then wlit 3
       else if is0 a5 && c_ltu a6 a4 then wlit 3
       else if is0 a5 && c_ltu (v_slli pg 1) a4 then wlit 5
       else cnt1.

Lemma cnt2_word : forall sc szc c1 usage2 nosmall, 0 <= sc < 48 -> 1 <= szc <= 8191 -> 1 <= c1 <= 32 ->
  exists c2, cnt2_rel sc (16 * szc) c1 c2 /\
    cnt2w (Z_to_bv 64 sc) usage2 (Z_to_bv 64 4096) (Z_to_bv 64 (16 * szc * c1)) (Z_to_bv 64 c1) nosmall = Z_to_bv 64 c2.
Proof.
  intros sc szc c1 usage2 nosmall Hsc Hs Hc. unfold cnt2w, cnt2_rel, wlit.
  destruct (negb (c_ltu usage2 (v_slliw (Z_to_bv 64 c1) 2))); [exists c1; auto|].
  destruct nosmall; [exists c1; auto|].
  rewrite v_andi_Z by llia. assert (E3 : Z.land sc 3 = sc mod 4) by (change 3 with (2^2 - 1); rewrite land_ones_low by llia; reflexivity). rewrite E3.
  pose proof (Z.mod_pos_bound sc 4 ltac:(llia)).
  rewrite !v_slli_Z by llia. change (2^3) with 8. change (2^2) with 4. change (2^1) with 2.
  rewrite !c_eq_Z, !c_ltu_Z, is0_Z by lnia.
  destruct (Z.eqb_spec (sc mod 4) 1) as [E1|N1]; cbn [andb].
  { destruct (Z.ltb_spec (4096 * 8) (16 * szc * c1)); [exists 2; split; [right; left; llia | reflexivity]|].
    replace (sc mod 4 =? 2) with false by (symmetry; apply Z.eqb_neq; llia). replace (sc mod 4 =? 0) with false by (symmetry; apply Z.eqb_neq; llia). cbn. exists c1; auto. }
  destruct (Z.eqb_spec (sc mod 4) 2) as [E2|N2]; cbn [andb].
  { destruct (Z.ltb_spec (4096 * 4) (16 * szc * c1)); [exists 3; split; [right; right; left; llia | reflexivity]|].
    replace (sc mod 4 =? 0) with false by (symmetry; apply Z.eqb_neq; llia). cbn. exists c1; auto. }
  destruct (Z.eqb_spec (sc mod 4) 0) as [E0|N0]; cbn [andb].
  { destruct (Z.ltb_spec (4096 * 8) (16 * szc * c1)); [exists 3; split; [right; right; right; left; llia | reflexivity]|].
    destruct (Z.ltb_spec (4096 * 2) (16 * szc * c1)); [exists 5; split; [right; right; right; right; llia | reflexivity]|].
    exists c1; auto. }
  exists c1; auto.
Qed.

Lemma roundup_word16 : forall x, 0 <= x < 2^40 ->
  v_addi (v_add (Z_to_bv 64 x) (v_and (v_sub (wlit (2^64 - 16)) (Z_to_bv 64 x)) (v_addi (Z_to_bv 64 4096) (-1)))) 16
  = Z_to_bv 64 (page_round_up_Z (x + 16)).
Proof.
  intros x Hx. unfold wlit. rewrite v_sub_Z, v_addi_Z.
  rewrite v_and_Z by llia. change (4096 + -1) with (2^12 - 1). rewrite land_ones_low by llia.
  rewrite v_add_Z, v_addi_Z. f_equal. unfold page_round_up_Z, page_size.
  pose proof (Z.mod_pos_bound (2^64 - 16 - x) (2^12) ltac:(llia)) as M.
  pose proof (Z.div_mod (2^64 - 16 - x) (2^12) ltac:(llia)) as D.
  pose proof (Z.div_mod (x + 16 + 4096 - 1) 4096 ltac:(llia)) as D2. pose proof (Z.mod_pos_bound (x + 16 + 4096 - 1) 4096 ltac:(llia)) as M2.
  change (2^12) with 4096 in *. lnia.
Qed.

(* [comment removed for export] *)
Lemma roundup_word20 : forall x, 0 <= x < 2^40 ->
  v_addi (v_add (Z_to_bv 64 x) (v_and (v_addi (Z_to_bv 64 4096) (-1)) (v_sub (wlit (2^64 - 20)) (Z_to_bv 64 x)))) 20
  = Z_to_bv 64 (page_round_up_Z (x + 20)).
Proof.
  intros x Hx. unfold wlit. rewrite v_sub_Z, v_addi_Z.
  rewrite v_and_Z by llia. change (4096 + -1) with (2^12 - 1). rewrite Z.land_comm, land_ones_low by llia.
  rewrite v_add_Z, v_addi_Z. f_equal. unfold page_round_up_Z, page_size.
  pose proof (Z.mod_pos_bound (2^64 - 20 - x) (2^12) ltac:(llia)) as M.
  pose proof (Z.div_mod (2^64 - 20 - x) (2^12) ltac:(llia)) as D.
  pose proof (Z.div_mod (x + 20 + 4096 - 1) 4096 ltac:(llia)) as D2. pose proof (Z.mod_pos_bound (x + 20 + 4096 - 1) 4096 ltac:(llia)) as M2.
  change (2^12) with 4096 in *. lnia.
Qed.

Lemma page_round_up_Z_spec : forall x, 0 <= x -> x <= page_round_up_Z x < x + 4096 /\ page_round_up_Z x mod 4096 = 0.
Proof.
  intros x Hx. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (x + 4096 - 1) 4096 ltac:(llia)). pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(llia)).
  split; [llia|]. rewrite Z.mod_mul by llia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition cn3w (nosmall : bool) (cnt2 needed req pg size usage2 : word) : word * word :=
  if nosmall then (cnt2, needed)
  else if c_ltu (wlit 7) cnt2 then (cnt2, needed)
  else let r := v_addi (v_add req (v_and (v_addi pg (-1)) (v_sub (wlit (2^64 - 20)) req))) 20 in
       if c_ltu r (v_addi size 16) then (wlit 1, r)
       else if c_ltu r (v_slli pg 2) then (cnt2, needed)
       else if c_ltu usage2 (v_slliw cnt2 1) then (wlit 1, r)
       else (cnt2, needed).

Lemma cn3_word : forall nosmall c2 n2 req szc usage2, 1 <= c2 <= 32 -> 0 <= n2 < 2^64 -> 0 <= req < 2^40 -> 1 <= szc <= 8191 ->
  exists c3 n3, cn3w nosmall (Z_to_bv 64 c2) (Z_to_bv 64 n2) (Z_to_bv 64 req) (Z_to_bv 64 4096) (Z_to_bv 64 (16 * szc)) usage2
               = (Z_to_bv 64 c3, Z_to_bv 64 n3) /\
    ((c3 = c2 /\ n3 = n2) \/
     (c3 = 1 /\ n3 = page_round_up_Z (req + 20) /\ (n3 < 16 * szc + 16 \/ 4 * 4096 <= n3))).
Proof.
  intros nosmall c2 n2 req szc usage2 Hc Hn Hr Hs. unfold cn3w, wlit.
  destruct nosmall; [exists c2, n2; auto|].
  rewrite c_ltu_Z by llia. destruct (7 <? c2); [exists c2, n2; auto|].
  rewrite roundup_word20 by llia. destruct (page_round_up_Z_spec (req + 20) ltac:(llia)) as [B _].
  rewrite v_addi_Z, v_slli_Z by llia. change (4096 * 2^2) with 16384. rewrite !c_ltu_Z by llia.
  destruct (Z.ltb_spec (page_round_up_Z (req + 20)) (16 * szc + 16)); [eexists 1, _; split; [reflexivity | right; auto]|].
  destruct (Z.ltb_spec (page_round_up_Z (req + 20)) 16384); [exists c2, n2; auto|].
  destruct (c_ltu usage2 (v_slliw (Z_to_bv 64 c2) 1)); [eexists 1, _; split; [reflexivity | right; split; [reflexivity | split; [reflexivity | right; llia]]]|].
  exists c2, n2; auto.
Qed.

(* [comment removed for export] *)
Lemma maplen_word : forall n3, 0 <= n3 < 2^62 -> n3 mod 4096 = 0 ->
  v_or (v_srli (v_slli (Z_to_bv 64 0) 52) 52) (v_and (Z_to_bv 64 n3) PAGEMASK) = Z_to_bv 64 n3.
Proof.
  intros n3 Hn Hm. rewrite v_slli_Z, v_srli_Z by llia. change (0 * 2^52 / 2^52) with 0.
  rewrite PAGEMASK_eq, v_and_Z by llia. rewrite land_pagemask by llia. rewrite v_or_Z by lnia. rewrite Z.lor_0_l.
  f_equal. pose proof (Z.div_mod n3 4096 ltac:(llia)). llia.
Qed.

(* [comment removed for export] *)
Lemma maplen0_word : v_srli (v_slli (Z_to_bv 64 0) 52) 52 = Z_to_bv 64 0.
Proof. rewrite v_slli_Z, v_srli_Z by llia. reflexivity. Qed.

Lemma aimax_word : forall szc, 1 <= szc <= 8191 -> v_divu (wlit 4080) (Z_to_bv 64 (16 * szc)) = Z_to_bv 64 (4080 / (16 * szc)).
Proof. intros szc Hs. unfold wlit. rewrite v_divu_Z by llia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma aidx_word : forall c3 q, 1 <= c3 <= 32 -> 0 <= q < 2^62 ->
  let a2 := if c_ltu (Z_to_bv 64 c3) (Z_to_bv 64 q) then Z_to_bv 64 c3 else Z_to_bv 64 q in
  v_and (v_addi (v_sltu a2 (v_addi a2 (-1))) (-1)) (v_addi a2 (-1)) = Z_to_bv 64 (Z.max (Z.min c3 q - 1) 0).
Proof.
  intros c3 q Hc Hq a2.
  assert (Ea : a2 = Z_to_bv 64 (Z.min c3 q)).
  { subst a2. rewrite c_ltu_Z by llia. destruct (Z.ltb_spec c3 q); f_equal; llia. }
  rewrite Ea. set (a := Z.min c3 q). assert (Ha : 0 <= a <= 32) by (subst a; llia).
  rewrite v_addi_Z. destruct (Z.eq_dec a 0) as [E0 | NE].
  - rewrite E0. change (0 + -1) with (-1). rewrite <- (ZZ_mod (-1)). change ((-1) mod 2^64) with (2^64 - 1).
    rewrite v_sltu_Z by llia. replace (0 <? 2^64 - 1) with true by reflexivity. rewrite v_addi_Z. change (1 + -1) with 0.
    rewrite v_and_Z by llia. rewrite Z.land_0_l. reflexivity.
  - rewrite v_sltu_Z by llia. replace (a <? a + -1) with false by (symmetry; apply Z.ltb_ge; llia). rewrite v_addi_Z. change (0 + -1) with (-1).
    rewrite <- (ZZ_mod (-1)). change ((-1) mod 2^64) with (2^64 - 1).
    rewrite v_and_Z by llia. change (2^64 - 1) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by llia. rewrite Z.mod_small by llia. f_equal. llia.
Qed.

(* [comment removed for export] *)
Lemma sextw_small : forall j, 0 <= j < 2^31 -> v_addiw (Z_to_bv 64 j) 0 = Z_to_bv 64 j.
Proof. intros j Hj. rewrite v_addiw_Z by llia. rewrite Z.add_0_r, swrap32_small by llia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bounce_d_word : forall sc, 0 <= sc < 48 ->
  (sc < 7 -> c_ltu (wlit 31) (v_addiw (Z_to_bv 64 sc) (-7)) = true) /\
  (7 <= sc -> v_addiw (Z_to_bv 64 sc) (-7) = Z_to_bv 64 (sc - 7)).
Proof.
  intros sc Hsc. rewrite v_addiw_Z by llia. rewrite swrap32_small by llia. split; intros H.
  - unfold wlit. rewrite <- (ZZ_mod (sc + -7)). pose proof (Z.mod_pos_bound (sc + -7) (2^64) ltac:(llia)). rewrite c_ltu_Z by llia.
    apply Z.ltb_lt. replace (sc + -7) with ((2^64 + sc - 7) + (-1) * 2^64) by llia. rewrite Z.mod_add by llia. rewrite Z.mod_small; llia.
  - f_equal; llia.
Qed.

End WithLayout.
