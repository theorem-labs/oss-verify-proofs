(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its module paths and module names changed; 470 of its 537 lines of code are new or changed and 429 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1h YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
JsonScalar JtokIs DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoRo
DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut DiscoArm3JsonC2Defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require DiscoEntBody.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import McConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_jscalar_model disco_json_text disco_json_reader_model jtok_is_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb slot_ser_Pq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac jk_bvne := let Hq := fresh "Hq" in intro Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate Hq.

Lemma jk_bytes_map : forall l : list Z, Forall (fun c => 0 <= c < 256) l -> map bv_unsigned (map (Z_to_bv 8) l) = l.
Proof.
  intros l H. induction H as [|z l Hz _ IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma jk_lzeqb : forall a b, lzeqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn; split; intros H; try congruence.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. subst. reflexivity.
  - inversion H. subst. rewrite Z.eqb_refl. apply IH. reflexivity.
Qed.

Lemma jk_forall_fs : forall {A} (P : A -> Prop) l a b, Forall P l -> Forall P (firstn a (skipn b l)).
Proof.
  intros A P l a b H. apply Forall_forall. intros x Hx. rewrite Forall_forall in H. apply H.
  rewrite <- (firstn_skipn b l). apply in_or_app. right. rewrite <- (firstn_skipn a (skipn b l)).
  apply in_or_app. left. exact Hx.
Qed.

Lemma jk_bridge : forall (Bz w : list Z) (ks kl : Z),
  Forall (fun c => 0 <= c < 256) Bz -> Forall (fun c => 0 < c < 256) w ->
  0 <= ks -> 0 <= kl -> kl < 2 ^ 64 -> ks + kl <= jlen Bz ->
  (jtok_match 1 1 (Z_to_bv 64 kl) (map (Z_to_bv 8) (firstn (length w) (skipn (Z.to_nat ks) Bz)))
     (map (Z_to_bv 8) w) <-> jtok_is Bz (1, ks, kl) 1 w = true).
Proof.
  intros Bz w ks kl HB HW Hks Hkl Hkl64 Hb. unfold jlen in Hb.
  assert (HW' : Forall (fun c => 0 <= c < 256) w).
  { apply Forall_forall. intros c Hc. rewrite Forall_forall in HW. specialize (HW c Hc). lia. }
  assert (HS : Forall (fun c => 0 <= c < 256) (firstn (length w) (skipn (Z.to_nat ks) Bz)))
    by (apply jk_forall_fs; exact HB).
  unfold jtok_match, jtok_is, tv_kind, tv_text. cbn [fst snd].
  rewrite unsigned_lit_small by lia. rewrite length_map.
  split.
  - intros (_ & E2 & E3). rewrite E2, !Z.eqb_refl, Nat2Z.id. cbn [andb]. apply jk_lzeqb.
    apply (f_equal (map bv_unsigned)) in E3. rewrite (jk_bytes_map _ HS), (jk_bytes_map _ HW') in E3. exact E3.
  - intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [_ H2].
    apply Z.eqb_eq in H2. apply jk_lzeqb in H3. split; [reflexivity|]. split; [exact H2|].
    rewrite H2, Nat2Z.id in H3. rewrite H3. reflexivity.
Qed.

Lemma jk_zs_range : forall (rd : Z -> option Z) Bs lo len a n,
  zero_shadow rd Bs lo len -> lo <= a -> a + n + 16 <= lo + len -> range_addressable rd Bs a n.
Proof.
  intros rd Bs lo len a n Hz H1 H2 x Hx. exists 0. split; [|left; reflexivity].
  unfold zero_shadow, shadow_of_addr in *.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Dl. pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as Ml.
  pose proof (Z.div_mod len 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound len 8 ltac:(lia)) as Mn.
  replace (Bs + x / 8) with (Bs + lo / 8 + (x / 8 - lo / 8)) by lia.
  apply Hz. lia.
Qed.

Lemma jk_zs_hull : forall (rd : Z -> option Z) lo len a n,
  zero_shadow rd SHADOW_OFF lo len -> lo + 64 <= a -> a + n + 80 <= lo + len -> 0 < n -> shadow_hull_vis rd a n.
Proof.
  intros rd lo len a n Hz H1 H2 Hn s Hs. unfold zero_shadow, shadow_of_addr in Hz. unfold shadow_addr in Hs.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ma.
  pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Db. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Mb.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Dl. pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as Ml.
  pose proof (Z.div_mod len 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound len 8 ltac:(lia)) as Mn.
  pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Dc.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Mc.
  pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Dd.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Md.
  replace s with (SHADOW_OFF + lo / 8 + (s - SHADOW_OFF - lo / 8)) by lia.
  rewrite Hz; [discriminate|]. lia.
Qed.

Lemma jk_rdword_kept : forall (rd1 rd2 : Z -> option Z) a, (forall k, 0 <= k < 8 -> rd2 (a + k) = rd1 (a + k)) ->
  rdword rd2 a = rdword rd1 a.
Proof.
  intros rd1 rd2 a H. unfold rdword.
  assert (H0 : rd2 a = rd1 a) by (rewrite <- (Z.add_0_r a); apply H; lia).
  rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma jk_mbyte_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a,
  d_kept P W m W' m' -> 0 <= a < 2 ^ 64 -> ~ P a -> mbyte SEGS (rd W' m') a = mbyte SEGS (rd W m) a.
Proof.
  intros P W m W' m' a HK Ha HP. pose proof (HK a Ha HP) as E. unfold aview in E.
  destruct (mbyte SEGS (rd W' m') a) as [b1|] eqn:E1; destruct (mbyte SEGS (rd W m) a) as [b2|] eqn:E2;
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma jk_val_mem_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a nb v,
  d_kept P W m W' m' -> 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat nb -> ~ P x) ->
  val_mem SEGS (rd W m) a nb v -> val_mem SEGS (rd W' m') a nb v.
Proof.
  intros P W m W' m' a nb v HK H0 H1 HP Hv k Hk.
  rewrite (jk_mbyte_kept P W m W' m'); [exact (Hv k Hk) | exact HK | lia |].
  apply HP. lia.
Qed.

Lemma jk_garr8_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a l,
  d_kept P W m W' m' -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (length l) -> ~ P x) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W' m') a l.
Proof.
  intros P W m W' m' a l HK H0 H1 HP Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  apply (jk_val_mem_kept P W m W' m'); [exact HK | lia | lia | | exact Hv].
  intros x Hx. apply HP. lia.
Qed.

Lemma jk_region_ok_kept : forall (E : env) (m m' : word -> option byte) (r : YP09.region) lo hi,
  region_ok SEGS E m r ->
  forallb (fun c => (lo <=? YP09.c_off c) && (YP09.c_off c + YP09.c_len c <=? hi)) (YP09.r_chunks r) = true ->
  (forall a, base_val E (YP09.r_base r) + lo <= a < base_val E (YP09.r_base r) + hi ->
     mbyte SEGS m' a = mbyte SEGS m a) ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> writable_at SEGS m' (base_val E (YP09.r_base r) + o)) ->
  region_ok SEGS E m' r.
Proof.
  intros E m m' r lo hi HR Hb Hk Hw. destruct HR as (H0 & H1 & _ & HC).
  split; [exact H0|]. split; [exact H1|]. split; [exact Hw|].
  rewrite Forall_forall in HC |- *. intros c Hc ii Hii. destruct (HC c Hc ii Hii) as (b & Hb1 & Hb2).
  exists b. split; [exact Hb1|].
  pose proof (proj1 (forallb_forall _ _) Hb c Hc) as Hcb. apply andb_prop in Hcb as [Hl Hh].
  apply Z.leb_le in Hl. apply Z.leb_le in Hh.
  rewrite Hk; [exact Hb2|]. lia.
Qed.

Lemma jk_garr8_sub : forall (m : word -> option byte) a (L : list Z) s n,
  garr8 SEGS m a L -> 0 <= s -> s + Z.of_nat n <= Z.of_nat (length L) ->
  garr8 SEGS m (a + s) (firstn n (skipn (Z.to_nat s) L)).
Proof.
  intros m a L s n G Hs Hn.
  rewrite <- (firstn_skipn (Z.to_nat s) L) in G. apply garr8_app in G. destruct G as [_ G].
  rewrite length_firstn in G. rewrite Nat.min_l in G by lia. rewrite Z2Nat.id in G by lia.
  rewrite <- (firstn_skipn n (skipn (Z.to_nat s) L)) in G. apply garr8_app in G. exact (proj1 G).
Qed.

Lemma jk_view_garr8 : forall (H : word -> bool) (m : word -> option byte) base n,
  (forall j, (j < n)%nat -> aview SEGS H m (base + Z.of_nat j) <> None) ->
  exists l, length l = n /\ garr8 SEGS (mrestrict H m) base l.
Proof.
  intros H m base n. revert base. induction n as [|n IH]; intros base Hv.
  - exists []. split; [reflexivity | apply garr8_nil].
  - assert (H0 : aview SEGS H m base <> None).
    { pose proof (Hv 0%nat ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
    unfold aview in H0. destruct (mbyte SEGS (mrestrict H m) base) as [b|] eqn:Eb; [|exfalso; apply H0; reflexivity].
    destruct (IH (base + 1)) as (l & Hlen & Hl).
    { intros j Hj. replace (base + 1 + Z.of_nat j) with (base + Z.of_nat (S j)) by lia. apply Hv. lia. }
    exists (bv_unsigned b :: l). split; [cbn [length]; lia|].
    pose proof (bv_unsigned_in_range _ b) as Hr. change (bv_modulus 8) with 256 in Hr.
    intros [|j] Hj.
    + cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [|lia].
      intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Eb. f_equal.
      unfold YO0f.le_byte. replace (8 * Z.of_nat 0) with 0 by reflexivity.
      replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
      rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Z.mod_small by lia.
      symmetry. apply Z_to_bv_bv_unsigned.
    + cbn [nth]. destruct (Hl j ltac:(cbn [length] in Hj; lia)) as [Hv' Hr']. split; [|exact Hr'].
      replace (base + Z.of_nat (S j)) with (base + 1 + Z.of_nat j) by lia. exact Hv'.
Qed.

Lemma jk_key : forall (W : world SEGS) m x (w : list Z),
  tjson_scalar_str W m x w ->
  exists slack : list byte,
  Forall (fun c => 0 < c < 256) w /\
  ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) w) /\
  garr8 SEGS (rd W m) x (map bv_unsigned (map (Z_to_bv 8) w ++ Z_to_bv 8 0 :: slack)) /\
  (- (x + Z.of_nat (length (map (Z_to_bv 8) w)) + 1)) mod 8 <= Z.of_nat (length slack) /\
  0 < x /\ x + Z.of_nat (length (map (Z_to_bv 8) w) + 1 + length slack) < 0x7fff8008 /\
  Z.of_nat (length (map (Z_to_bv 8) w)) + 1 < 2 ^ 32 /\
  amem_range x (Z.of_nat (length (map (Z_to_bv 8) w) + 1)) /\
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF x (Z.of_nat (length (map (Z_to_bv 8) w) + 1)) /\
  shadow_hull_vis (aview SEGS (w_H W) m) x (Z.of_nat (length (map (Z_to_bv 8) w) + 1)).
Proof.
  intros W m x w (HF & HG & Hx0 & Hx63 & Hx32 & Hamr & Hra & Hhull & Htail & Himg).
  pose proof (Z.mod_pos_bound (- (x + Z.of_nat (length w) + 1)) 8 ltac:(lia)) as Hr.
  destruct (jk_view_garr8 (w_H W) m (x + Z.of_nat (length w) + 1)
    (Z.to_nat ((- (x + Z.of_nat (length w) + 1)) mod 8))) as (l & Hl & Gl).
  { intros j Hj. apply Htail. lia. }
  pose proof (garr8_bytes_ok SEGS _ _ _ Gl) as Bl. unfold bytes_ok in Bl.
  assert (Hw' : Forall (fun c => 0 <= c < 256) w).
  { apply Forall_forall. intros c Hc. rewrite Forall_forall in HF. specialize (HF c Hc). lia. }
  pose proof (Himg (x + Z.of_nat (length w)) ltac:(lia)) as Hix. apply pa_segs_low in Hix.
  unfold kLowMemEnd in Hix.
  exists (map (Z_to_bv 8) l). rewrite !length_map.
  split; [exact HF|]. split.
  { intros Hin. apply in_map_iff in Hin. destruct Hin as (c & Hc & Hcw). rewrite Forall_forall in HF.
    specialize (HF c Hcw). apply (f_equal bv_unsigned) in Hc. rewrite !Z_to_bv_unsigned in Hc.
    unfold bv_wrap in Hc. change (bv_modulus 8) with 256 in Hc. rewrite !Z.mod_small in Hc by lia. lia. }
  split.
  { rewrite map_app. cbn [map]. rewrite (jk_bytes_map _ Hw'), (jk_bytes_map _ Bl).
    change (bv_unsigned (Z_to_bv 8 0)) with 0.
    replace (w ++ 0 :: l) with ((w ++ [0]) ++ l) by (rewrite <- app_assoc; reflexivity).
    apply garr8_app. split; [exact HG|]. rewrite length_app. cbn [length].
    replace (x + Z.of_nat (length w + 1)) with (x + Z.of_nat (length w) + 1) by lia. exact Gl. }
  split; [rewrite Hl; lia|]. split; [exact Hx0|]. split; [rewrite Hl; lia|]. split; [exact Hx32|].
  replace (Z.of_nat (length w + 1)) with (Z.of_nat (length w) + 1) by lia.
  split; [exact Hamr|]. split; [exact Hra | exact Hhull].
Qed.

Lemma jk_x_kept : forall (P : jc2p) (W : world SEGS) m (W' : world SEGS) m',
  jc2_x P W m -> 4096 <= d_FB (p_cx P) -> d_FB (p_cx P) + 4096 <= d_A (p_cx P) - TJTOK_IS_STK ->
  d_A (p_cx P) + 472 <= 2 ^ 47 ->
  d_kept (fun a => d_A (p_cx P) - TJTOK_IS_STK <= a < d_A (p_cx P)) W m W' m' -> jc2_x P W' m'.
Proof.
  intros P W m W' m' HX G1 G2 G3 HK. unfold TJTOK_IS_STK, ESTACK in G2, HK.
  pose proof (jc2_count P W m HX) as Hc.
  destruct HX as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & (J1 & J2 & J3 & J4 & J5 & J6) &
    V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9).
  assert (KV : forall off nb v, 0 <= off -> off + Z.of_nat nb <= 472 ->
    val_mem SEGS (rd W m) (d_A (p_cx P) + off) nb v -> val_mem SEGS (rd W' m') (d_A (p_cx P) + off) nb v).
  { intros off nb v H0 H1 Hv. apply (jk_val_mem_kept _ W m W' m' _ _ _ HK); [lia | lia | | exact Hv].
    intros y Hy Hp. cbv beta in Hp. lia. }
  assert (HLo : length (slot_ser_defs.objs_bytes (p_buf P) (p_vpad P) (p_acc P ++ [p_cur P])) =
    (144 * (Z.to_nat (p_count P) + 1))%nat).
  { rewrite (slot_ser_Pq.objs_len _ _ _ J3 J6). rewrite length_app. cbn [length]. rewrite Q4. lia. }
  split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
  split; [exact Q6|]. split; [exact Q7|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q10|].
  split; [exact Q11|]. split; [exact Q12|].
  split.
  { split; [apply KV; [lia | cbn; lia | exact J1]|]. split; [apply KV; [lia | cbn; lia | exact J2]|].
    split; [exact J3|].
    split.
    { apply (jk_garr8_kept _ W m W' m' _ _ HK); [lia | rewrite length_map, J3; cbn; lia | | exact J4].
      intros y Hy Hp. cbv beta in Hp. rewrite length_map, J3 in Hy. cbn in Hy. lia. }
    split; [|exact J6].
    apply (jk_garr8_kept _ W m W' m' _ _ HK); [unfold d_obj, dobj_off; lia | | | exact J5].
    - rewrite length_map, HLo. unfold d_obj, dobj_off. lia.
    - intros y Hy Hp. cbv beta in Hp. rewrite length_map, HLo in Hy. unfold d_obj, dobj_off in Hy. lia. }
  split; [apply KV; [lia | cbn; lia | exact V1]|]. split; [apply KV; [lia | cbn; lia | exact V2]|].
  split; [apply KV; [lia | cbn; lia | exact V3]|]. split; [apply KV; [lia | cbn; lia | exact V4]|].
  split; [apply KV; [lia | cbn; lia | exact V5]|]. split; [apply KV; [lia | cbn; lia | exact V6]|].
  split; [apply KV; [lia | cbn; lia | exact V7]|]. split; [apply KV; [lia | cbn; lia | exact V8]|].
  apply KV; [lia | cbn; lia | exact V9].
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DROH : d_ro_hyps B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis TJTOK : tjtok_is_spec B.
Hypothesis de_mc_ro : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis de_mc_un : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Lemma jk_cv : forall (W : world SEGS) m,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) -> consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W m.
Proof.
  intros W m HA a Ha. destruct (de_mc_un a Ha) as [H1 H2]. exact (HA a (de_mc_ro a Ha) H1 H2).
Qed.

Theorem jc2_jtk : jc2_jtk_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros P kb W c Hk6 Hc.
unfold jc2_call, jc2_at, jcut, d_arm_at_pf, d_at in Hc.
destruct Hc as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HCSR & HBASE & HJ & HFR & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R22 & R26 & HR2 & R1 & R10 & R11 & R12) & (HSP1 & HTAB & HBUF & HX & HKB) &
  HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HBODY as (T & G & Lk & HL & HFRM & HSHD & HOBJ & HBLK & HINP & HROD & _).
pose proof HBLK as (HPerm0 & _ & _ & HOFFb).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K (p_cx P) ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS (p_cx P) ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & _ & _ & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof (DCRO LAWS DROH ly3 S3 W mem3 md3 HAR3 HROD) as (_ & _ & _ & HSTRS & _).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range (p_cx P) ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo, GSTK.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
destruct Hastk as (_ & _ & Hstk1 & Hstk2 & Hstk3 & _).
unfold LLVMF_STK in Hstk2.
pose proof (al_zshadow _ _ LAWS ly3 S3 W mem3 md3 (ly_stk_lo ly3, ly_stk_hi ly3 - ly_stk_lo ly3) HAR3
  ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZS.
cbn [fst snd] in HZS. rewrite Elo, Ehi in HZS.
assert (Hinb : In (p_buf P, Z.max (slot_ser_defs.ser_cap (p_op P)) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & _).
pose proof (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (HbSh & HbHull).
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap (p_op P)) 1) = Z.max (slot_ser_defs.ser_cap (p_op P)) 1).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap (p_op P)) 1) 0); lia. }
rewrite Hreq in Hbceil, Hbapp, HbSh, HbHull.
pose proof HBUF as ((Hr2 & Hrc) & HgB).
set (N := Z.max (slot_ser_defs.ser_cap (p_op P)) 1) in *.
assert (HNr : a3_r (p_T1 P) (p_now P) + 1 <= N) by lia.
assert (HgT : garr8 SEGS (rd W mem3) (p_buf P) (a3_text (p_T1 P) (p_now P)))
  by (apply garr8_app in HgB; exact (proj1 HgB)).
pose proof (garr8_bytes_ok SEGS _ _ _ HgT) as HBok. unfold bytes_ok in HBok.
pose proof HX as (HF & _ & _ & _ & Hkk & _ & _ & _ & _ & _ & HKin & _ & _ & _ & _ & _ & V448 & V456 & V464 & _).
unfold slot_ser_tokb.tok_inb, p_kt, tv_kind in HKin. cbn [fst snd] in HKin.
destruct HKin as [HK0 | (Hks0 & Hkl0 & Hkb)]; [lia|].
change (jlen (p_B P)) with (a3_r (p_T1 P) (p_now P)) in Hkb.
assert (HlenB : Z.of_nat (length (p_B P)) = a3_r (p_T1 P) (p_now P)) by reflexivity.
assert (HKEY : tjson_scalar_str W mem3 (VAL (A_OBJ (4 + kb))) (nth kb keys [])).
{ destruct HSTRS as ((H4 & _) & (H5 & _) & (H6 & _) & (H7 & _) & (H8 & _) & (H9 & _) & _).
  destruct kb as [|[|[|[|[|[|kb]]]]]]; [exact H4 | exact H5 | exact H6 | exact H7 | exact H8 | exact H9 | lia]. }
set (w := nth kb keys []) in *.
destruct (jk_key W mem3 _ _ HKEY) as (slack & HKF & HKn0 & HKG & HKs & HKx0 & HKlo & HK32 & HKamr & HKra & HKhull).
pose proof (jk_cv W mem3 HROD) as HCV.
pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
assert (SpR : spZ regs = d_A (p_cx P)) by exact Rsp.
assert (HAFN : afn_pre SEGS B TJTOK_IS_STK ly3 S3 W (regupd regs 8 (Z_to_bv 64 0)) mem3 md3 []).
{ eapply (afn_pre_at SEGS B LLVMF_STK (d_S (p_cx P)) [] (c_ly (p_cx P)) (c_S (p_cx P)) (c_W (p_cx P))
    (c_mem (p_cx P)) (c_md (p_cx P)) [(DFRAME_CLASS, c_fpos (p_cx P))] ly3 S3 W mem3 md3 k
    (regupd regs 8 (Z_to_bv 64 0)) TJTOK_IS_STK (d_A (p_cx P) - d_S (p_cx P)) [] HJ).
  - unfold spZ. rewrite getr_other by jk_bvne. fold (spZ regs). rewrite SpR. lia.
  - lia.
  - lia.
  - unfold TJTOK_IS_STK, ESTACK. lia.
  - unfold TJTOK_IS_STK, ESTACK, LLVMF_STK. lia.
  - rewrite getr_other by jk_bvne. rewrite R1. unfold w64. apply ret_ok_codeptr_v; unfold C2_RET; lia.
  - unfold raZ. rewrite getr_other by jk_bvne. rewrite R1. unfold w64.
    rewrite unsigned_lit_small by (unfold C2_RET; lia). unfold C2_RET. lia.
  - rewrite getr_other by jk_bvne. exact Rgp.
  - rewrite getr_other by jk_bvne. exact Rtp.
  - left. split; [|reflexivity]. left. unfold s0Z. rewrite getr_same by jk_bvne.
    rewrite unsigned_lit_small by lia. lia. }
eapply SRr_mono.
{ apply (TJTOK fq ly3 S3 W regs mem3 md3 [] (d_A (p_cx P) + 448) (VAL (A_OBJ (4 + kb))) 1 1
    (p_buf P + p_ks P) (p_kl P) (map (Z_to_bv 8) w) slack
    (map (Z_to_bv 8) (firstn (length w) (skipn (Z.to_nat (p_ks P)) (p_B P)))) HAFN HROD HCV R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact V448.
  - replace (d_A (p_cx P) + 448 + 8) with (d_A (p_cx P) + 456) by lia. exact V456.
  - replace (d_A (p_cx P) + 448 + 16) with (d_A (p_cx P) + 464) by lia. rewrite Hkk in V464. exact V464.
  - lia.
  - lia.
  - pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold amem_range. right. rewrite C3, C4. lia.
  - apply (jk_zs_range _ _ _ _ _ _ HZS); lia.
  - apply (jk_zs_hull _ _ _ _ _ HZS); lia.
  - right. rewrite SpR. lia.
  - exact HKn0.
  - exact HKG.
  - exact HKs.
  - exact HKx0.
  - lia.
  - exact HK32.
  - exact HKamr.
  - exact HKra.
  - exact HKhull.
  - left. rewrite SpR. unfold TJTOK_IS_STK, ESTACK. lia.
  - intros _ Hvn. rewrite length_map in Hvn. rewrite !length_map.
    assert (HL1 : length (firstn (length w) (skipn (Z.to_nat (p_ks P)) (p_B P))) = length w).
    { rewrite length_firstn, length_skipn. lia. }
    assert (HSb : Forall (fun c => 0 <= c < 256) (firstn (length w) (skipn (Z.to_nat (p_ks P)) (p_B P))))
      by (apply jk_forall_fs; exact HBok).
    split; [exact HL1|].
    split.
    { rewrite (jk_bytes_map _ HSb). apply jk_garr8_sub; [exact HgT | lia | lia]. }
    split; [lia|]. split; [lia|].
    split; [apply (amem_range_sub_app (p_buf P) N (p_buf P + p_ks P) (Z.of_nat (length w)));
      [exact Hbapp | lia | lia | lia | lia]|].
    split; [apply (block_shadow_range _ _ (p_buf P) N (p_buf P + p_ks P) (Z.of_nat (length w)) HbSh); lia|].
    split.
    { intros Hpos s Hs. apply HbHull.
      pose proof (YCbq.shadow_mono (p_buf P) (p_buf P + p_ks P) ltac:(lia)) as Sm1.
      pose proof (YCbq.shadow_mono (p_buf P + p_ks P + Z.of_nat (length w) - 1) (p_buf P + N - 1) ltac:(lia)) as Sm2.
      pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Sm1) as Sd1.
      pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Sm2) as Sd2. lia. }
    left. rewrite SpR. unfold TJTOK_IS_STK, ESTACK. lia. }
cbv beta. intros W2 c2 HW2 Hpost.
unfold tjtok_is_post, apost_base in Hpost.
destruct Hpost as (fq2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfreg2 & Hcsr2 & HJc & HP & HAB & HKP & HRES).
pose proof (ajournal_sub SEGS B LAWS pa_segs_low LLVMF_STK (d_S (p_cx P)) [] (c_ly (p_cx P)) (c_S (p_cx P))
  (c_W (p_cx P)) (c_mem (p_cx P)) (c_md (p_cx P)) [(DFRAME_CLASS, c_fpos (p_cx P))] ly3 S3 W mem3 md3 k
  TJTOK_IS_STK (spZ regs) [] [] ly2 S2 W2 mem2 md2 0 HJ HJc
  ltac:(rewrite SpR; unfold LLVMF_STK, TJTOK_IS_STK, ESTACK; lia) ltac:(rewrite SpR; lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ4.
cbn [app] in HJ4. rewrite Z.add_0_r in HJ4.
pose proof HJc as (_ & _ & _ & _ & _ & HfrC & _).
assert (HFR4 : frames S2 = [(DFRAME_CLASS, c_fpos (p_cx P))]) by (rewrite HfrC; cbn [app]; exact HFR).
assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K (p_cx P) ly2 S2 W2 mem2 md2 k)
  by exact (conj HBASE (conj HJ4 HFR4)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS (p_cx P) ly2 S2 W2 mem2 md2 k HCTX4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
unfold LLVMF_STK in GSTK4.
set (Pw := fun a => d_A (p_cx P) - TJTOK_IS_STK <= a < d_A (p_cx P)).
assert (HK : d_kept Pw W mem3 W2 mem2).
{ intros a Ha HPa. apply HKP; [exact Ha|]. rewrite SpR. exact HPa. }
assert (HPlo : forall a, a < alloc_ceiling -> ~ Pw a).
{ intros a Ha Hp. unfold Pw in Hp. cbv beta in Hp. unfold TJTOK_IS_STK, ESTACK in Hp. lia. }
assert (HPA : forall a, d_A (p_cx P) <= a -> ~ Pw a).
{ intros a Ha Hp. unfold Pw in Hp. cbv beta in Hp. lia. }
assert (HFB8 : 0 <= d_FB (p_cx P) / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
pose proof HFRM as (E & HE & HREG & HFLAG & H216 & H152).
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
assert (HFRM4 : d_frame (p_cx P) (p_h P) dsh_scr W2 mem2).
{ exists E. split; [exact HE|]. split; [|split; [|split]].
  - unfold d_regions in HREG |- *. rewrite !Forall_cons_iff in HREG |- *.
    destruct HREG as (HRS & HRA & HRF & HRH & _).
    split; [|split; [|split; [|split; [|exact (Forall_nil _)]]]].
    + apply (jk_region_ok_kept E _ _ _ (-104) 0 HRS); [vm_compute; reflexivity | |].
      * cbn [YP09.r_base base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl).
        change (bv_unsigned (getr (c_regs (p_cx P)) 2)) with (d_S (p_cx P)).
        intros a Ha. apply (mbyte_of_aview SEGS). apply HK; [lia | apply HPA; lia].
      * cbn [YP09.r_wlo YP09.r_whi]. intros o Ho. lia.
    + apply (jk_region_ok_kept E _ _ _ 0 472 HRA); [vm_compute; reflexivity | |].
      * cbn [YP09.r_base base_val]. rewrite E60. unfold w64. rewrite unsigned_lit_small by lia.
        intros a Ha. apply (mbyte_of_aview SEGS). apply HK; [lia | apply HPA; lia].
      * cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi]. rewrite E60. unfold w64.
        rewrite unsigned_lit_small by lia. intros o Ho. apply (apresent_writable SEGS). apply GSTK4. lia.
    + apply (jk_region_ok_kept E _ _ _ 0 24 HRF); [vm_compute; reflexivity | |].
      * cbn [YP09.r_base base_val]. rewrite EF. unfold w64. rewrite unsigned_lit_small by lia.
        intros a Ha. apply (mbyte_of_aview SEGS). apply HK; [lia | apply HPlo; lia].
      * cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi]. rewrite EF. unfold w64.
        rewrite unsigned_lit_small by lia. intros o Ho. apply (apresent_writable SEGS). apply GFpres4.
        unfold DFRAME_SIZE in Ho. lia.
    + apply (jk_region_ok_kept E _ _ _ 0 384 HRH); [vm_compute; reflexivity | |].
      * unfold fshadow_region. cbn [YP09.r_base base_val]. rewrite ESH. unfold w64.
        rewrite unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
        intros a Ha. apply (mbyte_of_aview SEGS).
        apply HK; [unfold shadow_addr, SHADOW_OFF in *; lia | apply HPlo; unfold shadow_addr, SHADOW_OFF in *; lia].
      * unfold fshadow_region. cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi]. rewrite ESH. unfold w64.
        rewrite unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
        intros o Ho. apply (apresent_writable SEGS). apply GFsh4. unfold DFRAME_SH in Ho. lia.
  - rewrite <- HFLAG. apply jk_rdword_kept. intros kk0 Hkk0.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. apply HK; [lia | apply HPlo; lia].
  - apply (jk_val_mem_kept Pw W mem3 W2 mem2); [exact HK | lia | lia | intros x Hx; apply HPA; lia | exact H216].
  - apply (jk_val_mem_kept Pw W mem3 W2 mem2); [exact HK | lia | lia | intros x Hx; apply HPA; lia | exact H152]. }
assert (HSHD4 : d_shadow (p_cx P) dsh_scr W2 mem2).
{ intros kk0 Hkk0. rewrite <- (HSHD kk0 Hkk0). unfold DFRAME_SH in Hkk0.
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia | apply HPlo; unfold shadow_addr, SHADOW_OFF; lia]. }
pose proof (DiscoEntBody.d_body_call_keep B MT XM_LIB RLO RHI tfib_K LAWS (p_cx P) (p_h P) (p_n P)
  (a3_xb (p_buf P) (p_op P)) dsh_scr dsh_scr ly3 S3 W mem3
  ly2 S2 W2 mem2 md2 k (d_A (p_cx P) - TJTOK_IS_STK) (d_A (p_cx P)) HBODY (conj HBASE HJ4)
  ltac:(unfold TJTOK_IS_STK, ESTACK, LLVMF_STK; lia) ltac:(lia) HK HAB HFRM4 HSHD4) as HBODY4.
assert (P2 : getr regs2 2 = getr regs 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr regs 3) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr regs 4) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr regs 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr regs 9) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18 = getr regs 18) by exact (HP 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs2 19 = getr regs 19) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20 = getr regs 20) by exact (HP 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs2 21 = getr regs 21) by exact (HP 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs2 22 = getr regs 22) by exact (HP 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs2 23 = getr regs 23) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs2 24 = getr regs 24) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs2 25 = getr regs 25) by exact (HP 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs2 26 = getr regs 26) by exact (HP 26 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs2 27 = getr regs 27) by exact (HP 27 ltac:(unfold acallee_saved; lia)).
assert (HBR : jtok_match 1 1 (Z_to_bv 64 (p_kl P))
    (map (Z_to_bv 8) (firstn (length w) (skipn (Z.to_nat (p_ks P)) (p_B P)))) (map (Z_to_bv 8) w) <->
  jtok_is (p_B P) (p_kt P) 1 w = true).
{ unfold p_kt. rewrite Hkk. apply jk_bridge; [exact HBok | exact HKF | lia | lia | lia | exact Hkb]. }
assert (HRES' : exists res, getr regs2 10 = w64 res /\ jc2_res P kb res).
{ destruct HRES as [(HM & Q10) | (HM & Q10)].
  - exists 1. split; [exact Q10|]. left. split; [reflexivity|]. exact (proj1 HBR HM).
  - exists 0. split; [exact Q10|]. right. split; [reflexivity|].
    destruct (jtok_is (p_B P) (p_kt P) 1 (nth kb keys [])) eqn:EJ; [|reflexivity].
    exfalso. apply HM. exact (proj2 HBR EJ). }
destruct HRES' as (res & Q10 & HRS).
assert (KV : forall off nb v, 0 <= off -> off + Z.of_nat nb <= 472 ->
  val_mem SEGS (rd W mem3) (d_A (p_cx P) + off) nb v -> val_mem SEGS (rd W2 mem2) (d_A (p_cx P) + off) nb v).
{ intros off nb v Hoff Hnb Hv. apply (jk_val_mem_kept Pw W mem3 W2 mem2); [exact HK | lia | lia | | exact Hv].
  intros y Hy. apply HPA. lia. }
exists res.
unfold jc2_ret, jc2_at, jcut, d_arm_at_pf, d_at.
split.
{ destruct HFROM as (HA3 & HW0 & HT0 & HEX). split; [exact HA3|].
  split; [eapply wle_trans; [exact HW0 | exact HW2]|]. split; [exact HT0 | exact HEX]. }
exists fq2, ly2, S2, regs2, mem2, md2, k, acc.
split; [unfold cfg_at, w64; rewrite R1; reflexivity|].
split; [destruct Hcsr2 as [Hcs | Hcs]; [rewrite Hcs; exact HCSR | exact Hcs]|].
split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR4|]. split; [exact Hk|].
split; [pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite P2; exact Rsp|].
  split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|]. split; [rewrite P8; exact Rs0|].
  split; [rewrite P9; exact Rs1|]. split; [rewrite P18; exact Rs2|]. split; [rewrite P20; exact Rs4|].
  rewrite P25; exact Rs9. }
split.
{ destruct HR2 as (J19 & J21 & J23 & J24 & J27).
  split; [rewrite P22; exact R22|]. split; [rewrite P26; exact R26|].
  split; [|exact Q10].
  split; [rewrite P19; exact J19|]. split; [rewrite P21; exact J21|]. split; [rewrite P23; exact J23|].
  split; [rewrite P24; exact J24 | rewrite P27; exact J27]. }
split.
{ pose proof HSP1 as ((H232 & H344) & H224 & H248).
  split; [split; [split|split]|].
  - apply KV; [lia | cbn; lia | exact H232].
  - apply KV; [lia | cbn; lia | exact H344].
  - apply KV; [lia | cbn; lia | exact H224].
  - apply KV; [lia | cbn; lia | exact H248].
  - split.
    { pose proof HTAB as (HTex & HgOT). split; [exact HTex|].
      destruct HTex as (rem & _ & HAP). pose proof HAP as (HlenT1 & _).
      apply (jk_garr8_kept Pw W mem3 W2 mem2); [exact HK | unfold d_obj, dobj_off; lia | | | exact HgOT].
      - rewrite length_map, HlenT1. unfold d_obj, dobj_off. lia.
      - intros x Hx. rewrite length_map, HlenT1 in Hx. unfold d_obj, dobj_off in Hx. apply HPlo. lia. }
    split.
    { split; [lia|].
      apply (jk_garr8_kept Pw W mem3 W2 mem2); [exact HK | lia | | | exact HgB].
      - rewrite length_app. cbn [length]. unfold a3_r in *. lia.
      - intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. unfold a3_r in *. apply HPlo. lia. }
    split; [|split; [exact HKB | exact HRS]].
    apply (jk_x_kept P W mem3 W2 mem2 HX); [lia | unfold TJTOK_IS_STK, ESTACK; lia | lia | exact HK]. }
split.
{ pose proof HSP0 as (H232 & H344).
  split; [apply KV; [lia | cbn; lia | exact H232] | apply KV; [lia | cbn; lia | exact H344]]. }
exact HBODY4.
Qed.

End h.
End f.
End d.
