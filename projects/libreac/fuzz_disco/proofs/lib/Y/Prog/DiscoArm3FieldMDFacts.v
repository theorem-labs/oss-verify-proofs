From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC88 YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntryShapes DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3 DiscoArm3FieldCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_json_c disco_json_text disco_json_lemmas slot_ser_pure.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma mdf_u_at_range : forall (T : list byte) k n, 0 <= disco_table_c.u_at T k n < 2 ^ (8 * Z.of_nat n).
Proof.
  intros T k n. unfold disco_table_c.u_at.
  pose proof (YK11.bytes_le_to_Z_nonneg (disco_table_c.sub T k n)) as H0.
  pose proof (YK11.bytes_le_to_Z_bound (disco_table_c.sub T k n)) as H1.
  assert (L : (length (disco_table_c.sub T k n) <= n)%nat) by (unfold disco_table_c.sub; rewrite length_firstn; lia).
  split; [exact H0|]. eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma mdf_owned_iff : forall (T : list byte) p,
  disco_table_c.owned_of T p = 0 <-> disco_table_c.u_at T (48 * p + 24) 4 = 0.
Proof.
  intros T p. pose proof (mdf_u_at_range T (48 * p + 24) 4) as R.
  change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in R.
  unfold disco_table_c.owned_of, disco_table_c.s32_at.
  set (u := disco_table_c.u_at T (48 * p + 24) 4) in *.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  lia.
Qed.

Lemma mdf_owned_text : forall (T : list byte) p,
  disco_json_text.owned_text (reac_disco_table_json_c.tj_entry T p) =
  if disco_table_c.u_at T (48 * p + 24) 4 =? 0 then disco_json_text.s_false else disco_json_text.s_true.
Proof.
  intros T p. unfold disco_json_text.owned_text.
  change (disco_json_text.e_owned (reac_disco_table_json_c.tj_entry T p)) with (disco_table_c.owned_of T p).
  pose proof (mdf_owned_iff T p) as I.
  destruct (Z.eqb_spec (disco_table_c.owned_of T p) 0) as [E|E],
    (Z.eqb_spec (disco_table_c.u_at T (48 * p + 24) 4) 0) as [F|F]; try reflexivity; exfalso; tauto.
Qed.

Lemma mdf_owned_true : forall (T : list byte) p, disco_table_c.u_at T (48 * p + 24) 4 <> 0 ->
  disco_json_text.owned_text (reac_disco_table_json_c.tj_entry T p) = disco_json_text.s_true.
Proof.
  intros T p H. rewrite mdf_owned_text.
  destruct (Z.eqb_spec (disco_table_c.u_at T (48 * p + 24) 4) 0) as [E|E]; [contradiction | reflexivity].
Qed.

Lemma mdf_owned_false : forall (T : list byte) p, disco_table_c.u_at T (48 * p + 24) 4 = 0 ->
  disco_json_text.owned_text (reac_disco_table_json_c.tj_entry T p) = disco_json_text.s_false.
Proof. intros T p H. rewrite mdf_owned_text, H. reflexivity. Qed.

Lemma mdf_s_true : disco_json_text.s_true = [116; 114; 117; 101].
Proof. reflexivity. Qed.

Lemma mdf_s_false : disco_json_text.s_false = [102; 97; 108; 115; 101].
Proof. reflexivity. Qed.

Lemma mdf_s_true_ok : Forall (fun c => 0 < c < 256) disco_json_text.s_true.
Proof. unfold disco_json_text.s_true. repeat apply Forall_cons; try apply Forall_nil; lia. Qed.

Lemma mdf_s_false_ok : Forall (fun c => 0 < c < 256) disco_json_text.s_false.
Proof. unfold disco_json_text.s_false. repeat apply Forall_cons; try apply Forall_nil; lia. Qed.

Lemma mdf_owned_text_ok : forall e : disco_json_text.entry,
  Forall (fun c => 0 < c < 256) (disco_json_text.owned_text e) /\ (length (disco_json_text.owned_text e) <= 5)%nat.
Proof.
  intros e. unfold disco_json_text.owned_text. destruct (disco_json_text.e_owned e =? 0).
  - split; [exact mdf_s_false_ok | cbn; lia].
  - split; [exact mdf_s_true_ok | cbn; lia].
Qed.

Lemma mdf_model_txt : forall (T : list byte) p,
  Forall (fun c => 0 < c < 256) (fst (a3f_model T p)) /\ (length (fst (a3f_model T p)) <= 11)%nat /\
  Forall (fun c => 0 < c < 256) (snd (a3f_model T p)) /\ (length (snd (a3f_model T p)) <= 7)%nat.
Proof.
  intros T p. unfold a3f_model, disco_json_text.model_of.
  destruct (disco_json_text.e_has_decl (a3f_ent T p) =? 0).
  { cbn [fst snd]. unfold disco_json_text.s_unknown, disco_json_text.s_0x0. cbn [length].
    split; [repeat apply Forall_cons; try apply Forall_nil; lia|].
    split; [lia|]. split; [repeat apply Forall_cons; try apply Forall_nil; lia | lia]. }
  destruct (reac_disco_table_json_c.box_tok (disco_json_text.e_family (a3f_ent T p))
              (disco_json_text.e_decl_in (a3f_ent T p)) (disco_json_text.e_decl_out (a3f_ent T p))) as [t|] eqn:Ht.
  2: { cbn [fst snd]. unfold disco_json_text.s_unknown, disco_json_text.s_0x0. cbn [length].
       split; [repeat apply Forall_cons; try apply Forall_nil; lia|].
       split; [lia|]. split; [repeat apply Forall_cons; try apply Forall_nil; lia | lia]. }
  cbn [fst snd]. destruct (slot_ser_pure.ser_tok_ok _ _ _ _ Ht) as (Lt & Ft).
  change (disco_json_text.e_decl_in (a3f_ent T p)) with (disco_table_c.u_at T (48 * p + 13) 1).
  change (disco_json_text.e_decl_out (a3f_ent T p)) with (disco_table_c.u_at T (48 * p + 14) 1).
  pose proof (mdf_u_at_range T (48 * p + 13) 1) as Ri. pose proof (mdf_u_at_range T (48 * p + 14) 1) as Ro.
  change (2 ^ (8 * Z.of_nat 1)) with 256 in Ri, Ro.
  destruct (disco_json_lemmas.dec_spec (disco_table_c.u_at T (48 * p + 13) 1) ltac:(lia)) as (Di & _ & _ & Li).
  destruct (disco_json_lemmas.dec_spec (disco_table_c.u_at T (48 * p + 14) 1) ltac:(lia)) as (Do & _ & _ & Lo).
  specialize (Li 3 ltac:(lia) ltac:(lia)). specialize (Lo 3 ltac:(lia) ltac:(lia)).
  change (Z.to_nat 3) with 3%nat in Li, Lo.
  split; [eapply Forall_impl; [|exact Ft]; intros c Hc; unfold disco_json_text.tok_char in Hc; lia|].
  split; [exact Lt|].
  split.
  - apply Forall_app. split; [eapply Forall_impl; [|exact Di]; intros c Hc; unfold disco_json_lemmas.digc in Hc; lia|].
    apply Forall_app. split; [repeat apply Forall_cons; try apply Forall_nil; lia|].
    eapply Forall_impl; [|exact Do]. intros c Hc. unfold disco_json_lemmas.digc in Hc. lia.
  - rewrite !length_app. cbn [length]. lia.
Qed.

Lemma mdf_map_bytes : forall s : list Z, Forall (fun c => 0 <= c < 256) s -> map bv_unsigned (map (Z_to_bv 8) s) = s.
Proof.
  induction s as [|c s IH]; intros F; [reflexivity|].
  inversion F as [|c' s' Hc Fs]; subst. cbv beta in Hc. cbn [map]. rewrite (IH Fs). f_equal.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma mdf_nonzero : forall s : list Z, Forall (fun c => 0 < c < 256) s -> ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) s).
Proof.
  intros s F Hin. apply in_map_iff in Hin as (c & Ec & Hc).
  rewrite Forall_forall in F. specialize (F c Hc). cbv beta in F.
  apply (f_equal bv_unsigned) in Ec. rewrite !Z_to_bv_unsigned in Ec. unfold bv_wrap in Ec.
  change (bv_modulus 8) with 256 in Ec. lia.
Qed.

Lemma mdf_hull_sub : forall (rd : Z -> option Z) a n a' n', shadow_hull_vis rd a n -> a <= a' -> a' + n' <= a + n ->
  0 < n' -> shadow_hull_vis rd a' n'.
Proof.
  intros rd a n a' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
  assert (D1 : a / 8 <= a' / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : (a' + n' - 1) / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (D3 : (SHADOW_OFF + a / 8) / 8 <= (SHADOW_OFF + a' / 8) / 8) by (apply Z.div_le_mono; lia).
  assert (D4 : (SHADOW_OFF + (a' + n' - 1) / 8) / 8 <= (SHADOW_OFF + (a + n - 1) / 8) / 8)
    by (apply Z.div_le_mono; lia).
  lia.
Qed.

Definition mdf_fr_ok (shf : Z -> Z) (o L : Z) : bool :=
  forallb (fun j => let y := o + Z.of_nat j in
    (shf (y / 8) =? 0) || ((y mod 8 <? shf (y / 8)) && (shf (y / 8) <? 8))) (seq 0 (Z.to_nat L)).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma mdf_garr8_nat : forall (W : world SEGS) (m : word -> option byte) (n : nat) a,
  (forall i, 0 <= i < Z.of_nat n -> exists b, aview SEGS (w_H W) m (a + i) = Some b) ->
  exists L : list byte, length L = n /\ garr8 SEGS (rd W m) a (map bv_unsigned L).
Proof.
  intros W m n. induction n as [|n IH]; intros a HP.
  - exists []. split; [reflexivity|]. cbn [map]. apply garr8_nil.
  - destruct (HP 0 ltac:(lia)) as (v & Hv). rewrite Z.add_0_r in Hv.
    destruct (IH (a + 1)) as (L & HL & HG).
    { intros i Hi. rewrite <- Z.add_assoc. apply HP. lia. }
    unfold aview in Hv.
    destruct (mbyte SEGS (rd W m) a) as [b|] eqn:Eb; cbn [option_map] in Hv; [|discriminate Hv].
    assert (Hb : aview SEGS (w_H W) m a = Some (bv_unsigned b)) by (unfold aview; rewrite Eb; reflexivity).
    destruct (val_mem1_of_aview SEGS (w_H W) m a (bv_unsigned b) Hb) as [Hm Hr].
    exists (b :: L). split; [cbn [length]; lia|]. cbn [map].
    exact (garr8_cons_x SEGS (rd W m) a (bv_unsigned b) (map bv_unsigned L) Hm Hr HG).
Qed.

Lemma mdf_garr8_of_present : forall (W : world SEGS) (m : word -> option byte) a (len : Z), 0 <= len ->
  (forall i, 0 <= i < len -> exists b, aview SEGS (w_H W) m (a + i) = Some b) ->
  exists L : list byte, Z.of_nat (length L) = len /\ garr8 SEGS (rd W m) a (map bv_unsigned L).
Proof.
  intros W m a len Hl HP.
  destruct (mdf_garr8_nat W m (Z.to_nat len) a) as (L & HL & HG).
  { intros i Hi. apply HP. lia. }
  exists L. split; [lia | exact HG].
Qed.

Lemma mdf_garr8_slack : forall (W : world SEGS) (m : word -> option byte) a (L : list Z) (len : Z),
  garr8 SEGS (rd W m) a L -> 0 <= len ->
  (forall i, 0 <= i < len -> exists b, aview SEGS (w_H W) m (a + Z.of_nat (length L) + i) = Some b) ->
  exists sl : list byte, Z.of_nat (length sl) = len /\ garr8 SEGS (rd W m) a (L ++ map bv_unsigned sl).
Proof.
  intros W m a L len HG Hl HP.
  destruct (mdf_garr8_of_present W m (a + Z.of_nat (length L)) len Hl HP) as (sl & Hsl & HS).
  exists sl. split; [exact Hsl|].
  apply (proj2 (garr8_app SEGS (rd W m) a L (map bv_unsigned sl))). split; [exact HG | exact HS].
Qed.

Definition mdf_xarg (W : world SEGS) (m : word -> option byte) (x : Z) (T slack : list byte) : Prop :=
  ~ In (Z_to_bv 8 0) T /\
  garr8 SEGS (rd W m) x (map bv_unsigned (T ++ Z_to_bv 8 0 :: slack)) /\
  (- (x + Z.of_nat (length T) + 1)) mod 8 <= Z.of_nat (length slack) /\
  0 < x /\ x + Z.of_nat (length T + 1 + length slack) <= 2 ^ 63 /\
  Z.of_nat (length T) + 1 < 2 ^ 32 /\
  amem_range x (Z.of_nat (length T + 1)) /\
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF x (Z.of_nat (length T + 1)) /\
  shadow_hull_vis (aview SEGS (w_H W) m) x (Z.of_nat (length T + 1)) /\
  x + Z.of_nat (length T + 1 + length slack) <= x + Z.of_nat (length T) + 8.

Lemma mdf_xarg_of : forall (W : world SEGS) (m : word -> option byte) x (s : list Z),
  Forall (fun c => 0 < c < 256) s -> garr8 SEGS (rd W m) x (s ++ [0]) ->
  0 < x -> x + Z.of_nat (length s) + 1 <= 2 ^ 63 -> Z.of_nat (length s) + 1 < 2 ^ 32 ->
  amem_range x (Z.of_nat (length s) + 1) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF x (Z.of_nat (length s) + 1) ->
  shadow_hull_vis (aview SEGS (w_H W) m) x (Z.of_nat (length s) + 1) ->
  (forall y, x + Z.of_nat (length s) < y < x + Z.of_nat (length s) - (x + Z.of_nat (length s)) mod 8 + 8 ->
     aview SEGS (w_H W) m y <> None) ->
  exists slack, mdf_xarg W m x (map (Z_to_bv 8) s) slack.
Proof.
  intros W m x s F G Hx0 Hx63 H32 AM RA SH TL.
  assert (F' : Forall (fun c => 0 <= c < 256) s) by (eapply Forall_impl; [|exact F]; intros c Hc; cbv beta in *; lia).
  assert (HP : forall i, 0 <= i < (- (x + Z.of_nat (length s) + 1)) mod 8 ->
    exists b, aview SEGS (w_H W) m (x + Z.of_nat (length (s ++ [0])) + i) = Some b).
  { intros i Hi. rewrite length_app. cbn [length].
    destruct (aview SEGS (w_H W) m (x + Z.of_nat (length s + 1) + i)) as [b|] eqn:E; [exists b; reflexivity|].
    exfalso. apply (TL (x + Z.of_nat (length s + 1) + i)); [lia | exact E]. }
  destruct (mdf_garr8_slack W m x (s ++ [0]) ((- (x + Z.of_nat (length s) + 1)) mod 8) G ltac:(lia) HP)
    as (sl & Hsl & GS).
  exists sl. unfold mdf_xarg. rewrite length_map.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
  - exact (mdf_nonzero s F).
  - replace (map bv_unsigned (map (Z_to_bv 8) s ++ Z_to_bv 8 0 :: sl)) with ((s ++ [0]) ++ map bv_unsigned sl);
      [exact GS|].
    rewrite map_app, (mdf_map_bytes s F'). cbn [map]. rewrite <- app_assoc. reflexivity.
  - lia.
  - exact Hx0.
  - lia.
  - exact H32.
  - replace (Z.of_nat (length s + 1)) with (Z.of_nat (length s) + 1) by lia. exact AM.
  - replace (Z.of_nat (length s + 1)) with (Z.of_nat (length s) + 1) by lia. exact RA.
  - replace (Z.of_nat (length s + 1)) with (Z.of_nat (length s) + 1) by lia. exact SH.
  - lia.
Qed.

Lemma mdf_rostr_x : forall (W : world SEGS) (m : word -> option byte) a (s : list Z),
  d_rostr W m a s -> exists slack, mdf_xarg W m a (map (Z_to_bv 8) s) slack.
Proof.
  intros W m a s ((F & G & H0 & H63 & H32 & AM & RA & SH & TL & _) & _).
  exact (mdf_xarg_of W m a s F G H0 H63 H32 AM RA SH TL).
Qed.

Lemma mdf_rostr_sub : forall (W : world SEGS) (m : word -> option byte) a (s : list Z) a' n,
  d_rostr W m a s -> a <= a' -> a' + n <= a + Z.of_nat (length s) + 1 -> 0 < n ->
  amem_range a' n /\ range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a' n /\
  shadow_hull_vis (aview SEGS (w_H W) m) a' n.
Proof.
  intros W m a s a' n ((_ & _ & _ & _ & _ & AM & RA & SH & _) & _) H1 H2 H3.
  split; [|split].
  - unfold amem_range in *. lia.
  - exact (range_addressable_sub _ _ a (Z.of_nat (length s) + 1) a' n RA H1 ltac:(lia)).
  - exact (mdf_hull_sub _ a (Z.of_nat (length s) + 1) a' n SH H1 ltac:(lia) H3).
Qed.

Lemma mdf_owned_str : forall (W : world SEGS) (m : word -> option byte) (T : list byte) p, dimg_strs W m ->
  (disco_table_c.u_at T (48 * p + 24) 4 <> 0 ->
     d_rostr W m (VAL (A_OBJ 15)) (disco_json_text.owned_text (reac_disco_table_json_c.tj_entry T p))) /\
  (disco_table_c.u_at T (48 * p + 24) 4 = 0 ->
     d_rostr W m (VAL (A_OBJ 16)) (disco_json_text.owned_text (reac_disco_table_json_c.tj_entry T p))).
Proof.
  intros W m T p HS. destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S15 & S16 & _).
  split; intros Hu; [rewrite (mdf_owned_true T p Hu); exact S15 | rewrite (mdf_owned_false T p Hu); exact S16].
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma mdf_frame_triple : forall (cx : dcx) ly S (W : world SEGS) m md shf o L a len,
  AR SEGS B ly S W m md -> In (DFRAME_CLASS, c_fpos cx) (frames S) ->
  frame_addr ly DFRAME_CLASS (c_fpos cx) = d_FB cx -> in_app (d_FB cx) 4096 -> d_FB cx mod 32 = 0 ->
  d_shadow cx shf W m -> mdf_fr_ok shf o L = true -> 0 <= o -> o + L <= DFRAME_SIZE ->
  d_FB cx + o <= a -> a + len <= d_FB cx + o + L -> 0 < len ->
  amem_range a len /\ range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a len /\
  shadow_hull_vis (aview SEGS (w_H W) m) a len.
Proof.
  intros cx ly S W m md shf o L a len HAR Hin EFA Happ H32 HSH HOK Ho HoL Ha Hal Hlen.
  pose proof ASAN_CEIL_range as HC. unfold DFRAME_SIZE in HoL.
  split; [|split].
  - unfold amem_range, in_app in *.
    unfold YG0f.kLowMemEnd, YG0f.kHighMemBeg, YG0f.kHighMemEnd, YG0f.kLowShadowBeg in *. lia.
  - intros x Hx.
    assert (Hk : 0 <= (x - d_FB cx) / 8 < DFRAME_SH) by (unfold DFRAME_SH; lia).
    exists (shf ((x - d_FB cx) / 8)). split.
    + unfold shadow_of_addr.
      replace (SHADOW_OFF + x / 8) with (shadow_addr (d_FB cx) + (x - d_FB cx) / 8) by (unfold shadow_addr; lia).
      exact (HSH _ Hk).
    + unfold mdf_fr_ok in HOK. rewrite forallb_forall in HOK.
      specialize (HOK (Z.to_nat (x - d_FB cx - o)) ltac:(apply in_seq; lia)).
      cbv beta zeta in HOK.
      replace (o + Z.of_nat (Z.to_nat (x - d_FB cx - o))) with (x - d_FB cx) in HOK by lia.
      assert (Hxm : x mod 8 = (x - d_FB cx) mod 8) by lia.
      unfold saddr_ok. apply orb_prop in HOK as [E|E]; [left; apply Z.eqb_eq in E; exact E|right].
      apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. lia.
  - apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W m md DFRAME_CLASS (c_fpos cx) a len HAR Hin).
    + rewrite EFA. lia.
    + rewrite EFA. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
    + exact Hlen.
Qed.

Lemma mdf_frame_range : forall (cx : dcx) ly3 S3 (W3 : world SEGS) mem3 md3 k h n xb shf o L a len,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_body B cx h n xb shf ly3 S3 W3 mem3 ->
  mdf_fr_ok shf o L = true -> 0 <= o -> o + L <= DFRAME_SIZE ->
  d_FB cx + o <= a -> a + len <= d_FB cx + o + L -> 0 < len ->
  amem_range a len /\ range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF a len /\
  shadow_hull_vis (aview SEGS (w_H W3) mem3) a len.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k h n xb shf o L a len HC HB HOK Ho HoL Ha Hal Hlen.
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 mem3 md3 k HC)
    as (_ & _ & _ & _ & _ & Happ & _ & H32 & _ & _ & _ & HAR & Hin & EFA & _).
  destruct HB as (T & G & Lk & H & _ & HSH & _).
  exact (mdf_frame_triple cx ly3 S3 W3 mem3 md3 shf o L a len HAR Hin EFA Happ H32 HSH HOK Ho HoL Ha Hal Hlen).
Qed.

Lemma mdf_frame_x : forall (cx : dcx) ly3 S3 (W3 : world SEGS) mem3 md3 k h n xb shf o L x (s : list Z),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_body B cx h n xb shf ly3 S3 W3 mem3 ->
  mdf_fr_ok shf o L = true -> 0 <= o -> o + L <= DFRAME_SIZE ->
  d_FB cx + o <= x -> x + Z.of_nat (length s) + 1 <= d_FB cx + o + L ->
  Forall (fun c => 0 < c < 256) s -> garr8 SEGS (rd W3 mem3) x (s ++ [0]) ->
  exists slack, mdf_xarg W3 mem3 x (map (Z_to_bv 8) s) slack.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k h n xb shf o L x s HC HB HOK Ho HoL Hx Hxs F G.
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 mem3 md3 k HC)
    as (_ & _ & _ & HF0 & _ & Happ & _ & _ & HFpres & _ & _ & _ & _ & _ & _).
  destruct (mdf_frame_range cx ly3 S3 W3 mem3 md3 k h n xb shf o L x (Z.of_nat (length s) + 1) HC HB HOK Ho HoL Hx
    ltac:(lia) ltac:(lia)) as (AM & RA & SH).
  pose proof ASAN_CEIL_range as HCe. unfold DFRAME_SIZE in HoL.
  unfold in_app, YG0f.kLowShadowBeg, YG0f.kHighMemBeg in Happ.
  apply (mdf_xarg_of W3 mem3 x s F G); [lia | lia | lia | exact AM | exact RA | exact SH |].
  intros y Hy. apply (aview_some_of_apresent SEGS). apply HFpres. lia.
Qed.

Lemma mdf_tok_v : forall (cx : dcx) ly3 S3 (W3 : world SEGS) mem3 md3 k h n xb p j,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_body B cx h n xb dsh_md ly3 S3 W3 mem3 -> 0 <= p < 8 -> 0 <= j < 6 ->
  amem_range (d_obj cx OO + 144 * p + 24 * j) 20 /\
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (d_obj cx OO + 144 * p + 24 * j) 20 /\
  shadow_hull_vis (aview SEGS (w_H W3) mem3) (d_obj cx OO + 144 * p + 24 * j) 20.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k h n xb p j HC HB Hp Hj.
  exact (mdf_frame_range cx ly3 S3 W3 mem3 md3 k h n xb dsh_md 240 1296 (d_obj cx OO + 144 * p + 24 * j) 20 HC HB
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DFRAME_SIZE; lia)
    ltac:(unfold d_obj; cbn [dobj_off]; lia) ltac:(unfold d_obj; cbn [dobj_off]; lia) ltac:(lia)).
Qed.

Lemma mdf_wid_x : forall (cx : dcx) ly3 S3 (W3 : world SEGS) mem3 md3 k h n xb (T : list byte) p,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_body B cx h n xb dsh_md ly3 S3 W3 mem3 ->
  garr8 SEGS (rd W3 mem3) (d_obj cx OWID) (snd (a3f_model T p) ++ [0]) ->
  exists slack, mdf_xarg W3 mem3 (d_obj cx OWID) (map (Z_to_bv 8) (snd (a3f_model T p))) slack.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k h n xb T p HC HB G.
  destruct (mdf_model_txt T p) as (_ & _ & F & Lw).
  exact (mdf_frame_x cx ly3 S3 W3 mem3 md3 k h n xb dsh_md 2000 24 (d_obj cx OWID) (snd (a3f_model T p)) HC HB
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DFRAME_SIZE; lia)
    ltac:(unfold d_obj; cbn [dobj_off]; lia) ltac:(unfold d_obj; cbn [dobj_off]; lia) F G).
Qed.

Lemma mdf_mstr_x : forall (cx : dcx) ly3 S3 (W3 : world SEGS) mem3 md3 k h n xb mp (T : list byte) p,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_body B cx h n xb dsh_md ly3 S3 W3 mem3 -> dimg_strs W3 mem3 ->
  a3f_mstr cx W3 mem3 mp (fst (a3f_model T p)) ->
  exists slack, mdf_xarg W3 mem3 mp (map (Z_to_bv 8) (fst (a3f_model T p))) slack.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k h n xb mp T p HC HB HS [(-> & Es) | (-> & G)].
  - rewrite Es. destruct HS as (_ & _ & _ & _ & _ & _ & _ & S11 & _). exact (mdf_rostr_x W3 mem3 _ _ S11).
  - destruct (mdf_model_txt T p) as (F & Lf & _).
    exact (mdf_frame_x cx ly3 S3 W3 mem3 md3 k h n xb dsh_md 1856 24 (d_obj cx OTOK) (fst (a3f_model T p)) HC HB
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DFRAME_SIZE; lia)
      ltac:(unfold d_obj; cbn [dobj_off]; lia) ltac:(unfold d_obj; cbn [dobj_off]; lia) F G).
Qed.

End h.
End f.
End d.
