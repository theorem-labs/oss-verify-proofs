(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 133 of its 180 lines of code are new or changed and 467 lines of the source are left out. *)
(* fuzz_preset image B' (#102 pins, asan-ubsan d663f82d7f488d30): the HOME lemmas the walk of padded consumes.
   rule 24: no function proved. rule 24: proves no function (kind: state-level home lemmas).
   Pure state-level facts: no machine code is walked here. Consumer: lib/B/Prog/Padded102B.v (lane PaddedB102).
   PORT, lemma for lemma, of PvB_A_Home.v at origin/cold/h-rw-pre-7-b-parse_value 2773b89e7e5 (lane PValueB,
   parse_value B segment A): pvh_* / pva_* renamed pdh_*, statements and proofs otherwise unchanged. Its Requires of
   lib/B/Prog PvB_Defs / PvB_Model, lib/A PRH_FnParse / PRH_Charge, lib/Spec PjGrammar / PjTree / PjRoundTrip,
   YCbqGcallW, YGcfRoomKeep and lib/B/PAImg_prog are dropped: nothing below names them. The file stays parametric over
   {PA : PAImg B_prog_listing}; the image instance (PAImg_prog.v PI_prog_B) is NOT Required here.
   The text a reader reads lives at prhReader_home (PRH_FnReader.v:137-138): a live harness block (Lam), a registered
   read-only global (kept_at's in_zs arm), an image string under route (a) (kept_img), or a live allocator block whose
   base is not a hidden head. At any ARx state such a range is addressable and its shadow hull is visible
   (pdh_home_shadow); each of its bytes is a block byte or a read-only image byte the journal's image clause keeps
   (pdh_home_place); and a src_rd window whose bytes the view keeps is a src_rd window of the new state
   (pdh_src_rd_at).
   Templates of PvB_A_Home.v (FuzzStrdupB.v, over ARcf; line numbers of its blob db0e92d86ab7 at that commit):
   sd_hull_sub (:116), sd_hull_img (:126), sd_ro_img (:143), sd_garr8_move (:166), sd_src_shadow (:453). This
   tree's FuzzStrdupB.v (5499e1c6b3f0) has the first four at the same lines, sd_src_shadow at :454 and its
   aso_zshadow read at :471.
   Numerals: 8 (the shadow granule), 64 (kept_at's image margin, GrantRo.v:100), 1 / 256 (byte width), 4 (errno's
   width, as kept_at states it). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Instance PIB : PrhImg := prh_img_B.

(* ---- image-free arithmetic ---- *)
Lemma pdh_req_ge : forall m, m <= req_size m.
Proof. intros m. unfold req_size. destruct (Z.eqb_spec m 0); lia. Qed.
Lemma pdh_req_pos : forall m, 0 <= m -> 1 <= req_size m.
Proof. intros m Hm. unfold req_size. destruct (Z.eqb_spec m 0); lia. Qed.
Lemma pdh_req_eq : forall m, 0 < m -> req_size m = m.
Proof. intros m Hm. unfold req_size. destruct (Z.eqb_spec m 0); lia. Qed.
Lemma pdh_shadow_mono : forall x y, x <= y -> shadow_addr x <= shadow_addr y.
Proof. intros x y H. unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.
(* FuzzStrdupB.v:116 sd_hull_sub (cgif YCbq.v:1945 shadow_hull_vis_of_block): a hull covers its sub-ranges' hulls *)
Lemma pdh_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (pdh_shadow_mono p d Hpd) as M1. pose proof (pdh_shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
(* FuzzStrdupB.v:126 sd_hull_img (GrantRo.v:82-100 ro_hull's arithmetic): the hull of a range at least 64 bytes inside
   [IMG_LO, IMG_TOP) is the shadow of image bytes *)
Lemma pdh_hull_img : forall (lo hi : Z) a n s, 0 < n -> lo + 64 <= a -> a + n + 64 <= hi -> 0 <= lo -> hi <= 2 ^ 47 ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ lo <= 8 * (s - SHADOW_OFF) < hi.
Proof.
intros lo hi a n s Hn Hlo Hhi Hl0 Hh0 Hs. unfold shadow_addr in *.
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.
(* the one byte of a width-1 cell is its value *)
Lemma pdh_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity.
replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite (Z.mod_small v 256) by lia. apply Z.mod_small; lia.
Qed.

Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the kit rule: the allocator's laws over ARx (YCbqG.v AR_laws_x), as the source's consumers PvB_A.v / PvB_X.v take
   it *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* MARKED image fact, discharged at PI_prog_B: the image's shadow is mapped in every allocator state (h-mani-a8's
   img_shadow_vis_cf, lib/Reusable/YGcfAmx2.v, over ARx; image A's proof is AImgShadowVisCf.tfib_img_shadow_vis_cf).
   Used only for the hull of the two image arms of kept_at. *)
(* MARKED image fact: the image band, 0 <= pa_lo and pa_hi <= 2 ^ 47 (the kit moved kept_at's image arm to the
   INSTANCE bounds pa_lo / pa_hi, lib/A/PRH_Base.v 3004a98fe2d9), discharged at PI_prog_B by computation *)
Hypothesis pdh_img_band : 0 <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA <= 2 ^ 47.
Hypothesis pdh_img_vis : forall ly S Hp W mem md a, ARx ly S Hp W mem md ->
  @pa_lo _ B_prog_listing PA <= a < @pa_hi _ B_prog_listing PA ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* MARKED image fact, discharged at PI_prog_B: the image's zero-shadow ranges are whole granules (YG0f.v asyms_ok's
   aso_zshadow, a conjunct of ARcf's am_syms; FuzzStrdupB.v:470 reads it there) *)
Hypothesis pdh_zs_al : forall r, In r (as_zero_shadow B) -> fst r mod 8 = 0 /\ snd r mod 8 = 0.

(* FuzzStrdupB.v:143 sd_ro_img: a read-only byte is an image byte *)
Lemma pdh_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* FuzzStrdupB.v:166 sd_garr8_move: bytes the view keeps keep their garr8 reading *)
Lemma pdh_garr8_move : forall (W W' : world SEGS) m m' x d l, garr8 SEGS (mrestrict (w_H W) m) x l ->
  (forall j, (j < length l)%nat -> aview SEGS (w_H W') m' (d + Z.of_nat j) = aview SEGS (w_H W) m (x + Z.of_nat j)) ->
  garr8 SEGS (mrestrict (w_H W') m') d l.
Proof.
intros W W' m m' x d l H HA j Hj. destruct (H j Hj) as [V R]. split; [|exact R].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (V 0%nat Hkk). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
specialize (HA j Hj). unfold aview in HA. rewrite V in HA. cbn [option_map] in HA.
destruct (mbyte SEGS (mrestrict (w_H W') m') (d + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in HA; [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.

(* the hull of a range 64 bytes inside the image (the MARKED image fact pdh_img_vis) *)
Lemma pdh_img_hull : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> 0 < n ->
  @pa_lo _ B_prog_listing PA + 64 <= p -> p + n + 64 <= @pa_hi _ B_prog_listing PA ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md p n HAR Hn Hlo Hhi s Hs.
destruct (pdh_hull_img (@pa_lo _ B_prog_listing PA) (@pa_hi _ B_prog_listing PA) p n s Hn Hlo Hhi
  (proj1 pdh_img_band) ltac:(pose proof (proj2 pdh_img_band); lia) Hs) as [E Hr]. rewrite E.
exact (pdh_img_vis ly S Hp W mem md _ HAR Hr).
Qed.

(* a range inside one of the image's zero-shadow ranges is addressable (alx_zshadow, granule-aligned ranges) *)
Lemma pdh_zs_ra : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> in_zs B p n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n.
Proof.
intros ly S Hp W mem md p n HAR (q & m & Hin & Hq & Hqm).
destruct (pdh_zs_al (q, m) Hin) as [A1 A2]. cbn [fst snd] in A1, A2.
pose proof (alx_zshadow SEGS B ARx LAWS ly S Hp W mem md (q, m) HAR
  ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
cbn [fst snd] in Hz.
apply (range_addressable_sub (aview SEGS (w_H W) mem) SHADOW_OFF q m p n); [|exact Hq|exact Hqm].
exact (zero_shadow_range (aview SEGS (w_H W) mem) SHADOW_OFF q m A1 A2 Hz).
Qed.

(* a byte under route (a) has an addressable shadow: a whole zero-shadow granule, or a const shadow cell that
   alx_const_cells keeps *)
Lemma pdh_ro_ra : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> ro_shadow_ok B a ->
  exists s, aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF a) = Some s /\ saddr_ok a s.
Proof.
intros ly S Hp W mem md a HAR [Hz | (v & Hc & Hv)].
- pose proof (pdh_zs_ra ly S Hp W mem md (a - a mod 8) 8 HAR Hz) as Hr.
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)). apply (Hr a). lia.
- pose proof (alx_const_cells SEGS B ARx LAWS ly S Hp W mem md HAR) as HC.
  rewrite Forall_forall in HC. specialize (HC _ (Hc ly)).
  pose proof ((HC : forall k, (k < 1)%nat ->
    aview SEGS (w_H W) mem (shadow_addr a + Z.of_nat k) = Some (le_byte v 1 k)) 0%nat ltac:(lia)) as HC0.
  cbn [Z.of_nat] in HC0. rewrite Z.add_0_r in HC0. rewrite pdh_le_byte1 in HC0 by lia.
  exists v. split; [exact HC0|].
  unfold saddr_ok. destruct Hv as [Hv | Hv]; [left; exact Hv | right; lia].
Qed.

(* 1. the reader's home is addressable and its shadow hull is visible, at any allocator state whose ledger it is *)
Lemma pdh_home_shadow : forall ly S Hp W mem md Lam peak cnt fail ran most own p n,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> 0 < n ->
  prhReader_home B ly S Hp Lam p n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\ shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own p n HAR HL Hn Hh.
destruct HL as (_ & _ & HF & HP). rewrite Forall_forall in HF. pose proof cf_head_nonneg as H0.
destruct Hh as [[(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & _) | (Hlo & Hhi & Hk)]] | (b & m & Hin & Hnh & Hb & Hm)].
- (* a live harness block: its user range past the hidden head (alx_hshadow, field 14) *)
  destruct (HF (b, m) Hin) as (Hm0 & Hab & Hhp & _). cbn [fst snd] in Hm0, Hab, Hhp.
  destruct (alx_hshadow SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab Hhp) as [Hbs Hhu].
  rewrite (pdh_req_eq (m + cf_head)) in Hbs, Hhu by lia.
  rewrite Z.sub_add in Hbs, Hhu. rewrite Z.add_simpl_r in Hbs, Hhu.
  split; [eapply block_shadow_range; [exact Hbs | lia | lia] |].
  apply (pdh_hull_sub _ b m p n (Hhu ltac:(lia))); lia.
- (* a registered read-only global: the zero-shadow law, the image hull *)
  split; [exact (pdh_zs_ra ly S Hp W mem md p n HAR Hzs) | exact (pdh_img_hull ly S Hp W mem md p n HAR Hn Hlo Hhi)].
- (* an image string under route (a): per-byte shadow, the image hull *)
  split; [| exact (pdh_img_hull ly S Hp W mem md p n HAR Hn Hlo Hhi)].
  intros x Hx. destruct (Hk x Hx) as (_ & _ & _ & Hro). exact (pdh_ro_ra ly S Hp W mem md x HAR Hro).
- (* a live allocator block whose base is not a hidden head: no hidden head lies inside it (the heads are the bases
     of the ledger's blocks, which are other blocks, and blocks are pairwise apart), so alx_shadow applies *)
  assert (HnoH : forall h, In h Hp -> ~ (b <= h < b + req_size m)).
  { intros h Hhp Hr.
    apply (Permutation_in _ HP) in Hhp. apply in_map_iff in Hhp as ((a & k) & Eh & Hak). cbn [fst] in Eh. subst h.
    destruct (HF (a, k) Hak) as (Hk0 & Hab & Hah & _). cbn [fst snd] in Hk0, Hab, Hah.
    destruct (Z.eq_dec (a - cf_head) b) as [E | E]; [rewrite E in Hah; exact (Hnh Hah) |].
    assert (Hne : (a - cf_head, k + cf_head) <> (b, m)) by (intros X; injection X as X1 _; exact (E X1)).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hin Hne) as Hd.
    assert (Hr1 : 1 <= req_size (k + cf_head)) by (apply pdh_req_pos; lia).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  destruct (alx_shadow SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin HnoH) as [Hbs Hhu].
  pose proof (pdh_req_ge m).
  split; [eapply block_shadow_range; [exact Hbs | lia | lia] |].
  apply (pdh_hull_sub _ b (req_size m) p n Hhu); lia.
Qed.

(* 2. each byte of the reader's home is a live block's byte, or a read-only image byte off the runtime's own and off
   errno (which ajournal_x's image clause keeps) *)
Lemma pdh_home_place : forall ly S Hp W mem Lam peak cnt fail ran most own p n,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> prhReader_home B ly S Hp Lam p n ->
  forall a, p <= a < p + n ->
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= a < b + req_size m) \/
  (in_img SEGS a /\ in_roP SEGS pa_relro_lo pa_relro_hi a /\ ~ Exists (in_zr a) (as_owned_static B) /\
   ~ (as_errno B <= a < as_errno B + 4)).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own p n HL Hh a Ha.
destruct HL as (_ & _ & HF & _). rewrite Forall_forall in HF. pose proof cf_head_nonneg as H0.
destruct Hh as [[(b & m & Hin & Hb & Hm) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hin & _ & Hb & Hm)].
- left. destruct (HF (b, m) Hin) as (Hm0 & Hab & _). cbn [fst snd] in Hm0, Hab.
  exists (b - cf_head), (m + cf_head). split; [exact Hab|]. pose proof (pdh_req_ge (m + cf_head)). lia.
- right. destruct (Hro a Ha) as (Hr & Hno & Her). exact (conj (pdh_ro_img a Hr) (conj Hr (conj Hno Her))).
- right. destruct (Hro a Ha) as (Hr & Hno & Her & _). exact (conj (pdh_ro_img a Hr) (conj Hr (conj Hno Her))).
- left. exists b, m. split; [exact Hin|]. pose proof (pdh_req_ge m). lia.
Qed.

(* 3. a source window the view keeps, at the reader's home, is a source window of the new state *)
Lemma pdh_src_rd_at : forall ly S Hp W' mem' md Lam peak cnt fail ran most own W mem text tb,
  ARx ly S Hp W' mem' md -> prh_ledger B ly S Hp W' mem' Lam peak cnt fail ran most own ->
  prhReader_home B ly S Hp Lam text (Z.of_nat (length tb)) -> src_rd W mem text tb ->
  (forall a, text <= a < text + Z.of_nat (length tb) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  src_rd W' mem' text tb.
Proof.
intros ly S Hp W' mem' md Lam peak cnt fail ran most own W mem text tb HAR HL Hh (Hby & H4 & Hc & Ham & _ & _) Hv.
split; [| split; [exact H4 | split; [exact Hc | split; [exact Ham |]]]].
- unfold bytes_at in Hby |- *. apply (pdh_garr8_move W W' mem mem' text text tb Hby).
  intros j Hj. apply Hv. lia.
- destruct (Z_lt_le_dec 0 (Z.of_nat (length tb))) as [Hn | Hn].
  + destruct (pdh_home_shadow ly S Hp W' mem' md Lam peak cnt fail ran most own text _ HAR HL Hn Hh) as [Hr Hu].
    split; [exact Hr | intros _; exact Hu].
  + split; [apply range_addressable_nil; exact Hn | intros Hp0; lia].
Qed.
End c.
