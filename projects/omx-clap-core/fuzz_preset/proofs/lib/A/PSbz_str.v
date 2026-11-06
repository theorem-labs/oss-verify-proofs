(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29 (PresetStrlenPort, c-libc-stdio lane): the shadow half of the bridge from cgif's call-site
   facts (`range_addressable` / `shadow_hull_vis` over `aview`) to the K kit's shadow premise `chk_ok`
   (lib/K/A/I_qck.v:149, the asan half). rule 24: no function proved. PORTED, not new.

   DONOR: origin/cold/port-state-rt-str 17818dd9abc, proofs/omx-clap-core/fuzz_state/lib/A/FSbz_str.v (fuzz_state's
   copy of port-fm's origin/cold/port-fm-rtscan cedf3d02589 proofs/omx-clap-core/fuzz_manifest/lib/A/FMbz_str.v).
   The lemmas the strlen composition (A/PSstrlen.v) needs, in the donor's order, with the donor's names and proofs:
     asegs_tfibsegs            FSbz_str.v:30-31
     FM_SHADOW_OFF             FSbz_str.v:33     (the name is fm's; the value 0x7fff8000 is preset's SHADOW_OFF too)
     shad_of_addr              FSbz_str.v:36-37
     aview_of                  FSbz_str.v:40-41
     mbyte_mrd                 FSbz_str.v:43-45
     bytes_at1_of_view         FSbz_str.v:48-59
     sh_ok_of_saddr_ok         FSbz_str.v:70-75
     shad_range                FSbz_str.v:77-82
     acc_of_range_addressable  FSbz_str.v:85-99
     Z_to_le_bytes_roundtrip   FSbz_str.v:104-121
     word_of_mem               FSbz_str.v:124-126
     ro_C8_of_vis              FSbz_str.v:128-156
     hull_vis_of               FSbz_str.v:160-161
     qc_words_of_hull          FSbz_str.v:163-188
     chk_ok_of_view            FSbz_str.v:191-201
     aview_eq                  FSbz_str.v:211-212
     hull_of_shadow_hull_vis   FSbz_str.v:214-218
   NOT ported (the strlen composition does not use them): view_some_of_bytes_at1 (:62-68), chk_ok_of_AR (:221-231),
   chk_ok_of_ARU (:235-265, fuzz_state's user-poison window; preset's instance carries its hidden heads as the ghost
   list Hp of ARcf instead, and the strlen contract reads the shadow on `mem` itself).

   WHAT CHANGED: module paths fuzz_state -> fuzz_preset; the donor's kit lib/A/Bz (c-asan-rt's copy of bzip2's kit)
   -> this tree's lib/K (bzip2's kit, proofs/bzip2/bzip2_compress_target/lib/K at origin/ossv/recipes c8557374ad2e,
   relocated to preset); the donor's image names (its AB1v.tfibsegs, Bz ImageA.asegs) -> preset's (lib/A/AB1v.v
   tfibsegs, lib/K/Lib/ImageA.v asegs, both Asan.M.loaded_segments); the FSupoison import and its Section variable B
   are dropped with chk_ok_of_ARU. The proof scripts are the donor's. No premise added, no image value. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YP09 YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib Require Import Mem Bytes Cells Step ImageA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A Require Import Shadow I_qck I_consts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* the two trees name the same image *)
Lemma asegs_tfibsegs : asegs = tfibsegs.
Proof. reflexivity. Qed.

Definition FM_SHADOW_OFF : Z := 0x7fff8000.

(* and the same shadow map: the kit's `shad` is the donor's `shadow_of_addr SHADOW_OFF` *)
Lemma shad_of_addr : forall a, shad a = shadow_of_addr FM_SHADOW_OFF a.
Proof. intros a. unfold shad, SHB, shadow_of_addr, FM_SHADOW_OFF. lia. Qed.

(* `aview tfibsegs H mem` (YG0n.v:18) written out *)
Definition aview_of (H : word -> bool) (mem : word -> option byte) : Z -> option Z :=
  fun a => option_map (fun b : byte => bv_unsigned b) (mbyte tfibsegs (mrestrict H mem) a).

Lemma mbyte_mrd : forall (m : word -> option byte) a,
  mbyte tfibsegs m a = mrd asegs m (wa a).
Proof. intros m a. reflexivity. Qed.

(* a byte the donor's reader sees is a byte the walks can read *)
Lemma bytes_at1_of_view : forall (H : word -> bool) (mem : word -> option byte) a v,
  0 <= a < 2 ^ 64 -> aview_of H mem a = Some v ->
  bytes_at asegs (mrestrict H mem) a [Z_to_bv 8 v].
Proof.
  intros H mem a v Ha Hv. unfold aview_of in Hv.
  destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:E; [|discriminate].
  cbn in Hv. injection Hv as <-.
  split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn [length] in Hi. assert (Hi0 : i = 0%nat) by lia. subst i.
  cbn [nth_error]. rewrite Z.add_0_r.
  rewrite mbyte_mrd in E. rewrite E. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma sh_ok_of_saddr_ok : forall (b : byte) a, saddr_ok a (bv_unsigned b) -> sh_ok b a.
Proof.
  intros b a [H|[H1 H2]]; unfold sh_ok; [left; exact H|].
  right. split; [|exact H1]. split; [|exact H2].
  pose proof (bv_unsigned_in_range 8 b) as Hr. lia.
Qed.

Lemma shad_range : forall a, 0 <= a < 2 ^ 63 -> 0 <= shad a < 2 ^ 64.
Proof.
  intros a Ha. unfold shad, SHB.
  assert (Hd : 0 <= a / 8 <= a) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  lia.
Qed.

(* ACCESS: every byte of the range has a shadow byte that allows reading it *)
Lemma acc_of_range_addressable : forall (H : word -> bool) (mem : word -> option byte) p n,
  0 <= p -> 0 <= n -> p + n < 2 ^ 63 ->
  range_addressable (aview_of H mem) FM_SHADOW_OFF p n ->
  acc asegs (mrestrict H mem) p n.
Proof.
  intros H mem p n Hp Hn Hpn HRA i Hi.
  destruct (HRA (p + i) ltac:(lia)) as (s & Hs & Hok).
  rewrite <- shad_of_addr in Hs.
  exists (Z_to_bv 8 s). split.
  - apply bytes_at1_of_view; [apply shad_range; lia | exact Hs].
  - apply sh_ok_of_saddr_ok.
    assert (Hs8 : 0 <= s < 256) by (destruct Hok as [->|[H1 H2]]; lia).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite (Z.mod_small s 256 Hs8). exact Hok.
Qed.

(* ---- the quick check's two aligned shadow words ---- *)

(* the inverse of Mem.v's le bytes: a byte list is what its own little-endian value spells *)
Lemma Z_to_le_bytes_roundtrip : forall (bs : list byte),
  Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  assert (Hrest : 0 <= bytes_le_to_Z bs)
    by (rewrite bytes_le_to_Z_le_val; pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)); lia).
  rewrite lor_shiftl8_add by lia.
  assert (Hhead : Z_to_bv 8 (bv_unsigned b + 256 * bytes_le_to_Z bs) = b).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite (Z.mul_comm 256 (bytes_le_to_Z bs)), Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (Htail : Z.shiftr (bv_unsigned b + 256 * bytes_le_to_Z bs) 8 = bytes_le_to_Z bs).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    rewrite (Z.mul_comm 256 (bytes_le_to_Z bs)), Z.div_add by lia.
    rewrite (Z.div_small (bv_unsigned b) 256) by lia. lia. }
  rewrite Hhead, Htail, IH. reflexivity.
Qed.

(* eight readable bytes are an 8-byte cell: the word they spell *)
Definition word_of_mem (m : word -> option byte) (a : Z) : word :=
  le_bytes_to_word (map (fun j => match mrd asegs m (wa (a + Z.of_nat j)) with
                                  | Some b => b | None => Z_to_bv 8 0 end) (seq 0 8)).

Lemma ro_C8_of_vis : forall (m : word -> option byte) a,
  0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall j, 0 <= j < 8 -> exists b, bytes_at asegs m (a + j) [b]) ->
  ro_cells asegs m a [C8 (word_of_mem m a)].
Proof.
  intros m a Ha Ha8 HB.
  set (bs := map (fun j => match mrd asegs m (wa (a + Z.of_nat j)) with
                           | Some b => b | None => Z_to_bv 8 0 end) (seq 0 8)).
  assert (Hlen : length bs = 8%nat) by (subst bs; rewrite length_map, length_seq; reflexivity).
  assert (Hbs : bytes_at asegs m a bs).
  { split; [lia|]. split; [rewrite Hlen; cbn; lia|].
    intros i Hi. rewrite Hlen in Hi.
    destruct (HB (Z.of_nat i) ltac:(lia)) as (b & _ & _ & Hb).
    specialize (Hb 0%nat ltac:(cbn; lia)). cbn [nth_error] in Hb. rewrite Z.add_0_r in Hb.
    subst bs. rewrite nth_error_map, nth_error_seq.
    replace (i <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    cbn [option_map Nat.add]. rewrite Hb. reflexivity. }
  assert (Hval : bv_unsigned (le_bytes_to_word bs) = bytes_le_to_Z bs).
  { unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small.
    rewrite bytes_le_to_Z_le_val.
    pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Hr.
    rewrite length_map, Hlen in Hr. change (256 ^ Z.of_nat 8) with (2 ^ 64) in Hr. lia. }
  assert (Heq : le8 (le_bytes_to_word bs) = bs).
  { unfold le8, word_to_le_bytes. rewrite Hval, <- Hlen. apply Z_to_le_bytes_roundtrip. }
  split; [cbn; lia|].
  cbn [cells_bytes cbytes app]. rewrite app_nil_r.
  unfold word_of_mem. fold bs. rewrite Heq. exact Hbs.
Qed.

(* the donor's shadow hull (YG0d.v:310) written out *)
Definition hull_vis_of (rd : Z -> option Z) (x n : Z) : Prop :=
  forall s, (FM_SHADOW_OFF + x / 8) / 8 * 8 <= s < (FM_SHADOW_OFF + (x + n - 1) / 8) / 8 * 8 + 8 -> rd s <> None.

Lemma qc_words_of_hull : forall (H : word -> bool) (mem : word -> option byte) p n,
  0 <= p -> 0 < n -> p + n < 2 ^ 63 ->
  hull_vis_of (aview_of H mem) p n ->
  qc_words (mrestrict H mem) p n.
Proof.
  intros H mem p n Hp Hn Hpn HV Hrange.
  assert (Hmono : shad p <= shad (p + n - 1)).
  { unfold shad. assert (p / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia). lia. }
  assert (Hcell : forall a, al8 (shad p) <= a -> a + 8 <= al8 (shad (p + n - 1)) + 8 ->
                  ro_cells asegs (mrestrict H mem) a [C8 (word_of_mem (mrestrict H mem) a)]).
  { intros a Hlo Hhi.
    assert (Hsp : 0 <= shad p < 2 ^ 64) by (apply shad_range; lia).
    assert (Hse : 0 <= shad (p + n - 1) < 2 ^ 64) by (apply shad_range; lia).
    assert (Hal : 0 <= al8 (shad p) /\ al8 (shad (p + n - 1)) + 8 <= 2 ^ 64)
      by (unfold al8; Z.div_mod_to_equations; lia).
    apply ro_C8_of_vis; [lia | lia |].
    intros j Hj.
    assert (HN : aview_of H mem (a + j) <> None).
    { apply HV. unfold FM_SHADOW_OFF. unfold al8, shad, SHB in Hlo, Hhi.
      Z.div_mod_to_equations. lia. }
    destruct (aview_of H mem (a + j)) as [v|] eqn:E; [|exfalso; apply HN; reflexivity].
    exists (Z_to_bv 8 v). apply bytes_at1_of_view; [lia | exact E]. }
  exists (word_of_mem (mrestrict H mem) (al8 (shad p))),
         (word_of_mem (mrestrict H mem) (al8 (shad (p + n - 1)))).
  split; apply Hcell; unfold al8; Z.div_mod_to_equations; lia.
Qed.

(* CHK_OK: what the interceptors' range check needs, from what the donor's call sites carry *)
Theorem chk_ok_of_view : forall (H : word -> bool) (mem : word -> option byte) p n,
  0 <= p -> 0 < n -> p + n < 2 ^ 63 -> n <= 2 ^ 40 -> region_in_mem p n ->
  range_addressable (aview_of H mem) FM_SHADOW_OFF p n ->
  hull_vis_of (aview_of H mem) p n ->
  chk_ok (mrestrict H mem) p n.
Proof.
  intros H mem p n Hp Hn Hpn Hn40 Hreg HRA HV.
  split; [apply acc_of_range_addressable; [lia | lia | lia | exact HRA]|].
  split; [apply qc_words_of_hull; [lia | lia | lia | exact HV]|].
  intros _. split; [exact Hreg | exact Hn40].
Qed.

(* ---- the same, in the donor's own words ---- *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YM05 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0n YG0d.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma aview_eq : forall H mem, aview_of H mem = aview tfibsegs H mem.
Proof. reflexivity. Qed.

Lemma hull_of_shadow_hull_vis : forall rd x n,
  shadow_hull_vis rd x n -> hull_vis_of rd x n.
Proof.
  intros rd x n HV s Hs. apply HV. unfold shadow_addr, SHADOW_OFF. unfold FM_SHADOW_OFF in Hs. exact Hs.
Qed.

End c.
