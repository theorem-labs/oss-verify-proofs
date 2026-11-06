(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSbz_str.v, with its module paths and module names changed; 96 of its 255 lines of code are new or changed. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMbz_str.v (a working branch 3e35620c52e); relocated to libreac/fuzz_disco.asan-ubsan by reloc.py (target disco-Y): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan-ubsan, symbol + offset; table: this file's rows in provenance/evidence/g9-gxa/g9tool/g9-table-disco-Y.tsv); names: A-core -> Y-core (lib.Reusable): AB1v->YB1v. *)
(* The shadow half of the bridge between the donor's ASan state and the string walks'
   memory vocabulary.  The walks ask for `chk_ok m p n` (lib/A/Bz/A/I_qck.v:31) - what the
   interceptors' range check reads - while the donor's call-site contracts carry
   `range_addressable` and `shadow_hull_vis` over `aview` (lib/Reusable/YG0v.v:32,
   YG0d.v:309).  This file turns the second into the first.

   It is stated over the reader `aview_of H mem`, which is `aview tfibsegs H mem` written
   out (YG0n.v:17), so that it does not depend on the part of the core that is still in
   flight (YG0n -> YA0n -> YK18, which does not compile on a working branch bad0693aadc
   yet).  `aview_eq` closes that gap in one line as soon as it does.

   a Theorem Labs lane owns the rest of the bridge (lib/A/FMbz_bridge.v: evt/msteps -> SRr and the frame
   vocabulary); this file is only about the shadow. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YP09 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz.Lib Require Import Mem Bytes Cells Step ImageA.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz.A Require Import Shadow I_qck I_consts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* the two trees name the same image *)
Lemma asegs_tfibsegs : asegs = tfibsegs.
Proof. reflexivity. Qed.

Definition FM_SHADOW_OFF : Z := 0x7fff8000.

(* and the same shadow map: Bz's `shad` is the donor's `shadow_of_addr SHADOW_OFF` *)
Lemma shad_of_addr : forall a, shad a = shadow_of_addr FM_SHADOW_OFF a.
Proof. intros a. unfold shad, SHB, shadow_of_addr, FM_SHADOW_OFF. lia. Qed.

(* `aview tfibsegs H mem` (YG0n.v:17) written out *)
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

(* and back *)
Lemma view_some_of_bytes_at1 : forall (H : word -> bool) (mem : word -> option byte) a b,
  bytes_at asegs (mrestrict H mem) a [b] -> aview_of H mem a = Some (bv_unsigned b).
Proof.
  intros H mem a b (_ & _ & Hb).
  specialize (Hb 0%nat ltac:(cbn; lia)). cbn [nth_error] in Hb. rewrite Z.add_0_r in Hb.
  unfold aview_of. rewrite mbyte_mrd, Hb. reflexivity.
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

(* the inverse of Mem.v:497: a byte list is what its own little-endian value spells *)
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

(* the donor's shadow hull (YG0d.v:309) written out, so that this file does not depend on
   the part of the core that is still in flight *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YM05 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnUpoison.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma aview_eq : forall H mem, aview_of H mem = aview tfibsegs H mem.
Proof. reflexivity. Qed.

Lemma hull_of_shadow_hull_vis : forall rd x n,
  shadow_hull_vis rd x n -> hull_vis_of rd x n.
Proof.
  intros rd x n HV s Hs. apply HV. unfold shadow_addr, SHADOW_OFF. unfold FM_SHADOW_OFF in Hs. exact Hs.
Qed.

(* the plain heap state *)
Theorem chk_ok_of_AR : forall ly S W mem md p n,
  AR tfibsegs B ly S W mem md ->
  0 <= p -> 0 < n -> p + n < 2 ^ 63 -> n <= 2 ^ 40 -> region_in_mem p n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) p n ->
  chk_ok (mrestrict (w_H W) mem) p n.
Proof.
  intros ly S W mem md p n _ Hp Hn Hpn Hn40 Hreg HRA HV.
  apply chk_ok_of_view; [exact Hp | exact Hn | exact Hpn | exact Hn40 | exact Hreg | exact HRA |].
  apply hull_of_shadow_hull_vis. exact HV.
Qed.

(* fm's poison window: a live chunk carries a user-poisoned head, so AR holds of
   `unpoison U mem` while the walk runs on `mem` (a Theorem Labs lane, proofs/omx-clap-core/fuzz_manifest/lib/A/FMupoison.v (a working branch 3e35620c52e)) *)
Theorem chk_ok_of_ARU : forall ly S U W mem md p n,
  ARU tfibsegs B ly S U W mem md ->
  0 <= p -> 0 < n -> p + n < 2 ^ 63 -> n <= 2 ^ 40 -> region_in_mem p n ->
  range_addressable (aview tfibsegs (w_H W) (unpoison U mem)) SHADOW_OFF p n ->
  shadow_hull_vis (aview tfibsegs (w_H W) (unpoison U mem)) p n ->
  (forall i, 0 <= i < n -> in_ush U (shadow_addr (p + i)) = false) ->
  chk_ok (mrestrict (w_H W) mem) p n.
Proof.
  intros ly S U W mem md p n HARU Hp Hn Hpn Hn40 Hreg HRA HV HOUT.
  destruct HARU as (_ & _ & HPO).
  assert (Hsh64 : forall a, 0 <= a < 2 ^ 63 -> 0 <= shadow_addr a < 2 ^ 64).
  { intros a Ha. unfold shadow_addr, SHADOW_OFF.
    assert (0 <= a / 8 <= a) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia. }
  apply chk_ok_of_view; [exact Hp | exact Hn | exact Hpn | exact Hn40 | exact Hreg | |].
  - rewrite (aview_eq (w_H W) mem). intros x Hx.
    destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite <- Hs. symmetry.
    replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) by (unfold shadow_of_addr, shadow_addr; lia).
    apply aview_unpoison_out. rewrite wz by (apply Hsh64; lia).
    replace x with (p + (x - p))%Z by lia. apply HOUT. lia.
  - rewrite (aview_eq (w_H W) mem). intros s Hs.
    destruct (in_ush U s) eqn:EU.
    + rewrite (HPO s EU). discriminate.
    + rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem s); [| rewrite wz; [exact EU |]].
      * apply (hull_of_shadow_hull_vis _ _ _ HV). exact Hs.
      * unfold FM_SHADOW_OFF in Hs. unfold shadow_addr, SHADOW_OFF.
        assert (0 <= p / 8 <= p) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
        assert (0 <= (p + n - 1) / 8 <= p + n - 1)
          by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
        Z.div_mod_to_equations. lia.
Qed.

End c.

(* ---- mem_inv: the walks' standing fact about the mutable store ----
   Every Bz body walk takes `mem_inv asegs m` (A/Bz/Lib/Mem.v:96-102): the store holds no
   byte at a read-only address or at or above 2^47, and no segment reaches that high.  The
   donor states nothing of the kind (YG0d.v:376 defines `rom_clean` but no AR law uses it),
   so the second half is a premise of this lane's runtime contracts - `store_clean` - while
   the first half is a fact about fm.asan's own segment table and is proved here. *)

Definition seg_tops_below (ss : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) ss.

Lemma asegs_below_utop : seg_tops_below asegs UTOP = true.
Proof. vm_compute. reflexivity. Qed.

Lemma seg_addr_below : forall a, seg_addr asegs a = true -> bv_unsigned a < UTOP.
Proof.
  intros a Ha. unfold seg_addr in Ha.
  destruct (find_segment asegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate].
  pose proof (YK04.find_segment_some_spec asegs _ _ s E) as (Hin & Hlo & Hhi).
  pose proof (proj1 (forallb_forall _ _) asegs_below_utop s Hin) as Hb.
  apply Z.leb_le in Hb. lia.
Qed.

(* what this lane's contracts carry about the store, for the part the donor does not state *)
Definition store_clean (H : word -> bool) (mem : word -> option byte) : Prop :=
  forall a : word, mrestrict H mem a <> None -> ro_addr asegs a = false /\ bv_unsigned a < UTOP.

Lemma mem_inv_of_store_clean : forall H mem,
  store_clean H mem -> mem_inv asegs (mrestrict H mem).
Proof.
  intros H mem HS a. unfold mem_ok_at.
  apply andb_true_intro. split.
  - destruct (seg_addr asegs a) eqn:ES; [|reflexivity].
    apply Z.ltb_lt. apply seg_addr_below. exact ES.
  - destruct (mrestrict H mem a) as [b|] eqn:EM; [|reflexivity].
    destruct (HS a ltac:(rewrite EM; discriminate)) as (Hro & Hlt).
    rewrite Hro. cbn [negb]. apply andb_true_intro. split; [reflexivity | apply Z.ltb_lt; exact Hlt].
Qed.

(* lib/A/FMH_Base.v does not state the same fact; in the donor's vocabulary it is the premise of store_clean_of_donor (FMbz_str.v:318:
   no byte `in_rom`, everything below 2^47).
   This is the step from that form to the one the walks ask for. *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma ro_addr_in_rom : forall a : word, ro_addr asegs a = true -> in_rom tfibsegs (bv_unsigned a).
Proof.
  intros a Ha. unfold ro_addr in Ha.
  destruct (find_segment asegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate].
  apply negb_true_iff in Ha.
  pose proof (YK04.find_segment_some_spec asegs _ _ s E) as (Hin & Hlo & Hhi).
  exists s. split; [exact Hin | split; [exact Ha | lia]].
Qed.

Lemma store_clean_of_donor : forall (H : word -> bool) (mem : word -> option byte),
  (forall a : word, mrestrict H mem a <> None ->
     ~ in_rom tfibsegs (bv_unsigned a) /\ bv_unsigned a < 2 ^ 47) ->
  store_clean H mem.
Proof.
  intros H mem HD a Ha. destruct (HD a Ha) as (Hrom & Hlt).
  split; [|exact Hlt].
  destruct (ro_addr asegs a) eqn:E; [|reflexivity].
  exfalso. apply Hrom. apply ro_addr_in_rom. exact E.
Qed.

End d.
