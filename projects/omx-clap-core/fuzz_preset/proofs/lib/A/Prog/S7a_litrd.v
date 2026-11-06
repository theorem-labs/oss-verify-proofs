(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: THE GENERIC LITERAL READER (slice S7a, a Theorem Labs lane; the ONE copy, cited by S7a_indent_wit.v
   and by the writer row's literal witnesses). Function-free: it states no walk and Requires no walk file, only the
   engine, PRH_Base and the image vocabulary.
   - s7w_lit_rd (any B, any ARx with AR_laws_x, any PAImg whose bounds pa_lo / pa_hi lie above page 0 and below
     kLowMemEnd): kept_img (PRH_Base.v, route (a), per instance), the ROM bytes and one img_shadow_cover check give
     src_rd and kept_at at any ARx state with arodata_okP. Its per-byte shadow argument is WalkS10's s10_src_img
     (lib/A/Prog/S10TxState.v at a working branch 8a8cbf8b36a6); that lemma's two stand-ins are replaced:
     the hull visibility by the cover check (YImgShadowCover.img_shadow_cover_sound), and zs_aligned by a premise an
     instance discharges by vm_compute.
   - the closed-check helpers an instance witness uses: s7w_ro_b (a read-only segment holds a), s7w_zr_b (some range
     of a list holds a), s7w_is_z1 / s7w_cell_in (a const cell found by computation), s7w_pst_clear_b (a list of
     ranges clear of the read-only bytes and the relro range), each with its soundness lemma.
   Numerals: 8, 64 (LENGTH: a granule, a shadow granule's span), 256 (a byte's range), 0x7fff8000 (SHADOW_OFF). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop YK1g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YImgShadowCover.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* a read-only segment holds a (h-verbs-1's lit_inst_in_rom_b, lib/A/Prog/literal_inst.v at 68059ec877b4) *)
Definition s7w_ro_b (segs : list Segment) (a : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
    (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.
Lemma s7w_ro_b_sound : forall segs a, s7w_ro_b segs a = true ->
  exists sg, In sg segs /\ seg_writable sg = false /\
    Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
intros segs a H. apply existsb_exists in H as (sg & Hin & H). cbv beta in H.
apply andb_true_iff in H as [H H2]. apply andb_true_iff in H as [H0 H1]. apply negb_true_iff in H0.
exists sg. split; [exact Hin|]. split; [exact H0|].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
(* some range of a list holds a *)
Definition s7w_zr_b (l : list (Z * Z)) (a : Z) : bool := existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l.
Lemma s7w_zr_b_sound : forall l a, s7w_zr_b l a = false -> ~ Exists (in_zr a) l.
Proof.
intros l a H HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
assert (E : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
unfold s7w_zr_b in H. rewrite E in H. discriminate H.
Qed.

(* a const cell `z1 (ANum x) v` of a list, found by computation (no index typed) *)
Definition s7w_is_z1 (x v : Z) (c : acell) : bool :=
  match c_at c, c_w c, c_val c with
  | ANum y, 1%nat, AV (ANum w) => (y =? x) && (w =? v)
  | _, _, _ => false
  end.
Lemma s7w_is_z1_sound : forall x v c, s7w_is_z1 x v c = true -> c = z1 (ANum x) v.
Proof.
intros x v [ca cw cv] H. unfold s7w_is_z1 in H. cbn [c_at c_w c_val] in H.
destruct ca; try discriminate H. destruct cw as [|[|cw]]; try discriminate H.
destruct cv as [e|m w]; try discriminate H. destruct e; try discriminate H.
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Lemma s7w_cell_in : forall x v l, existsb (s7w_is_z1 x v) l = true -> In (z1 (ANum x) v) l.
Proof.
intros x v l H. apply existsb_exists in H as (c & Hc & H). rewrite <- (s7w_is_z1_sound x v c H). exact Hc.
Qed.

(* the statics against the read-only bytes *)
Definition s7w_pst_clear_b (segs : list Segment) (lo hi : Z) (l : list (Z * Z)) : bool :=
  forallb (fun r => forallb (fun sg => seg_writable sg || (fst r + snd r <=? Z.of_N (seg_base sg)) ||
                                       (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? fst r)) segs &&
                    ((fst r + snd r <=? lo) || (hi <=? fst r))) l.
Lemma s7w_pst_clear_sound : forall segs lo hi l, s7w_pst_clear_b segs lo hi l = true ->
  forall a, in_roP segs lo hi a -> ~ Exists (in_zr a) l.
Proof.
intros segs lo hi l H a Hro HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
unfold s7w_pst_clear_b in H. rewrite forallb_forall in H. specialize (H r Hr).
apply andb_true_iff in H as [Hs Hrel]. rewrite forallb_forall in Hs.
destruct Hro as [(sg & Hin & Hw & Hb) | Hb].
- specialize (Hs sg Hin). rewrite Hw in Hs. cbn [orb] in Hs.
  apply orb_true_iff in Hs as [H1 | H1]; apply Z.leb_le in H1; lia.
- apply orb_true_iff in Hrel as [H1 | H1]; apply Z.leb_le in H1; lia.
Qed.

(* ---- THE GENERIC STEP: an image literal under route (a) is a readable, kept source at any ARx state ---- *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := (@pa_segs rc L PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.

(* one read-back byte (WalkS10's s10_val1_of_aview, S10TxState.v :183-194 at 8a8cbf8b36a6) *)
Lemma s7w_val1_of_aview : forall (H : word -> bool) mem a v, aview segs H mem a = Some v ->
  val_mem segs (mrestrict H mem) a 1 v /\ 0 <= v < 256.
Proof.
intros H mem a v E. unfold aview in E.
destruct (mbyte segs (mrestrict H mem) a) as [bb|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as <-. pose proof (bv_unsigned_in_range 8 bb) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|exact Hr].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb.
f_equal. rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by exact Hr. reflexivity.
Qed.

Lemma s7w_lit_rd : forall (zs : list (Z * Z)) (cs : list acell) (Lo Hi : Z) ly S Hp (W : world segs) mem md s src,
  4096 <= @pa_lo rc L PA -> @pa_hi rc L PA <= kLowMemEnd ->
  Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B) ->
  img_shadow_cover zs cs Lo Hi = true -> incl zs (as_zero_shadow B) -> (forall ly, incl cs (as_const B ly)) ->
  Lo <= s / 8 / 8 * 64 -> (s + Z.of_nat (length src) - 1) / 8 / 8 * 64 + 64 <= Hi ->
  ARx ly S Hp W mem md -> arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) ->
  kept_img (PA := PA) B s (Z.of_nat (length src)) -> (0 < length src)%nat ->
  (forall j, (j < length src)%nat ->
     option_map (fun bb : byte => bv_unsigned bb) (seg_rom segs (Z_to_bv 64 (s + Z.of_nat j))) = Some (nth j src 0)) ->
  src_rd (PA := PA) W mem s src /\ kept_at (PA := PA) B [] s (Z.of_nat (length src)).
Proof.
intros zs cs Lo Hi ly S Hp W mem md s src HPL HPH ZA Hc Iz Ic HLo HHi HAR HRO HKI Hn Hrom.
pose proof HKI as (Hlo & Hhi & Hro).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
split; [|right; right; exact HKI].
split; [|split; [lia|split; [lia|split; [unfold amem_range; left; lia|split]]]].
- (* the bytes: read-only, so the image's (arodata_okP) *)
  unfold bytes_at. intros j Hj.
  destruct (Hro (s + Z.of_nat j) ltac:(lia)) as (Hr & Hno & Her & _).
  pose proof (HRO _ Hr Hno Her) as E. rewrite (Hrom j Hj) in E.
  exact (s7w_val1_of_aview (w_H W) mem _ _ E).
- (* each byte's shadow: a zero-shadow granule (alx_zshadow) or a const-shadow cell (alx_const_cells) *)
  intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzs | (v & Hcl & Hv)]).
  + destruct Hzs as (q & m & Hin & Hq & Hqm).
    pose proof (proj1 (Forall_forall _ _) ZA (q, m) Hin) as (Hq8 & Hm8). cbn [fst snd] in Hq8, Hm8.
    pose proof (alx_zshadow _ _ _ LAWS ly S Hp W mem md (q, m) HAR ltac:(right; exact Hin)) as Hz.
    cbn [fst snd] in Hz. pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
    exact (zero_shadow_range (aview segs (w_H W) mem) SHADOW_OFF q m Hq8 Hm8 Hz x ltac:(lia)).
  + pose proof (proj1 (Forall_forall _ _) (alx_const_cells _ _ _ LAWS ly S Hp W mem md HAR) _ (Hcl ly)) as Hcell.
    unfold cell_holds, z1, c1 in Hcell. cbn [c_at c_w c_val aeval] in Hcell.
    specialize (Hcell 0%nat ltac:(lia)). rewrite Z.add_0_r in Hcell.
    exists v. split; [|unfold saddr_ok; lia].
    unfold shadow_of_addr. unfold shadow_addr in Hcell. rewrite Hcell. f_equal.
    unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r, (Z.mod_small v (2 ^ 8)) by lia. apply Z.mod_small. lia.
- (* the shadow hull: each byte is the shadow of a granule in [Lo, Hi), covered by the lists *)
  intros _ sh Hsh. set (n := Z.of_nat (length src)) in *.
  unfold shadow_addr, SHADOW_OFF in Hsh.
  replace (0x7fff8000 + s / 8) with (s / 8 + 0xffff000 * 8) in Hsh by lia.
  replace (0x7fff8000 + (s + n - 1) / 8) with ((s + n - 1) / 8 + 0xffff000 * 8) in Hsh by lia.
  rewrite !Z.div_add in Hsh by lia.
  assert (E : shadow_addr (8 * (sh - SHADOW_OFF)) = sh)
    by (unfold shadow_addr; rewrite Z.mul_comm, Z.div_mul by lia; lia).
  rewrite <- E.
  apply (img_shadow_cover_sound (aview segs (w_H W) mem) zs cs Lo Hi Hc).
  + intros r Hr. exact (alx_zshadow _ _ _ LAWS ly S Hp W mem md r HAR ltac:(right; exact (Iz r Hr))).
  + intros x Hx. unfold shv_cell_bytes in Hx. apply in_flat_map in Hx as (c & Hc' & Hx).
    exact (shv_acell_bytes_vis B ly _ c x
      (proj1 (Forall_forall _ _) (alx_const_cells _ _ _ LAWS ly S Hp W mem md HAR) c (Ic ly c Hc')) Hx).
  + unfold SHADOW_OFF. lia.
Qed.
End g.
