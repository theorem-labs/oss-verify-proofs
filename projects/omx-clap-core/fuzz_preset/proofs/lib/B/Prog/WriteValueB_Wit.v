(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d, unstripped twin c90d4fa54d43), lane
   WriteValueB (h-rw-pre-7): the INSTANCE WITNESSES of the image facts the write_value walk keeps as Section hypotheses
   (lib/B/Prog/WriteValueB_Base.v Section h, lib/B/Prog/WriteValueB_Leaf.v Section cl). rule 24: no function proved
   (kind: instance discharge of image facts only).
   THE INSTANCE: PA := PI_prog_B (lib/B/PAImg_prog.v), B := YD2l.TfibB (lib/Reusable/YD2l.v), ci := CfImgB.CfImg_B
   (lib/AU/CfImgB.v), cp := CfParamsPreset.CfParams_preset, PI := prh_img_B, ARx := ARcfx = YG0ncf.ARcf SEGS TfibB /\
   YG0ncf.xs_placed_cf (the spelling of lib/A/Prog/FuzzFree.v:379 and lib/B/Prog/FuzzFreeB.v:296; YGcallcf.v's ARxs).
   fx and rc stay Section Context. Each wvw_<hyp> states its hypothesis's TEXT at that instance; the two type checks at
   the end of Section w apply WriteValueB_Base.wv_disj_img and WriteValueB_Leaf.wv_leaf_num to them, so each text is
   checked against the walk's own Section hypothesis by the kernel.
   - wvw_laws (LAWS): citation, YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf (lib/B/Prog/ex_ws_cf.v's route).
   - wvw_tl (TL): citation, PALibB.exvi_eh_palib.
   - wvw_hw (HW, Leaf): citation, PALibB.exvi_eh_head (= CfParamsPreset.preset_head_wide).
   - wvw_hent (Hent): vm_compute on the closed listing (B_prog_sigma / B_prog_val / B_prog_slot).
   - wvw_hobj (Hobj): vm_compute of a cover check (S1ImgCheck.in_img_b at each of the 8 bytes, YP08.zallb) at the GOT word
     A_OBJ 0 and at the shadow-base cell A_OBJ 12.
   - wvw_hjt (HJT): vm_compute of one boolean per table word (wvw_jt_b, all seven by forallb over seq 0 7): the ROM
     bytes of the word against WV_JTW k (wvw_vm_b: mbyte with the empty memory falls to seg_rom), the bounds, the
     apartness from A_OBJ 0 / A_OBJ 12, and per byte in_img / in_roP / not as_owned_static / not errno
     (wvw_ro_byte_b); soundness lemmas are generic.
   - wvw_hpstro (HPSTRO): citation, S1ImgB.pst_not_ro_B (the S1ImgA.pst_not_ro_A template on this base).
   - wvw_hlit (HLIT): the GENERIC STEP wvw_lit_rd, PORTED from image-A lane h-rw-pre-5 WalkS7aR's S7a_indent_wit.v
     s7w_lit_rd (origin/cold/h-rw-pre-5-walk-s7a-put c2f1ac7094cb, blob 0792f0b58114; its own source WalkS10's
     s10_src_img), with s7w_val1_of_aview, s7w_ro_b's role taken by S1ImgCheck.in_ro_b and s7w_zr_b; the change: kept_img
     now states the instance's pa_lo / pa_hi (PRH_Base.v blob fdb45545469b), so the two numeric facts the template read
     off IMG_LO / IMG_TOP are premises (4096 <= pa_lo, pa_hi <= kLowMemEnd), each closed here by vm_compute. Route:
     kept_img (route (a): read-only, not owned, not errno, ro_shadow_ok per byte, the const-shadow cells kept by
     alx_const_cells / the zero-shadow ranges by alx_zshadow), the ROM bytes, and one img_shadow_cover check of the
     shadow hull. The per-literal facts are one closed boolean wvw_lit_b (all ten by forallb over wv_lits): the bounds,
     the byte checks (wvw_lit_byte_b, with ro_shadow_ok decided by wvw_rso_b over as_zero_shadow TfibB and
     YF0m.Tfib_const_shadow), the ROM bytes (wvw_romb, PORTED from PvB_ImgFacts.v pvi_romb / pvi_romb_sound,
     origin/cold/h-rw-pre-7-bp-parse_value 522b151df78a, blob 3fdd18a3ae21) and the hull cover.
     wvw_const_incl / wvw_zs_al are PvB_Inst.v's pvI_const_incl / pvI_zs_al (same branch, blob df4d9b627aa3).
   - wvw_strlen (STRLEN, Leaf): citation of the PROVED row lib/AU/PSstrRo.v ps_strlen_xrom_xs_B (blob 45e63604063e,
     c-libc-stdio lane: astrlen_realizes_xrom at ARcf /\ xs_placed_cf, any rlo / rhi, from PSstrlen.v
     ps_strlen_realizes_cfm_B_closed) at B := TfibB with YD2l.TfibB_syms, after the pc equation
     SIGMA AS___wrap_strlen = cf_pc_strlen CfImg_B (vm_compute).
   The former named premise SRC-CEIL needs no witness here: at the batch kit's cut it is AR_laws_x's field alx_blocks_ceil8,
   so wvw_laws carries it.
   Every vm_compute is on a closed goal (the listing tables, rsegs, TfibB's lists).
   Numerals: 4 (LENGTH: a table word, errno), 7 (COUNT: the table words, tags 0 .. 6), 8 (LENGTH: a word / a granule),
   64 (LENGTH: kept_img's margin, a shadow granule's span), 256 / 2 ^ 8 (byte range), 4096 (LENGTH: page 0),
   2 ^ 31 - 1 (WORD: the text's bound), 0 / 1 (the shadow cell's width and the zero shadow value); in the ported
   generic step only, 0x7fff8000 (the ASan shadow offset SHADOW_OFF, unfolded: a runtime constant, not an image value)
   and 0xffff000 (= SHADOW_OFF / 8). No image ADDRESS is typed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgShadowCover.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YP08.
(* YI04.val_mem reads YO0f's le_byte (YG0f's has the same body under another name) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0f.
(* the walk's files: Required, not Imported, to name their definitions (no Section of theirs is opened) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require WriteValueB_Base WriteValueB_Leaf.
(* the instance and its proved facts: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PSstrRo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require S1ImgB.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List Bool.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================= 1. generic checkers and their soundness (no image) ======================= *)

(* no range of a list holds a (S7a_indent_wit.v s7w_zr_b / s7w_zr_b_sound, ported) *)
Definition wvw_zr_b (l : list (Z * Z)) (a : Z) : bool := existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l.
Lemma wvw_zr_b_sound : forall l a, wvw_zr_b l a = false -> ~ Exists (in_zr a) l.
Proof.
intros l a H HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
assert (E : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
unfold wvw_zr_b in H. rewrite E in H. discriminate H.
Qed.

(* S1ImgCheck's in_ro_b (both arms of in_roP) is sound *)
Lemma wvw_in_ro_b_sound : forall segs rlo rhi a, S1ImgCheck.in_ro_b segs rlo rhi a = true -> in_roP segs rlo rhi a.
Proof.
intros segs rlo rhi a H. unfold S1ImgCheck.in_ro_b in H. apply orb_true_iff in H as [H|H].
- left. apply existsb_exists in H as (s & Hs & Hb). apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply negb_true_iff in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  exists s. split; [exact Hs|]. split; [exact H1|]. lia.
- right. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* one byte: in the image, read-only, not a runtime-owned static, not errno *)
Definition wvw_ro_byte_b (segs : list Segment) (rlo rhi : Z) (B : asyms) (x : Z) : bool :=
  S1ImgCheck.in_img_b segs x && S1ImgCheck.in_ro_b segs rlo rhi x && negb (wvw_zr_b (as_owned_static B) x) &&
  negb ((as_errno B <=? x) && (x <? as_errno B + 4)).
Lemma wvw_ro_byte_sound : forall segs rlo rhi B x, wvw_ro_byte_b segs rlo rhi B x = true ->
  in_img segs x /\ in_roP segs rlo rhi x /\ ~ Exists (in_zr x) (as_owned_static B) /\
  ~ (as_errno B <= x < as_errno B + 4).
Proof.
intros segs rlo rhi B x H. unfold wvw_ro_byte_b in H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
split; [exact (S1ImgCheck.in_img_b_sound _ _ H1)|].
split; [exact (wvw_in_ro_b_sound _ _ _ _ H2)|].
split; [apply negb_true_iff in H3; exact (wvw_zr_b_sound _ _ H3)|].
apply negb_true_iff in H4. intros [E1 E2].
apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite E1, E2 in H4. discriminate H4.
Qed.

(* the byte facts over [a, a + n) from one zallb check *)
Lemma wvw_ro_range_sound : forall segs rlo rhi B a n, YP08.zallb (wvw_ro_byte_b segs rlo rhi B) a n = true ->
  forall i, 0 <= i < Z.of_nat n ->
  in_img segs (a + i) /\ in_roP segs rlo rhi (a + i) /\ ~ Exists (in_zr (a + i)) (as_owned_static B) /\
  ~ (as_errno B <= a + i < as_errno B + 4).
Proof.
intros segs rlo rhi B a n H i Hi. apply wvw_ro_byte_sound. apply (YP08.zallb_sound _ n a); [exact H | lia].
Qed.

Lemma wvw_img_range_sound : forall segs a n, YP08.zallb (S1ImgCheck.in_img_b segs) a n = true ->
  forall i, 0 <= i < Z.of_nat n -> in_img segs (a + i).
Proof. intros segs a n H i Hi. apply S1ImgCheck.in_img_b_sound. apply (YP08.zallb_sound _ n a); [exact H | lia]. Qed.

(* an n-byte value in the ROM alone (mbyte with the empty memory reads seg_rom), as a boolean *)
Definition wvw_vm_b (segs : list Segment) (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun j => match mbyte segs (fun _ => None) (a + Z.of_nat j) with
                    | Some b => bv_unsigned b =? YO0f.le_byte v n j
                    | None => false
                    end) (seq 0 n).
Lemma wvw_vm_sound : forall segs a n v, wvw_vm_b segs a n v = true -> val_mem segs (fun _ => None) a n v.
Proof.
intros segs a n v H j Hj. unfold wvw_vm_b in H. rewrite forallb_forall in H.
specialize (H j ltac:(apply in_seq; lia)).
destruct (mbyte segs (fun _ => None) (a + Z.of_nat j)) as [b|] eqn:E; [|discriminate H].
apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- H.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by exact Hr. reflexivity.
Qed.

(* the rom bytes at [p, p + length l) are l (PvB_ImgFacts.v pvi_romb / pvi_romb_sound, ported) *)
Fixpoint wvw_romb (segs : list Segment) (p : Z) (l : list Z) : bool :=
  match l with
  | [] => true
  | b :: t => match YK11.seg_rom segs (Z_to_bv 64 p) with
              | Some x => (bv_unsigned x =? b) && wvw_romb segs (p + 1) t
              | None => false
              end
  end.
Lemma wvw_romb_sound : forall segs l p, wvw_romb segs p l = true -> forall j, (j < length l)%nat ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 (p + Z.of_nat j))) = Some (nth j l 0).
Proof.
intros segs l. induction l as [|b t IH]; intros p H j Hj; cbn [length] in Hj; [lia|].
cbn [wvw_romb] in H. destruct (YK11.seg_rom segs (Z_to_bv 64 p)) as [x|] eqn:E; [|discriminate].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
destruct j as [|j].
- cbn [nth Z.of_nat]. rewrite Z.add_0_r, E. cbn [option_map]. rewrite H1. reflexivity.
- cbn [nth]. replace (p + Z.of_nat (S j)) with (p + 1 + Z.of_nat j) by lia. apply IH; [exact H2 | lia].
Qed.

(* a one-byte const cell at sa whose value passes P *)
Definition wvw_z1_match (sa : Z) (P : Z -> bool) (c : acell) : bool :=
  match c with
  | ACell (ANum x) w (AV (ANum v)) => Nat.eqb w 1 && Z.eqb x sa && P v
  | _ => false
  end.
Lemma wvw_z1_match_sound : forall sa P c, wvw_z1_match sa P c = true -> exists v, c = z1 (ANum sa) v /\ P v = true.
Proof.
intros sa P [ca cw cv] H. unfold wvw_z1_match in H.
destruct ca; cbn in H; try discriminate H.
destruct cv as [e|mask v0]; cbn in H; try discriminate H.
destruct e; cbn in H; try discriminate H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. subst. eexists. split; [reflexivity | exact H3].
Qed.

(* ro_shadow_ok (PRH_Base.v) as a boolean: a whole zero-shadow granule, or a const-shadow cell whose value admits the
   byte *)
Definition wvw_vok (x v : Z) : bool := (v =? 0) || ((x mod 8 <? v) && (v <? 8)).
Definition wvw_rso_b (zs : list (Z * Z)) (cs : list acell) (x : Z) : bool :=
  existsb (fun r => (fst r <=? x - x mod 8) && (x - x mod 8 + 8 <=? fst r + snd r)) zs ||
  existsb (wvw_z1_match (shadow_addr x) (wvw_vok x)) cs.
Lemma wvw_rso_sound : forall (B : asyms) zs cs x,
  incl zs (as_zero_shadow B) -> (forall ly, incl cs (as_const B ly)) -> wvw_rso_b zs cs x = true ->
  ro_shadow_ok B x.
Proof.
intros B zs cs x Iz Ic H. unfold ro_shadow_ok, in_zs. unfold wvw_rso_b in H. apply orb_true_iff in H as [H|H].
- left. apply existsb_exists in H as ([q m] & Hin & Hb). apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2.
  exists q, m. split; [exact (Iz _ Hin)|]. lia.
- right. apply existsb_exists in H as (c & Hin & Hb).
  destruct (wvw_z1_match_sound _ _ _ Hb) as (v & -> & Hv).
  exists v. split; [intros ly; exact (Ic ly _ Hin)|].
  unfold wvw_vok in Hv. apply orb_true_iff in Hv as [Hv|Hv]; [left; apply Z.eqb_eq; exact Hv|].
  right. apply andb_prop in Hv as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* ======================= 2. THE GENERIC STEP (any B, any ARx with AR_laws_x, any PAImg) =======================
   PORTED from S7a_indent_wit.v s7w_val1_of_aview / s7w_lit_rd (origin/cold/h-rw-pre-5-walk-s7a-put c2f1ac7094cb,
   blob 0792f0b58114): an image literal under kept_img (route (a)) with its ROM bytes and a cover of its shadow hull is
   a readable, kept source at any ARx state with arodata_okP. The one change: the template's IMG_LO / IMG_TOP
   arithmetic is the instance's pa_lo / pa_hi, bounded by the two premises PLO / PHI. *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation segs := (@pa_segs rc L PA).

Lemma wvw_val1_of_aview : forall (H : word -> bool) mem a v, aview segs H mem a = Some v ->
  val_mem segs (mrestrict H mem) a 1 v /\ 0 <= v < 256.
Proof.
intros H mem a v E. unfold aview in E.
destruct (mbyte segs (mrestrict H mem) a) as [bb|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as <-. pose proof (bv_unsigned_in_range 8 bb) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|exact Hr].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb.
f_equal. rewrite YI04.le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by exact Hr. reflexivity.
Qed.

Lemma wvw_lit_rd : forall (B : asyms)
    (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop) (HL : Z),
  AR_laws_x segs B ARx HL ->
  forall (zs : list (Z * Z)) (cs : list acell) (Lo Hi : Z) ly S Hp (W : world segs) mem md s src,
  4096 <= @pa_lo rc L PA -> @pa_hi rc L PA <= kLowMemEnd ->
  Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B) ->
  img_shadow_cover zs cs Lo Hi = true -> incl zs (as_zero_shadow B) -> (forall ly, incl cs (as_const B ly)) ->
  Lo <= s / 8 / 8 * 64 -> (s + Z.of_nat (length src) - 1) / 8 / 8 * 64 + 64 <= Hi ->
  ARx ly S Hp W mem md ->
  arodata_okP segs (@pa_relro_lo rc L PA) (@pa_relro_hi rc L PA) B (aview segs (w_H W) mem) ->
  kept_img (PA := PA) B s (Z.of_nat (length src)) ->
  (forall j, (j < length src)%nat ->
     option_map (fun bb : byte => bv_unsigned bb) (YK11.seg_rom segs (Z_to_bv 64 (s + Z.of_nat j))) =
       Some (nth j src 0)) ->
  src_rd (PA := PA) W mem s src /\ kept_at (PA := PA) B [] s (Z.of_nat (length src)).
Proof.
intros B ARx HL LAWS zs cs Lo Hi ly S Hp W mem md s src PLO PHI ZA Hc Iz Ic HLo HHi HAR HRO HKI Hrom.
pose proof HKI as (Hlo & Hhi & Hro).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
split; [|right; right; exact HKI].
split; [|split; [lia|split; [lia|split; [unfold amem_range; left; lia|split]]]].
- (* the bytes: read-only, so the image's (arodata_okP) *)
  unfold bytes_at. intros j Hj.
  destruct (Hro (s + Z.of_nat j) ltac:(lia)) as (Hr & Hno & Her & _).
  pose proof (HRO _ Hr Hno Her) as E. rewrite (Hrom j Hj) in E.
  exact (wvw_val1_of_aview (w_H W) mem _ _ E).
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

(* ======================= 3. THE WITNESSES at the instance ======================= *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PI_prog_B).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
#[local] Abbreviation RLO := (@pa_relro_lo _ B_prog_listing PI_prog_B).
#[local] Abbreviation RHI := (@pa_relro_hi _ B_prog_listing PI_prog_B).
(* the allocator relation of the walk at the instance (FuzzFree.v:379 / FuzzFreeB.v:296's ARcfx) *)
#[local] Abbreviation ARcfx := (fun ly S Hp (W : world SEGS) mem md =>
  YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

(* ---- LAWS / TL / HW: citations ---- *)
Lemma wvw_laws : AR_laws_x SEGS TB ARcfx (@cf_head CP).
Proof. exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)). Qed.

Lemma wvw_tl : PALib (PI := PI_prog_B) TB.
Proof. exact PALibB.exvi_eh_palib. Qed.

Lemma wvw_hw : @prh_head_wide CP.
Proof. exact PALibB.exvi_eh_head. Qed.

(* ---- Hent: write_value's entry is its listing slot (closed) ---- *)
Lemma wvw_hent : SIGMA AS_write_value = BASE + WriteValueB_Base.AF_write_value.
Proof. apply Z.eqb_eq. vm_compute. reflexivity. Qed.

(* ---- Hobj: the GOT word and the shadow-base cell are 8 image bytes each (closed cover check) ---- *)
Lemma wvw_hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
Proof.
assert (H0 : YP08.zallb (S1ImgCheck.in_img_b SEGS) (VAL (A_OBJ 0)) 8 = true) by (vm_compute; reflexivity).
assert (H12 : YP08.zallb (S1ImgCheck.in_img_b SEGS) (VAL (A_OBJ 12)) 8 = true) by (vm_compute; reflexivity).
intros i Hi. split; [exact (wvw_img_range_sound _ _ 8 H0 i Hi) | exact (wvw_img_range_sound _ _ 8 H12 i Hi)].
Qed.

(* ---- HJT: the seven table words, one closed boolean each ---- *)
Definition wvw_jt_b (k : nat) : bool :=
  wvw_vm_b SEGS (VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k) 4
    (WriteValueB_Base.WV_JTW (PA := PI_prog_B) k) &&
  (0 <=? WriteValueB_Base.WV_JTW (PA := PI_prog_B) k) &&
  (WriteValueB_Base.WV_JTW (PA := PI_prog_B) k <=? 2 ^ 31 - 1) &&
  (0 <=? VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k) &&
  (VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k + 4 <=? kLowMemEnd) &&
  ((VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k + 4 <=? VAL (A_OBJ 0)) ||
   (VAL (A_OBJ 0) + 8 <=? VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k)) &&
  ((VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k + 4 <=? VAL (A_OBJ 12)) ||
   (VAL (A_OBJ 12) + 8 <=? VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k)) &&
  YP08.zallb (wvw_ro_byte_b SEGS RLO RHI TB) (VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k) 4.

Lemma wvw_jt_all : forallb wvw_jt_b (seq 0 7) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wvw_hjt : forall k : nat, (k < 7)%nat ->
  val_mem SEGS (fun _ => None) (VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k) 4
    (WriteValueB_Base.WV_JTW (PA := PI_prog_B) k) /\
  0 <= WriteValueB_Base.WV_JTW (PA := PI_prog_B) k <= 2 ^ 31 - 1 /\
  0 <= VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k /\
  VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k + 4 <= kLowMemEnd /\
  (VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k + 4 <= VAL (A_OBJ 0) \/
   VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k) /\
  (VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k + 4 <= VAL (A_OBJ 12) \/
   VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k) /\
  (forall i, 0 <= i < 4 -> in_img SEGS (VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k + i) /\
     in_roP SEGS RLO RHI (VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k + i) /\
     ~ Exists (in_zr (VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k + i)) (as_owned_static TB) /\
     ~ (as_errno TB <= VAL (A_OBJ 2) + WriteValueB_Base.WV_JT + 4 * Z.of_nat k + i < as_errno TB + 4)).
Proof.
intros k Hk.
assert (H : wvw_jt_b k = true).
{ pose proof wvw_jt_all as A. rewrite forallb_forall in A. apply A. apply in_seq. lia. }
unfold wvw_jt_b in H.
apply andb_prop in H as [H Hro]. apply andb_prop in H as [H Hd12]. apply andb_prop in H as [H Hd0].
apply andb_prop in H as [H Hlow]. apply andb_prop in H as [H Ha0]. apply andb_prop in H as [H Hv1].
apply andb_prop in H as [Hvm Hv0].
apply Z.leb_le in Hv0. apply Z.leb_le in Hv1. apply Z.leb_le in Ha0. apply Z.leb_le in Hlow.
split; [exact (wvw_vm_sound _ _ _ _ Hvm)|].
split; [split; [exact Hv0 | exact Hv1]|].
split; [exact Ha0|]. split; [exact Hlow|].
split; [apply orb_true_iff in Hd0 as [D|D]; apply Z.leb_le in D; [left|right]; exact D|].
split; [apply orb_true_iff in Hd12 as [D|D]; apply Z.leb_le in D; [left|right]; exact D|].
exact (wvw_ro_range_sound _ _ _ _ _ 4 Hro).
Qed.

(* ---- HPSTRO: no alloc.c static lies in the read-only band (S1ImgB.v pst_not_ro_B) ---- *)
Lemma wvw_hpstro : forall a, in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (@prh_pst prh_img_B).
Proof. intros a Hro Hx. exact (S1ImgB.pst_not_ro_B a Hx Hro). Qed.

(* ---- HLIT: the ten literals ---- *)
(* the image's zero-shadow ranges are whole granules (PvB_Inst.v pvI_zs_al) *)
Lemma wvw_zs_al : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow TB).
Proof.
assert (H : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0))%bool (as_zero_shadow TB) = true)
  by (vm_compute; reflexivity).
apply Forall_forall. intros r Hr. rewrite forallb_forall in H. specialize (H r Hr).
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. split; [exact H1 | exact H2].
Qed.

(* the image's const-shadow cells are const cells of every layout (PvB_Inst.v pvI_const_incl) *)
Lemma wvw_const_incl : forall ly, incl YF0m.Tfib_const_shadow (as_const TB ly).
Proof.
intros ly. change (as_const TB ly) with (YF0m.Tfib_const ly). unfold YF0m.Tfib_const.
apply incl_appr, incl_appr, incl_refl.
Qed.

(* the instance's image bounds against page 0 and the low-memory end (closed) *)
Lemma wvw_lo4096 : 4096 <= @pa_lo _ B_prog_listing PI_prog_B.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma wvw_hi_low : @pa_hi _ B_prog_listing PI_prog_B <= kLowMemEnd.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* a literal byte: the byte facts of kept_img and ro_shadow_ok *)
Definition wvw_lit_byte_b (x : Z) : bool :=
  wvw_ro_byte_b SEGS RLO RHI TB x && wvw_rso_b (as_zero_shadow TB) YF0m.Tfib_const_shadow x.
(* one literal (slot k, bytes bs): the kept_img bounds, every byte, the ROM bytes and the shadow hull's cover *)
Definition wvw_lit_b (k : nat) (bs : list Z) : bool :=
  (@pa_lo _ B_prog_listing PI_prog_B + 64 <=? WriteValueB_Base.WV_STR (PA := PI_prog_B) k) &&
  (WriteValueB_Base.WV_STR (PA := PI_prog_B) k + Z.of_nat (length bs) + 64 <=? @pa_hi _ B_prog_listing PI_prog_B) &&
  YP08.zallb wvw_lit_byte_b (WriteValueB_Base.WV_STR (PA := PI_prog_B) k) (length bs) &&
  wvw_romb SEGS (WriteValueB_Base.WV_STR (PA := PI_prog_B) k) bs &&
  img_shadow_cover (as_zero_shadow TB) YF0m.Tfib_const_shadow
    (WriteValueB_Base.WV_STR (PA := PI_prog_B) k / 8 / 8 * 64)
    ((WriteValueB_Base.WV_STR (PA := PI_prog_B) k + Z.of_nat (length bs) - 1) / 8 / 8 * 64 + 64).

Lemma wvw_lits_all : forallb (fun e => wvw_lit_b (fst e) (snd e)) WriteValueB_Base.wv_lits = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wvw_lit_sound : forall k bs, wvw_lit_b k bs = true ->
  forall ly S Hp (W : world SEGS) mem md, ARcfx ly S Hp W mem md ->
  arodata_okP SEGS RLO RHI TB (aview SEGS (w_H W) mem) ->
  src_rd (PA := PI_prog_B) W mem (WriteValueB_Base.WV_STR (PA := PI_prog_B) k) bs /\
  kept_at (PA := PI_prog_B) TB [] (WriteValueB_Base.WV_STR (PA := PI_prog_B) k) (Z.of_nat (length bs)) /\
  (forall i, 0 <= i < Z.of_nat (length bs) -> in_img SEGS (WriteValueB_Base.WV_STR (PA := PI_prog_B) k + i)).
Proof.
intros k bs H ly S Hp W mem md HAR HRO. unfold wvw_lit_b in H.
set (p := WriteValueB_Base.WV_STR (PA := PI_prog_B) k) in *.
apply andb_prop in H as [H HCV]. apply andb_prop in H as [H HROM].
apply andb_prop in H as [H HBY]. apply andb_prop in H as [HLO HHI].
apply Z.leb_le in HLO. apply Z.leb_le in HHI.
assert (BY : forall i, 0 <= i < Z.of_nat (length bs) -> wvw_lit_byte_b (p + i) = true).
{ intros i Hi. apply (YP08.zallb_sound _ (length bs) p); [exact HBY | lia]. }
assert (KI : kept_img (PA := PI_prog_B) TB p (Z.of_nat (length bs))).
{ unfold kept_img. split; [exact HLO|]. split; [exact HHI|].
  intros a Ha. specialize (BY (a - p) ltac:(lia)). replace (p + (a - p)) with a in BY by ring.
  unfold wvw_lit_byte_b in BY. apply andb_prop in BY as [B1 B2].
  destruct (wvw_ro_byte_sound _ _ _ _ _ B1) as (_ & R2 & R3 & R4).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  exact (wvw_rso_sound TB _ _ a (incl_refl _) wvw_const_incl B2). }
destruct (wvw_lit_rd (PA := PI_prog_B) TB ARcfx _ wvw_laws (as_zero_shadow TB) YF0m.Tfib_const_shadow
  (p / 8 / 8 * 64) ((p + Z.of_nat (length bs) - 1) / 8 / 8 * 64 + 64) ly S Hp W mem md p bs
  wvw_lo4096 wvw_hi_low wvw_zs_al HCV (incl_refl _) wvw_const_incl (Z.le_refl _) (Z.le_refl _) HAR HRO KI
  (wvw_romb_sound _ _ _ HROM)) as [SR KA].
split; [exact SR|]. split; [exact KA|].
intros i Hi. specialize (BY i Hi). unfold wvw_lit_byte_b in BY. apply andb_prop in BY as [B1 _].
exact (proj1 (wvw_ro_byte_sound _ _ _ _ _ B1)).
Qed.

Lemma wvw_hlit : forall (k : nat) (bs : list Z) ly' S' Hp' (W' : world SEGS) m' md',
  In (k, bs) WriteValueB_Base.wv_lits ->
  ARcfx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS RLO RHI TB (aview SEGS (w_H W') m') ->
  src_rd (PA := PI_prog_B) W' m' (WriteValueB_Base.WV_STR (PA := PI_prog_B) k) bs /\
  kept_at (PA := PI_prog_B) TB [] (WriteValueB_Base.WV_STR (PA := PI_prog_B) k) (Z.of_nat (length bs)) /\
  (forall i, 0 <= i < Z.of_nat (length bs) -> in_img SEGS (WriteValueB_Base.WV_STR (PA := PI_prog_B) k + i)).
Proof.
intros k bs ly' S' Hp' W' m' md' Hin HAR HRO.
pose proof wvw_lits_all as A. rewrite forallb_forall in A.
exact (wvw_lit_sound k bs (A (k, bs) Hin) ly' S' Hp' W' m' md' HAR HRO).
Qed.

(* ---- STRLEN (Leaf): the PROVED strlen row of image B' (lib/AU/PSstrRo.v ps_strlen_xrom_xs_B) at TfibB, after the
   pc equation (the listing's __wrap_strlen is CfImgB's trampoline pc; closed) ---- *)
Lemma wvw_strlen_pc : SIGMA AS___wrap_strlen = @cf_pc_strlen CfImgB.CfImg_B.
Proof. apply Z.eqb_eq. vm_compute. reflexivity. Qed.

Lemma wvw_strlen : YGcallMxmn.astrlen_realizes_xrom SEGS TB ARcfx RLO RHI (SIGMA AS___wrap_strlen).
Proof.
rewrite wvw_strlen_pc.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSstrRo.ps_strlen_xrom_xs_B TB YD2l.TfibB_syms RLO RHI).
Qed.

(* ---- THE TYPE CHECKS: the witnesses are the walk's Section hypotheses at the instance, in their order ---- *)
Lemma wvw_fit_base : True.
Proof.
pose proof (fun (RL : PrhRoomLive) (SK : YI16.sink_head) =>
  @WriteValueB_Base.wv_disj_img fx rc CfImgB.CfImg_B CP RL SK PI_prog_B TB ARcfx wvw_laws wvw_tl wvw_hent wvw_hobj
    wvw_hjt wvw_hlit wvw_hpstro) as _.
exact I.
Qed.
Lemma wvw_fit_leaf : True.
Proof.
pose proof (fun (RL : PrhRoomLive) (SK : YI16.sink_head) CTX0 PUT PUTSTR INDENT =>
  @WriteValueB_Leaf.wv_leaf_num fx rc CfImgB.CfImg_B CP RL SK PI_prog_B TB ARcfx wvw_laws wvw_tl wvw_hent wvw_hobj
    wvw_hjt wvw_hlit wvw_hpstro CTX0 PUT PUTSTR INDENT wvw_hw wvw_strlen) as _.
exact I.
Qed.
End w.

(* each Locate names the lemma whose assumptions the next line prints *)
Locate wvw_laws. Print Assumptions wvw_laws.
Locate wvw_tl. Print Assumptions wvw_tl.
Locate wvw_hw. Print Assumptions wvw_hw.
Locate wvw_hent. Print Assumptions wvw_hent.
Locate wvw_hobj. Print Assumptions wvw_hobj.
Locate wvw_hjt. Print Assumptions wvw_hjt.
Locate wvw_hpstro. Print Assumptions wvw_hpstro.
Locate wvw_hlit. Print Assumptions wvw_hlit.
Locate wvw_strlen. Print Assumptions wvw_strlen.
Locate wvw_fit_base. Print Assumptions wvw_fit_base.
Locate wvw_fit_leaf. Print Assumptions wvw_fit_leaf.
