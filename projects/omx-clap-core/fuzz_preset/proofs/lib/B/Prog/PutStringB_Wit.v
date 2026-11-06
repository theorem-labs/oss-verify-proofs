(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d7f488d30, twin c90d4fa54d43160b), lane
   PutStringB (h-rw-pre-7): the INSTANCE WITNESSES of the image facts the put_string walk keeps as Section hypotheses
   (lib/B/Prog/PutStringB_Base.v / PutStringB_A.v Section h, PutStringB_T.v Section h and its release lemma's FPRX).
   rule 24: no function proved (kind: instance discharge of image facts only, for the put_string walk).
   THE INSTANCE (the internal file bprime-pivot.md item 6): PA := PAImg_prog.PI_prog_B, B := YD2l.TfibB, ci := CfImgB.CfImg_B,
   cp := CfParamsPreset.CfParams_preset, RL := PRH_Base.prh_room_live_a8, PI := prh_img_B, ARx := ARcfx =
   YG0ncf.ARcf SEGS TfibB /\ YG0ncf.xs_placed_cf (YGcallcf.v's ARxs). fx, rc, SK stay Section Context. Each psw_<hyp>
   states its hypothesis's TEXT at that instance (the walk's own definitions ps_objs_disj / ps_uar_ok / ps_lit_fact /
   AF_put_string / ARx_frame_hull_vis are cited, not restated); psw_fit_base applies six PutStringB_Base.v lemmas to
   them, so those texts are checked against the walk's Section hypotheses by the kernel.
   TEMPLATES (copied, not Required; reuse, not trust):
   - WT = lib/B/Prog/WriteValueB_Wit.v at origin/cold/h-rw-pre-7-bp-write_value 6639b1e8a3ca (blob 94d028301e5d):
     the generic checkers and the literal step (psw_zr_b .. psw_lit_rd, psw_lit_b / psw_lit_sound), LAWS, TL, HW,
     Hent, HPSTRO, the zero-shadow alignment, the const-shadow inclusion, the bound checks and the strlen row. The
     literal step is WT's wvw_lit_rd (itself PORTED from h-rw-pre-5's S7a_indent_wit.v s7w_lit_rd), with every lia
     scoped here.
   - PT = lib/B/Prog/PutB_Wit.v at origin/cold/h-rw-pre-7-bp-put 768d17e2fe20 (blob 29f078c91f7c): HIMGSH
     (pe_imgsh: YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover at YF0m.Tfib_zero_shadow / Tfib_const_shadow, the
     cover check at pa_lo / pa_hi), HFHULL (pe_frsh), the Hobj cover check (pe_obj).
   - ET = lib/B/Prog/ExvB_ImgFacts.v at origin/cold/h-rw-pre-7-bp-ex_value b767dd3b849 (blob 4d34335b252c): the
     disjointness checker (exvi_disj_b), Huar (exvi_eh_got_uar), HUARC's apartness (exvi_eh_uar_cell), PST_ok's
     owned part (exvi_eh_pst_own), OWNLOW (exvi_eh_ownlow, here at ARcfx), SMX / SFX (exvi_eh_smx / exvi_eh_sfx),
     ASFX / FFLX (here YGcallScf.v's ARcfx twins astack_free_x_xs / frame_flag_x_xs), FPRX (exvi_eh_fflx's apresent
     conjunct), Hsm0 (exvi_eh_sm1_pc at class 0), errno_low (PALibB.exvi_eh_errno).
   WHAT EACH WITNESS CITES: psw_laws YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf; psw_tl PALibB.exvi_eh_palib;
   psw_hent / psw_huar / psw_hsm0 / psw_hobjd / psw_hpab vm_compute on the closed listing and record; psw_hobj /
   psw_huarc S1ImgCheck.in_img_b cover checks (vm_compute) plus closed apartness booleans; psw_segs_low
   PAImg_prog.B_prog_segs_low; psw_errno_low PALibB.exvi_eh_errno; psw_ownlow YGcallcf.ARx_owned_low_law_xs;
   psw_smx / psw_sfx YGcallScf.stack_malloc_x_any / stack_free_x_any; psw_asfx / psw_fflx YGcallScf.astack_free_x_xs /
   frame_flag_x_xs; psw_fprx YG0scf.AR_flag_law_ok_cf (first conjunct); psw_hw PALibB.exvi_eh_head; psw_aso
   YD2l.TfibB_ok; psw_himgsh YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover with psw_imgsh_cover; psw_fhull
   YGcfFsVis.ARx_frame_hull_vis_cf_ok; psw_pst_ok S1ImgB.pst_in_img_B plus two closed disjointness checks;
   psw_hpstro S1ImgB.pst_not_ro_B; psw_hlit18 .. psw_hlit89 psw_hlit (one closed boolean psw_lit_b per literal: the
   kept_img bounds, per byte in_img / in_roP / not owned / not errno / ro_shadow_ok, the ROM bytes, the hull cover);
   psw_strlen lib/AU/PSstrRo.v ps_strlen_xrom_xs_B after the pc equation psw_strlen_pc.
   The literal bytes are the B' image's own: psw_lit_b compares the walk's byte list with YK11.seg_rom at ps_str k
   (put_string + 4 k is a PAddHi over A_OBJ 2), so a wrong list fails its vm_compute. MEASURED 2026-10-29 (a
   vm_compute of seg_rom at ps_str k, 8 bytes each, since removed; log zfb-20261029T200605Z): k = 65 and 183 (one
   literal, .str.18) read 34 then NUL, 85 reads 92 116 0, 87 reads 92 110 0, 89 reads 92 117 37 48 52 120 0, 91 reads
   92 114 0, 93 reads 92 37 99 0: the walk's six lists are the image's.
   Every vm_compute is on a closed goal. Numerals: 4 (LENGTH: errno, the uar cell), 8 (LENGTH: a word / a granule),
   64 (LENGTH: kept_img's margin, a shadow granule's span), 256 / 2 ^ 8 (byte range), 4096 (LENGTH: page 0); the
   listing offsets 65 .. 93 and the literal bytes are the walk's own; in the ported generic step only, 0x7fff8000 (the
   ASan shadow offset SHADOW_OFF, unfolded: a runtime constant) and 0xffff000 (= SHADOW_OFF / 8). No image ADDRESS is
   typed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* the walk's own import list (PutStringB_Base.v), so each hypothesis text below reads as the walk reads it *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomPre YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx YGcallx YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB.
(* the cover checker and the byte checkers: Required, cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgShadowCover YImgShadowCoverCf YP08.
(* the walk's files: Required, not Imported, to name their definitions (no Section of theirs is opened) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PutStringB_HShadow PutStringB_Base.
(* the instance and its proved facts: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0lawscf YGcallcf YG0scf YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfFsVis.
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

(* ======================= 1. generic checkers and their soundness (no image; WT section 1) ======================= *)

(* no range of a list holds a (WT wvw_zr_b / wvw_zr_b_sound) *)
Definition psw_zr_b (l : list (Z * Z)) (a : Z) : bool := existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l.
Lemma psw_zr_b_sound : forall l a, psw_zr_b l a = false -> ~ Exists (in_zr a) l.
Proof.
intros l a H HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
assert (E : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l = true).
{ apply existsb_exists. exists r. split; [exact Hr|].
  apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; clear - Hz; lia. }
unfold psw_zr_b in H. rewrite E in H. discriminate H.
Qed.

(* S1ImgCheck's in_ro_b (both arms of in_roP) is sound (WT wvw_in_ro_b_sound) *)
Lemma psw_in_ro_b_sound : forall segs rlo rhi a, S1ImgCheck.in_ro_b segs rlo rhi a = true -> in_roP segs rlo rhi a.
Proof.
intros segs rlo rhi a H. unfold S1ImgCheck.in_ro_b in H. apply orb_true_iff in H as [H|H].
- left. apply existsb_exists in H as (s & Hs & Hb). apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply negb_true_iff in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  exists s. split; [exact Hs|]. split; [exact H1|]. clear - H2 H3; lia.
- right. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. clear - H1 H2; lia.
Qed.

(* one byte: in the image, read-only, not a runtime-owned static, not errno (WT wvw_ro_byte_b / wvw_ro_byte_sound) *)
Definition psw_ro_byte_b (segs : list Segment) (rlo rhi : Z) (B : asyms) (x : Z) : bool :=
  S1ImgCheck.in_img_b segs x && S1ImgCheck.in_ro_b segs rlo rhi x && negb (psw_zr_b (as_owned_static B) x) &&
  negb ((as_errno B <=? x) && (x <? as_errno B + 4)).
Lemma psw_ro_byte_sound : forall segs rlo rhi B x, psw_ro_byte_b segs rlo rhi B x = true ->
  in_img segs x /\ in_roP segs rlo rhi x /\ ~ Exists (in_zr x) (as_owned_static B) /\
  ~ (as_errno B <= x < as_errno B + 4).
Proof.
intros segs rlo rhi B x H. unfold psw_ro_byte_b in H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
split; [exact (S1ImgCheck.in_img_b_sound _ _ H1)|].
split; [exact (psw_in_ro_b_sound _ _ _ _ H2)|].
split; [apply negb_true_iff in H3; exact (psw_zr_b_sound _ _ H3)|].
apply negb_true_iff in H4. intros [E1 E2].
apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite E1, E2 in H4. discriminate H4.
Qed.

(* the image bytes [a, a + n) from one zallb check (WT wvw_img_range_sound) *)
Lemma psw_img_range_sound : forall segs a n, YP08.zallb (S1ImgCheck.in_img_b segs) a n = true ->
  forall i, 0 <= i < Z.of_nat n -> in_img segs (a + i).
Proof.
intros segs a n H i Hi. apply S1ImgCheck.in_img_b_sound. apply (YP08.zallb_sound _ n a); [exact H | clear - Hi; lia].
Qed.

(* the rom bytes at [p, p + length l) are l (WT wvw_romb / wvw_romb_sound) *)
Fixpoint psw_romb (segs : list Segment) (p : Z) (l : list Z) : bool :=
  match l with
  | [] => true
  | b :: t => match YK11.seg_rom segs (Z_to_bv 64 p) with
              | Some x => (bv_unsigned x =? b) && psw_romb segs (p + 1) t
              | None => false
              end
  end.
Lemma psw_romb_sound : forall segs l p, psw_romb segs p l = true -> forall j, (j < length l)%nat ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 (p + Z.of_nat j))) = Some (nth j l 0).
Proof.
intros segs l. induction l as [|b t IH]; intros p H j Hj; cbn [length] in Hj; [clear - Hj; lia|].
cbn [psw_romb] in H. destruct (YK11.seg_rom segs (Z_to_bv 64 p)) as [x|] eqn:E; [|discriminate].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
destruct j as [|j].
- cbn [nth Z.of_nat]. rewrite Z.add_0_r, E. cbn [option_map]. rewrite H1. reflexivity.
- cbn [nth]. replace (p + Z.of_nat (S j)) with (p + 1 + Z.of_nat j) by (clear - p j; lia).
  apply IH; [exact H2 | clear - Hj; lia].
Qed.

(* a one-byte const cell at sa whose value passes P (WT wvw_z1_match / wvw_z1_match_sound) *)
Definition psw_z1_match (sa : Z) (P : Z -> bool) (c : acell) : bool :=
  match c with
  | ACell (ANum x) w (AV (ANum v)) => Nat.eqb w 1 && Z.eqb x sa && P v
  | _ => false
  end.
Lemma psw_z1_match_sound : forall sa P c, psw_z1_match sa P c = true -> exists v, c = z1 (ANum sa) v /\ P v = true.
Proof.
intros sa P [ca cw cv] H. unfold psw_z1_match in H.
destruct ca; cbn in H; try discriminate H.
destruct cv as [e|mask v0]; cbn in H; try discriminate H.
destruct e; cbn in H; try discriminate H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. subst. eexists. split; [reflexivity | exact H3].
Qed.

(* ro_shadow_ok (PRH_Base.v) as a boolean: a whole zero-shadow granule, or a const-shadow cell whose value admits the
   byte (WT wvw_vok / wvw_rso_b / wvw_rso_sound) *)
Definition psw_vok (x v : Z) : bool := (v =? 0) || ((x mod 8 <? v) && (v <? 8)).
Definition psw_rso_b (zs : list (Z * Z)) (cs : list acell) (x : Z) : bool :=
  existsb (fun r => (fst r <=? x - x mod 8) && (x - x mod 8 + 8 <=? fst r + snd r)) zs ||
  existsb (psw_z1_match (shadow_addr x) (psw_vok x)) cs.
Lemma psw_rso_sound : forall (B : asyms) zs cs x,
  incl zs (as_zero_shadow B) -> (forall ly, incl cs (as_const B ly)) -> psw_rso_b zs cs x = true ->
  ro_shadow_ok B x.
Proof.
intros B zs cs x Iz Ic H. unfold ro_shadow_ok, in_zs. unfold psw_rso_b in H. apply orb_true_iff in H as [H|H].
- left. apply existsb_exists in H as ([q m] & Hin & Hb). apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2.
  exists q, m. split; [exact (Iz _ Hin)|]. clear - H1 H2; lia.
- right. apply existsb_exists in H as (c & Hin & Hb).
  destruct (psw_z1_match_sound _ _ _ Hb) as (v & -> & Hv).
  exists v. split; [intros ly; exact (Ic ly _ Hin)|].
  unfold psw_vok in Hv. apply orb_true_iff in Hv as [Hv|Hv]; [left; apply Z.eqb_eq; exact Hv|].
  right. apply andb_prop in Hv as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. clear - H1 H2; lia.
Qed.

(* two range lists are apart (ET exvi_disj_b / exvi_disj_b_sound) *)
Definition psw_disj_b (l1 l2 : list (Z * Z)) : bool :=
  forallb (fun r => forallb (fun r' => (fst r + snd r <=? fst r') || (fst r' + snd r' <=? fst r))%bool l2) l1.
Lemma psw_disj_b_sound : forall l1 l2, psw_disj_b l1 l2 = true ->
  forall a, Exists (in_zr a) l1 -> ~ Exists (in_zr a) l2.
Proof.
intros l1 l2 H a H1 H2. apply Exists_exists in H1 as (r & Hr & Ar). apply Exists_exists in H2 as (r' & Hr' & Ar').
unfold psw_disj_b in H. rewrite forallb_forall in H. specialize (H r Hr). rewrite forallb_forall in H.
specialize (H r' Hr'). apply Bool.orb_true_iff in H. unfold in_zr in Ar, Ar'.
destruct H as [H|H]; apply Z.leb_le in H; clear - Ar Ar' H; lia.
Qed.

(* ======================= 2. THE GENERIC LITERAL STEP (any B, any ARx with AR_laws_x, any PAImg; WT section 2:
   wvw_val1_of_aview / wvw_lit_rd, the lia calls scoped) ======================= *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation segs := (@pa_segs rc L PA).

Lemma psw_val1_of_aview : forall (H : word -> bool) mem a v, aview segs H mem a = Some v ->
  val_mem segs (mrestrict H mem) a 1 v /\ 0 <= v < 256.
Proof.
intros H mem a v E. unfold aview in E.
destruct (mbyte segs (mrestrict H mem) a) as [bb|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as <-. pose proof (bv_unsigned_in_range 8 bb) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|exact Hr].
intros k Hk. assert (k = 0%nat) by (clear - Hk; lia). subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb.
f_equal. rewrite YI04.le_byte_small by (cbn; clear - Hr; lia).
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by exact Hr. reflexivity.
Qed.

Lemma psw_lit_rd : forall (B : asyms)
    (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop) (HL : Z),
  AR_laws_x segs B ARx HL ->
  forall (zs : list (Z * Z)) (cs : list acell) (Lo Hi : Z) ly S Hp (W : world segs) mem md s src,
  4096 <= @pa_lo rc L PA -> @pa_hi rc L PA <= kLowMemEnd ->
  Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B) ->
  YImgShadowCover.img_shadow_cover zs cs Lo Hi = true -> incl zs (as_zero_shadow B) ->
  (forall ly, incl cs (as_const B ly)) ->
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
split; [|split; [clear - PLO Hlo; lia|split; [clear - Hhi PHI C1 C5; lia|
  split; [unfold amem_range; left; clear - Hhi PHI; lia|split]]]].
- (* the bytes: read-only, so the image's (arodata_okP) *)
  unfold bytes_at. intros j Hj.
  destruct (Hro (s + Z.of_nat j) ltac:(clear - Hj; lia)) as (Hr & Hno & Her & _).
  pose proof (HRO _ Hr Hno Her) as E. rewrite (Hrom j Hj) in E.
  exact (psw_val1_of_aview (w_H W) mem _ _ E).
- (* each byte's shadow: a zero-shadow granule (alx_zshadow) or a const-shadow cell (alx_const_cells) *)
  intros x Hx. pose proof (Z.mod_pos_bound x 8 ltac:(clear - x; lia)) as Hxm.
  destruct (Hro x Hx) as (_ & _ & _ & [Hzs | (v & Hcl & Hv)]).
  + destruct Hzs as (q & m & Hin & Hq & Hqm).
    pose proof (proj1 (Forall_forall _ _) ZA (q, m) Hin) as (Hq8 & Hm8). cbn [fst snd] in Hq8, Hm8.
    pose proof (alx_zshadow _ _ _ LAWS ly S Hp W mem md (q, m) HAR ltac:(right; exact Hin)) as Hz.
    cbn [fst snd] in Hz.
    exact (zero_shadow_range (aview segs (w_H W) mem) SHADOW_OFF q m Hq8 Hm8 Hz x ltac:(clear - Hq Hqm Hxm; lia)).
  + pose proof (proj1 (Forall_forall _ _) (alx_const_cells _ _ _ LAWS ly S Hp W mem md HAR) _ (Hcl ly)) as Hcell.
    unfold cell_holds, z1, c1 in Hcell. cbn [c_at c_w c_val aeval] in Hcell.
    specialize (Hcell 0%nat (Nat.lt_0_succ 0)). rewrite Z.add_0_r in Hcell.
    exists v. split; [|unfold saddr_ok; clear - Hv; lia].
    unfold shadow_of_addr. unfold shadow_addr in Hcell. rewrite Hcell. f_equal.
    unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r, (Z.mod_small v (2 ^ 8)) by (clear - Hv Hxm; lia).
    apply Z.mod_small. clear - Hv Hxm; lia.
- (* the shadow hull: each byte is the shadow of a granule in [Lo, Hi), covered by the lists *)
  intros _ sh Hsh. set (n := Z.of_nat (length src)) in *.
  unfold shadow_addr, SHADOW_OFF in Hsh.
  replace (0x7fff8000 + s / 8) with (s / 8 + 0xffff000 * 8) in Hsh by (clear - s; lia).
  replace (0x7fff8000 + (s + n - 1) / 8) with ((s + n - 1) / 8 + 0xffff000 * 8) in Hsh by (clear - s n; lia).
  rewrite !Z.div_add in Hsh by discriminate.
  assert (E : shadow_addr (8 * (sh - SHADOW_OFF)) = sh)
    by (unfold shadow_addr; rewrite Z.mul_comm, Z.div_mul by discriminate; clear - sh; lia).
  rewrite <- E.
  apply (YImgShadowCover.img_shadow_cover_sound (aview segs (w_H W) mem) zs cs Lo Hi Hc).
  + intros r Hr. exact (alx_zshadow _ _ _ LAWS ly S Hp W mem md r HAR ltac:(right; exact (Iz r Hr))).
  + intros x Hx. unfold YImgShadowCover.shv_cell_bytes in Hx. apply in_flat_map in Hx as (c & Hc' & Hx).
    exact (YImgShadowCover.shv_acell_bytes_vis B ly _ c x
      (proj1 (Forall_forall _ _) (alx_const_cells _ _ _ LAWS ly S Hp W mem md HAR) c (Ic ly c Hc')) Hx).
  + unfold SHADOW_OFF. clear - Hsh HLo HHi; lia.
Qed.
End g.

(* ======================= 3. THE WITNESSES at the instance ======================= *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {ci : CfImg}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance PRH_Base.prh_room_live_a8.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PI_prog_B).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
#[local] Abbreviation RLO := (@pa_relro_lo _ B_prog_listing PI_prog_B).
#[local] Abbreviation RHI := (@pa_relro_hi _ B_prog_listing PI_prog_B).
#[local] Abbreviation PLO := (@pa_lo _ B_prog_listing PI_prog_B).
#[local] Abbreviation PHI := (@pa_hi _ B_prog_listing PI_prog_B).
(* the allocator relation of the walk at the instance (FuzzFreeB.v:296's ARcfx; YGcallcf.v's ARxs) *)
#[local] Abbreviation ARcfx := (fun ly S Hp (W : world SEGS) mem md =>
  YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

(* ---- LAWS / TL / HW / ASO: citations ---- *)
Lemma psw_laws : AR_laws_x SEGS TB ARcfx (@cf_head CP).
Proof. exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)). Qed.

Lemma psw_tl : PALib (PI := PI_prog_B) TB.
Proof. exact PALibB.exvi_eh_palib. Qed.

Lemma psw_hw : @prh_head_wide CP.
Proof. exact PALibB.exvi_eh_head. Qed.

Lemma psw_aso : asyms_ok TB.
Proof. exact YD2l.TfibB_ok. Qed.

(* ---- Hent / Huar / Hsm0: closed equations on the listing and the record ---- *)
Lemma psw_hent : SIGMA AS_put_string = BASE + PutStringB_Base.AF_put_string.
Proof. apply Z.eqb_eq. vm_compute. reflexivity. Qed.

Lemma psw_huar : as_got_uar TB = VAL (A_OBJ 1).
Proof. apply Z.eqb_eq. vm_compute. reflexivity. Qed.

Lemma psw_hsm0 : pc_stack_malloc (as_code TB) 0 = SIGMA AS___asan_stack_malloc_0.
Proof. apply Z.eqb_eq. vm_compute. reflexivity. Qed.

(* ---- Hobj / HOBJ / HUARC: the three 8-byte objects and the uar cell, image bytes and apart ---- *)
Lemma psw_hobj : forall i, 0 <= i < 8 ->
  in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i) /\ in_img SEGS (VAL (A_OBJ 1) + i).
Proof.
assert (C : S1ImgCheck.pst_allb (S1ImgCheck.in_img_b SEGS) [(VAL (A_OBJ 0), 8); (VAL (A_OBJ 12), 8); (VAL (A_OBJ 1), 8)]
  = true) by (vm_compute; reflexivity).
intros i Hi. split; [|split]; apply S1ImgCheck.in_img_b_sound; apply (S1ImgCheck.pst_allb_sound _ _ _ C).
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. clear - Hi; lia.
- apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. clear - Hi; lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. clear - Hi; lia.
Qed.

Lemma psw_hobjd : PutStringB_Base.ps_objs_disj (PA := PI_prog_B).
Proof.
assert (D : forall a b : Z, (a + 8 <=? b) || (b + 8 <=? a) = true -> a + 8 <= b \/ b + 8 <= a)
  by (intros a b Hab; apply Bool.orb_true_iff in Hab as [Hab|Hab]; [left|right]; apply Z.leb_le; exact Hab).
unfold PutStringB_Base.ps_objs_disj. split; apply D; vm_compute; reflexivity.
Qed.

Lemma psw_huarc : PutStringB_Base.ps_uar_ok (PA := PI_prog_B) TB.
Proof.
assert (I4 : YP08.zallb (S1ImgCheck.in_img_b SEGS) (as_uar_cell TB) 4 = true) by (vm_compute; reflexivity).
assert (D : forall a b : Z, (a + 4 <=? b) || (b + 8 <=? a) = true -> a + 4 <= b \/ b + 8 <= a)
  by (intros a b Hab; apply Bool.orb_true_iff in Hab as [Hab|Hab]; [left|right]; apply Z.leb_le; exact Hab).
unfold PutStringB_Base.ps_uar_ok. split; [|split; [|split]].
- intros i Hi. exact (psw_img_range_sound _ _ 4 I4 i Hi).
- apply D. vm_compute. reflexivity.
- apply D. vm_compute. reflexivity.
- apply D. vm_compute. reflexivity.
Qed.

(* ---- segs_low / errno_low / HPAB: the image's bounds ---- *)
Lemma psw_segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd.
Proof. exact B_prog_segs_low. Qed.

Lemma psw_errno_low : api_env SEGS TB.
Proof. exact PALibB.exvi_eh_errno. Qed.

Lemma psw_hpab : 4096 <= PLO /\ PHI <= kLowShadowBeg.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* ---- OWNLOW / SMX: the frame-area laws at ARcfx ---- *)
Lemma psw_ownlow : ARx_owned_low_law SEGS TB ARcfx.
Proof. exact (YGcallcf.ARx_owned_low_law_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)). Qed.

Lemma psw_smx : forall ly S Hp W mem md cid, ARcfx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
Proof. exact (YGcallScf.stack_malloc_x_any SEGS ARcfx). Qed.

(* ---- HIMGSH / HFHULL: the image's shadow over pa_lo / pa_hi and the live frames' hulls ---- *)
Lemma psw_const_incl : forall ly, incl YF0m.Tfib_const_shadow (as_const TB ly).
Proof.
intros ly. change (as_const TB ly) with (YF0m.Tfib_const ly). unfold YF0m.Tfib_const.
apply incl_appr, incl_appr, incl_refl.
Qed.

Lemma psw_imgsh_cover : YImgShadowCover.img_shadow_cover YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow PLO PHI = true.
Proof. vm_compute. reflexivity. Qed.

Lemma psw_himgsh : forall ly S Hp (W : world SEGS) mem md a, ARcfx ly S Hp W mem md ->
  @pa_lo _ B_prog_listing PI_prog_B <= a < @pa_hi _ B_prog_listing PI_prog_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof.
intros ly S Hp W mem md a [HA _] Ha.
refine (YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover SEGS TB YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow
  PLO PHI psw_imgsh_cover _ psw_const_incl ly S Hp W mem md a HA Ha).
exact (incl_refl YF0m.Tfib_zero_shadow).
Qed.

Lemma psw_fhull : PutStringB_HShadow.ARx_frame_hull_vis SEGS ARcfx.
Proof.
intros ly S Hp W mem md cid pos [HA _] Hin.
exact (YGcfFsVis.ARx_frame_hull_vis_cf_ok SEGS TB (YG0lawscf.AR_laws_ok_cf SEGS TB) ly S Hp W mem md cid pos HA Hin).
Qed.

(* ---- PST_ok / HPSTRO: alloc.c's five statics ---- *)
Lemma psw_pst_ok : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static TB) /\ ~ (as_errno TB <= a < as_errno TB + 4).
Proof.
assert (D1 : psw_disj_b (@prh_pst prh_img_B) (as_owned_static TB) = true) by (vm_compute; reflexivity).
assert (D2 : psw_disj_b (@prh_pst prh_img_B) [(as_errno TB, 4)] = true) by (vm_compute; reflexivity).
intros a Ha. split; [exact (S1ImgB.pst_in_img_B a Ha)|]. split; [exact (psw_disj_b_sound _ _ D1 a Ha)|].
intros He. apply (psw_disj_b_sound _ _ D2 a Ha). apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact He.
Qed.

Lemma psw_hpstro : forall a, in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (@prh_pst prh_img_B).
Proof. intros a Hro Hx. exact (S1ImgB.pst_not_ro_B a Hx Hro). Qed.

(* ---- the six literals (HLIT18 / HLIT85 / HLIT87 / HLIT91 / HLIT93 / HLIT89) ---- *)
(* the image's zero-shadow ranges are whole granules (WT wvw_zs_al) *)
Lemma psw_zs_al : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow TB).
Proof.
assert (H : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0))%bool (as_zero_shadow TB) = true)
  by (vm_compute; reflexivity).
apply Forall_forall. intros r Hr. rewrite forallb_forall in H. specialize (H r Hr).
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. split; [exact H1 | exact H2].
Qed.

(* the instance's image bounds against page 0 and the low-memory end (closed; WT wvw_lo4096 / wvw_hi_low) *)
Lemma psw_lo4096 : 4096 <= PLO.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma psw_hi_low : PHI <= kLowMemEnd.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* a literal byte: the byte facts of kept_img and ro_shadow_ok *)
Definition psw_lit_byte_b (x : Z) : bool :=
  psw_ro_byte_b SEGS RLO RHI TB x && psw_rso_b (as_zero_shadow TB) YF0m.Tfib_const_shadow x.
(* one literal (listing offset k, bytes bs): the kept_img bounds, every byte, the ROM bytes and the shadow hull's cover
   (WT wvw_lit_b at the walk's ps_str) *)
Definition psw_lit_b (k : nat) (bs : list Z) : bool :=
  (PLO + 64 <=? PutStringB_Base.ps_str (PA := PI_prog_B) k) &&
  (PutStringB_Base.ps_str (PA := PI_prog_B) k + Z.of_nat (length bs) + 64 <=? PHI) &&
  YP08.zallb psw_lit_byte_b (PutStringB_Base.ps_str (PA := PI_prog_B) k) (length bs) &&
  psw_romb SEGS (PutStringB_Base.ps_str (PA := PI_prog_B) k) bs &&
  YImgShadowCover.img_shadow_cover (as_zero_shadow TB) YF0m.Tfib_const_shadow
    (PutStringB_Base.ps_str (PA := PI_prog_B) k / 8 / 8 * 64)
    ((PutStringB_Base.ps_str (PA := PI_prog_B) k + Z.of_nat (length bs) - 1) / 8 / 8 * 64 + 64).

Lemma psw_lit_sound : forall k bs, psw_lit_b k bs = true ->
  forall ly S Hp (W : world SEGS) mem md, ARcfx ly S Hp W mem md ->
  arodata_okP SEGS RLO RHI TB (aview SEGS (w_H W) mem) ->
  src_rd (PA := PI_prog_B) W mem (PutStringB_Base.ps_str (PA := PI_prog_B) k) bs /\
  kept_at (PA := PI_prog_B) TB [] (PutStringB_Base.ps_str (PA := PI_prog_B) k) (Z.of_nat (length bs)).
Proof.
intros k bs H ly S Hp W mem md HAR HRO. unfold psw_lit_b in H.
set (p := PutStringB_Base.ps_str (PA := PI_prog_B) k) in *.
apply andb_prop in H as [H HCV]. apply andb_prop in H as [H HROM].
apply andb_prop in H as [H HBY]. apply andb_prop in H as [HLO HHI].
apply Z.leb_le in HLO. apply Z.leb_le in HHI.
assert (BY : forall i, 0 <= i < Z.of_nat (length bs) -> psw_lit_byte_b (p + i) = true).
{ intros i Hi. apply (YP08.zallb_sound _ (length bs) p); [exact HBY | clear - Hi; lia]. }
assert (KI : kept_img (PA := PI_prog_B) TB p (Z.of_nat (length bs))).
{ unfold kept_img. split; [exact HLO|]. split; [exact HHI|].
  intros a Ha. specialize (BY (a - p) ltac:(clear - Ha; lia)). replace (p + (a - p)) with a in BY by ring.
  unfold psw_lit_byte_b in BY. apply andb_prop in BY as [B1 B2].
  destruct (psw_ro_byte_sound _ _ _ _ _ B1) as (_ & R2 & R3 & R4).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  exact (psw_rso_sound TB _ _ a (incl_refl _) psw_const_incl B2). }
exact (psw_lit_rd (PA := PI_prog_B) TB ARcfx _ psw_laws (as_zero_shadow TB) YF0m.Tfib_const_shadow
  (p / 8 / 8 * 64) ((p + Z.of_nat (length bs) - 1) / 8 / 8 * 64 + 64) ly S Hp W mem md p bs
  psw_lo4096 psw_hi_low psw_zs_al HCV (incl_refl _) psw_const_incl (Z.le_refl _) (Z.le_refl _) HAR HRO KI
  (psw_romb_sound _ _ _ HROM)).
Qed.

(* one closed check gives the walk's ps_lit_fact at the instance *)
Lemma psw_hlit : forall k bs, psw_lit_b k bs = true -> PutStringB_Base.ps_lit_fact (PA := PI_prog_B) TB ARcfx k bs.
Proof.
intros k bs H ly' S' Hp' W' m' md' HAR HRO. exact (psw_lit_sound k bs H ly' S' Hp' W' m' md' HAR HRO).
Qed.

(* .str.18, the double quote (put_string + 4 * 65 and + 4 * 183) *)
Lemma psw_hlit18 : PutStringB_Base.ps_lit_fact (PA := PI_prog_B) TB ARcfx 65 [34].
Proof. apply psw_hlit. vm_compute. reflexivity. Qed.
(* .str.21 "\\t" *)
Lemma psw_hlit85 : PutStringB_Base.ps_lit_fact (PA := PI_prog_B) TB ARcfx 85 [92; 116; 0].
Proof. apply psw_hlit. vm_compute. reflexivity. Qed.
(* .str.20 "\\n" *)
Lemma psw_hlit87 : PutStringB_Base.ps_lit_fact (PA := PI_prog_B) TB ARcfx 87 [92; 110; 0].
Proof. apply psw_hlit. vm_compute. reflexivity. Qed.
(* .str.22 "\\r" *)
Lemma psw_hlit91 : PutStringB_Base.ps_lit_fact (PA := PI_prog_B) TB ARcfx 91 [92; 114; 0].
Proof. apply psw_hlit. vm_compute. reflexivity. Qed.
(* .str.19 "\\%c" *)
Lemma psw_hlit93 : PutStringB_Base.ps_lit_fact (PA := PI_prog_B) TB ARcfx 93 [92; 37; 99; 0].
Proof. apply psw_hlit. vm_compute. reflexivity. Qed.
(* .str.23 "\\u%04x" *)
Lemma psw_hlit89 : PutStringB_Base.ps_lit_fact (PA := PI_prog_B) TB ARcfx 89 [92; 117; 37; 48; 52; 120; 0].
Proof. apply psw_hlit. vm_compute. reflexivity. Qed.

(* ---- the tail's frame laws (PutStringB_T.v Section h's ASFX / FFLX / SFX, verbatim at ARcfx) and the release
   lemma pst_tail_end's FPRX ---- *)
Lemma psw_asfx : forall ly S Hp (W : world SEGS) mem md mem' md' cid pos,
  ARcfx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned TB ly S a -> a <> flag_addr ly cid pos ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARcfx ly (stack_free_state cid pos S) Hp W mem' md'.
Proof. exact (YGcallScf.astack_free_x_xs (cp := CP) SEGS TB). Qed.

Lemma psw_fflx : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARcfx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned TB ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Proof. exact (YGcallScf.frame_flag_x_xs (cp := CP) SEGS TB). Qed.

Lemma psw_sfx : forall ly S Hp (W : world SEGS) mem md cid pos, ARcfx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Proof. exact (YGcallScf.stack_free_x_any SEGS ARcfx). Qed.

Lemma psw_fprx : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARcfx ly S Hp W mem md -> In (cid, pos) (frames S) -> apresent (w_H W) mem (flag_addr ly cid pos).
Proof.
intros ly S Hp W mem md cid pos [HA _] Hin.
exact (proj1 (YG0scf.AR_flag_law_ok_cf (cp := CP) SEGS TB ly S Hp W mem md cid pos HA Hin)).
Qed.

(* ---- the strlen row: the PROVED row of image B' (lib/AU/PSstrRo.v ps_strlen_xrom_xs_B) at TfibB, after the pc
   equation (the listing's __wrap_strlen is CfImgB's trampoline pc; closed) ---- *)
Lemma psw_strlen_pc : SIGMA AS___wrap_strlen = @cf_pc_strlen CfImgB.CfImg_B.
Proof. apply Z.eqb_eq. vm_compute. reflexivity. Qed.

Lemma psw_strlen : YGcallMxmn.astrlen_realizes_xrom SEGS TB ARcfx RLO RHI (SIGMA AS___wrap_strlen).
Proof.
rewrite psw_strlen_pc.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSstrRo.ps_strlen_xrom_xs_B TB YD2l.TfibB_syms RLO RHI).
Qed.

(* ---- THE TYPE CHECKS: the witnesses are the walk's Section hypotheses at the instance, applied to the lemmas of
   PutStringB_Base.v (the one walk file that builds) that take them; A's / T's lemmas take the same texts (their
   Section headers are Base's, plus HLIT85 .. HLIT89 and T's ASFX / FFLX / SFX / FPRX in the forms above) ---- *)
Lemma psw_fit_base : True.
Proof.
pose proof (PutStringB_Base.ps_entry TB ARcfx psw_laws psw_tl psw_huar psw_hobj psw_hobjd psw_huarc) as _.
pose proof (PutStringB_Base.kept_at_bounds TB ARcfx psw_laws psw_hpab) as _.
pose proof (PutStringB_Base.cstr_from_entry TB ARcfx psw_hpstro) as _.
pose proof (PutStringB_Base.str_shadow_at TB ARcfx psw_laws psw_aso psw_himgsh psw_hpab) as _.
pose proof (fun Pm PCALL CTX0 PUT =>
  PutStringB_Base.ps_put_step TB ARcfx psw_laws psw_segs_low psw_hpab psw_hpstro Pm PCALL CTX0 PUT) as _.
pose proof (fun Pm CTX0 =>
  PutStringB_Base.ps_common_frame TB ARcfx psw_laws psw_segs_low psw_hw psw_pst_ok Pm CTX0) as _.
exact I.
Qed.
End w.

(* each Locate names the lemma whose assumptions the next line prints *)
Locate psw_laws. Print Assumptions psw_laws.
Locate psw_tl. Print Assumptions psw_tl.
Locate psw_hent. Print Assumptions psw_hent.
Locate psw_huar. Print Assumptions psw_huar.
Locate psw_hobj. Print Assumptions psw_hobj.
Locate psw_hobjd. Print Assumptions psw_hobjd.
Locate psw_huarc. Print Assumptions psw_huarc.
Locate psw_segs_low. Print Assumptions psw_segs_low.
Locate psw_errno_low. Print Assumptions psw_errno_low.
Locate psw_ownlow. Print Assumptions psw_ownlow.
Locate psw_smx. Print Assumptions psw_smx.
Locate psw_hsm0. Print Assumptions psw_hsm0.
Locate psw_hw. Print Assumptions psw_hw.
Locate psw_aso. Print Assumptions psw_aso.
Locate psw_himgsh. Print Assumptions psw_himgsh.
Locate psw_fhull. Print Assumptions psw_fhull.
Locate psw_hpab. Print Assumptions psw_hpab.
Locate psw_pst_ok. Print Assumptions psw_pst_ok.
Locate psw_hpstro. Print Assumptions psw_hpstro.
Locate psw_hlit18. Print Assumptions psw_hlit18.
Locate psw_hlit85. Print Assumptions psw_hlit85.
Locate psw_hlit87. Print Assumptions psw_hlit87.
Locate psw_hlit91. Print Assumptions psw_hlit91.
Locate psw_hlit93. Print Assumptions psw_hlit93.
Locate psw_hlit89. Print Assumptions psw_hlit89.
Locate psw_asfx. Print Assumptions psw_asfx.
Locate psw_fflx. Print Assumptions psw_fflx.
Locate psw_sfx. Print Assumptions psw_sfx.
Locate psw_fprx. Print Assumptions psw_fprx.
Locate psw_strlen. Print Assumptions psw_strlen.
Locate psw_fit_base. Print Assumptions psw_fit_base.
