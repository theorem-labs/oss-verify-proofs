(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102 pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa54d43160b): THE VACUITY
   GUARD of the walk of LLVMFuzzerTestOneInput, the twin of lib/A/Ent102InstA.v for the record of image facts ec_img
   (lib/AU/Ent102CutsB.v blob efe110ab522f, section 5). The fields that differ from A' are ei_own (displacement
   +0x590 from B_prog_hi 4) and ei_empty's YImgTop half (IMG_LO_B / IMG_TOP_B).
   rule 24: proves no function (kind: instance lemma of image facts).

   THE B' IMAGE TOP. Its import lib/B/PAImg_prog.v needs the #102 B' top IMG_TOP_B = 0x601000: lib/Reusable/YImgTop.v
   blob d2a97d3111ce of record (a Theorem Labs lane, a working branch a9548e31002a; on the old pins' blob
   cead467be393 PAImg_prog.v:160 fails). ei_empty is proved in both of its halves: against YImgTop's B' names IMG_LO_B /
   IMG_TOP_B and against PI_prog_B's own pa_lo / pa_hi (the same numbers, 0x10000 / 0x601000). The kit's kept_img
   (PRH_Base.v blob 3004a98fe2d9 :1020-1023, used by ei_lits) is bounded by pa_lo / pa_hi, so by B''s too.

   THE INSTANCE. L := B_prog_listing (lib/B/Listing_prog.v blob c97cc46b3e13, a Theorem Labs lane's listings v3 74dcda1eda12;
   the tables of the earlier blob 8bcc2c9e7809, the slot tree pre-evaluated); PA := PI_prog_B (lib/B/PAImg_prog.v
   blob 15fab93fe702); PI := prh_img_B (lib/B/PRH_ImgB.v blob 3216eca68342, the kit Batch 1);
   cp := CfParams_preset (lib/A/CfParamsPreset.v blob 1333a52cd63a); fx and rc stay section variables. The image
   values that no generated file on this branch names are typed constants, each with its source on its line
   (section 1).

   STATUS. ec_img IS CLOSED at the concrete instance (Theorem ec_img_B, section 4, B := YD2l.TfibB, the #102 B'
   runtime symbol record of a Theorem Labs lane, lib/Reusable/YD2l.v blob 95803a8b9493). Section 2 closes the fields that do not
   read the record, section 3 reduces ec_img to the six facts that read it, section 4 proves those six at TfibB by
   computation (ei_sm1, ei_pal, the static-free halves of ei_sio and ei_pst - owned statics AND errno - and the record
   half of ei_lits). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YG0ncf YG0dcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import Ent102CutsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
(* the #102 B' runtime symbol record and its tables, used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0l YF0m YCej YD2l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0. Decision procedures for the finite facts (each with its soundness lemma; generic in the segment list). *)
Lemma pst_all_of_b (P : Z -> Prop) (f : Z -> Z -> bool)
  (Hf : forall lo n a, f lo n = true -> lo <= a < lo + n -> P a) :
  forall l, forallb (fun r => f (fst r) (snd r)) l = true -> forall a, Exists (in_zr a) l -> P a.
Proof.
intros l Hl a HE. apply Exists_exists in HE as (r & Hr & Ha).
exact (Hf (fst r) (snd r) a (proj1 (forallb_forall _ _) Hl r Hr) Ha).
Qed.

(* [lo, lo + n) lies in one loaded segment *)
Definition iv_img_b (segs : list Segment) (lo n : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (lo + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool segs.
Lemma iv_img_sound : forall segs lo n a, iv_img_b segs lo n = true -> lo <= a < lo + n -> in_img segs a.
Proof.
intros segs lo n a H Ha. apply existsb_exists in H as (s & Hs & X).
apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2.
unfold in_img. exists s. split; [exact Hs | lia].
Qed.

(* [lo, lo + n) meets no non-writable segment and not the relro range *)
Definition iv_off_ro (segs : list Segment) (rlo rhi lo n : Z) : bool :=
  (forallb (fun s => seg_writable s || (lo + n <=? Z.of_N (seg_base s)) ||
                     (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? lo)) segs &&
   ((lo + n <=? rlo) || (rhi <=? lo)))%bool.
Lemma iv_off_ro_sound : forall segs rlo rhi lo n a,
  iv_off_ro segs rlo rhi lo n = true -> lo <= a < lo + n -> ~ in_roP segs rlo rhi a.
Proof.
intros segs rlo rhi lo n a H Ha. unfold iv_off_ro in H. apply andb_prop in H as [Hs Hr].
unfold in_roP. intros [(s & Hin & Hw & Hsa) | Hra].
- pose proof (proj1 (forallb_forall _ _) Hs s Hin) as X. cbv beta in X. rewrite Hw in X. cbn [orb] in X.
  apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
- apply orb_prop in Hr as [X|X]; apply Z.leb_le in X; lia.
Qed.

(* [lo, lo + n) lies in one non-writable segment *)
Definition iv_ro_b (segs : list Segment) (lo n : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? lo) &&
                    (lo + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool segs.
Lemma iv_ro_sound : forall segs rlo rhi lo n a, iv_ro_b segs lo n = true -> lo <= a < lo + n -> in_roP segs rlo rhi a.
Proof.
intros segs rlo rhi lo n a H Ha. apply existsb_exists in H as (s & Hs & X).
apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
apply negb_true_iff in X1. apply Z.leb_le in X2. apply Z.leb_le in X3.
unfold in_roP. left. exists s. split; [exact Hs | split; [exact X1 | lia]].
Qed.

(* [lo, lo + n) meets no interval of l *)
Definition iv_off_pst (l : list (Z * Z)) (lo n : Z) : bool :=
  forallb (fun r => (lo + n <=? fst r) || (fst r + snd r <=? lo))%bool l.
Lemma iv_off_pst_sound : forall l lo n a, iv_off_pst l lo n = true -> lo <= a < lo + n -> ~ Exists (in_zr a) l.
Proof.
intros l lo n a H Ha HE. apply Exists_exists in HE as (r & Hr & Hra).
pose proof (proj1 (forallb_forall _ _) H r Hr) as X. cbv beta in X. unfold in_zr in Hra.
apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
Qed.

(* every byte of [lo, lo + n) is a writable byte at the empty overlay *)
Definition iv_w_b (segs : list Segment) (lo n : Z) : bool :=
  forallb (fun k => match wview segs (fun _ => None) (Z_to_bv 64 (lo + Z.of_nat k)) with
                    | Some _ => true | None => false end) (seq 0 (Z.to_nat n)).
Lemma iv_w_sound : forall segs lo n a, iv_w_b segs lo n = true -> lo <= a < lo + n -> writable_at segs (fun _ => None) a.
Proof.
intros segs lo n a H Ha. unfold iv_w_b in H.
assert (Hk : In (Z.to_nat (a - lo)) (seq 0 (Z.to_nat n))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) H _ Hk) as X. cbv beta in X.
rewrite Z2Nat.id in X by lia. replace (lo + (a - lo)) with a in X by lia.
unfold writable_at. intros HN. rewrite HN in X. discriminate X.
Qed.

Fixpoint pairwise_b {X : Type} (f : X -> X -> bool) (l : list X) : bool :=
  match l with [] => true | x :: t => (forallb (f x) t && pairwise_b f t)%bool end.
Lemma pairwise_of_b {X : Type} (R : X -> X -> Prop) (f : X -> X -> bool)
  (Hf : forall x y, f x y = true -> R x y) : forall l, pairwise_b f l = true -> pairwise R l.
Proof.
induction l as [|x t IH]; intros H; [exact I|].
cbn [pairwise_b] in H. apply andb_prop in H as [H1 H2]. cbn [pairwise]. split.
- apply Forall_forall. intros y Hy. exact (Hf x y (proj1 (forallb_forall _ _) H1 y Hy)).
- exact (IH H2).
Qed.
Definition zdisjoint_b (u v : Z * Z) : bool := ((fst u + snd u <=? fst v) || (fst v + snd v <=? fst u))%bool.
Lemma zdisjoint_of_b : forall u v, zdisjoint_b u v = true -> zdisjoint u v.
Proof.
intros u v H. unfold zdisjoint_b in H. unfold zdisjoint.
apply orb_prop in H as [H|H]; apply Z.leb_le in H; [left|right]; exact H.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1. The image values of the instance that have no generated name on this branch. *)
(* the empty payload: symbol oft_aligned_copy.empty of twin c90d4fa5; = lib/AU/PresetCfnB.v:195 A_EMPTY (blob
   773e6d0f6c59, MEASURED) *)
Definition ia_empty : Z := 0x5ddd60.
(* check_round_trip's two literals: lib/A/Prog/Crt102Img.v CRT_MOD_AT_B / CRT_STAMP_B (a working branch
   fbb5bc52bdb, blob 10b5850baf33, :1024-1025) = VAL (A_OBJ 2) + the listing's PAddHi payloads 0x110c0 / 0x11380 *)
Definition ia_mod_at : Z := B_prog_val (A_OBJ 2) + 0x110c0.
Definition ia_stamp : Z := B_prog_val (A_OBJ 2) + 0x11380.
(* the musl stdio half of PINV and its bytes: the text of lib/AU/PresetCfnB.v:297-298 (pinv_stdio) and :306-307
   (stdio_img), blob 773e6d0f6c59, with its section-1 constants (:204-207: A_THREADED 0x5fe9c1, A_NEED_LOCKS 0x5fe9c3,
   A_OFL_LOCK 0x5fee20, A_OFL_HEAD 0x5fee28, MEASURED on twin c90d4fa5) written in. *)
Definition ia_sio (rd : reader) : Prop :=
  rd 0x5fe9c1 = Some 0 /\ rd 0x5fe9c3 = Some 0 /\ rd32 rd 0x5fee20 0 /\ rd64 rd 0x5fee28 0.
Definition ia_sio_img (a : Z) : Prop :=
  a = 0x5fe9c1 \/ a = 0x5fe9c3 \/ (0x5fee20 <= a < 0x5fee20 + 4) \/ (0x5fee28 <= a < 0x5fee28 + 8).
Definition ia_sio_ivs : list (Z * Z) := [(0x5fe9c1, 1); (0x5fe9c3, 1); (0x5fee20, 4); (0x5fee28, 8)].
Lemma ia_sio_img_ivs : forall a, ia_sio_img a -> Exists (in_zr a) ia_sio_ivs.
Proof.
intros a Ha. unfold ia_sio_img in Ha. unfold ia_sio_ivs.
destruct Ha as [H|[H|[H|H]]].
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
(* the half of kept_img (PRH_Base.v blob 3004a98fe2d9 :1020-1023) that reads the image and not B, at PI_prog_B's
   pa_lo / pa_hi (= IMG_LO_B / IMG_TOP_B, PAImg_prog.v:407) *)
Definition ia_lit_ro (p n : Z) : Prop :=
  IMG_LO_B + 64 <= p /\ p + n + 64 <= IMG_TOP_B /\
  (forall a, p <= a < p + n -> in_roP rsegs B_prog_relro_lo B_prog_relro_hi a).
(* the half of kept_img that reads B *)
Definition ia_lits_B (B : asyms) (p n : Z) : Prop :=
  forall a, p <= a < p + n ->
    ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\ ro_shadow_ok B a.

(* ---------------------------------------------------------------------- *)
(* 2. The fields of ec_img that do not read the runtime symbol record B, one lemma each, at the instance. *)
Section InstB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation PAI := (PI_prog_B (rc := rc)).
Local Notation SEGS := (@pa_segs rc B_prog_listing PAI).
Local Notation PST := (@prh_pst prh_img_B).

Lemma ei_entry_B : @pa_sigma rc B_prog_listing PAI AS_LLVMFuzzerTestOneInput = EC_BASE (rc := rc) (L := B_prog_listing) (PA := PAI).
Proof. vm_compute. reflexivity. Qed.

Lemma ei_frame_B : EC_SAVE + 16 <= @pi_frame prh_img_B F_LLVMFuzzerTestOneInput.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* both halves: YImgTop's B' bounds IMG_LO_B / IMG_TOP_B and PI_prog_B's own pa_lo / pa_hi (0x10000 / 0x601000) *)
Lemma ei_empty_B : (YImgTop.IMG_LO_B + 64 <= ia_empty /\ ia_empty + 64 <= YImgTop.IMG_TOP_B) /\
  (@pa_lo rc B_prog_listing PAI + 64 <= ia_empty /\ ia_empty + 64 <= @pa_hi rc B_prog_listing PAI).
Proof. split; split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* at the CfParams of record on this branch (CfParamsPreset.v blob 1333a52cd63a: cf_malloc_max = 2 ^ 29 - 2 ^ 20);
   it holds at the owner's 402,653,184 too, and the same vm_compute re-checks it when that value lands *)
Lemma ei_malloc_max_B : PRH_FnWriter.prhWriter_WMAX + @cf_head CfParams_preset < @cf_malloc_max CfParams_preset.
Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.
(* THE NEW FIELD (CFHEAD-16): the harness HEAD is the model's, 16 = 16 at CfParams_preset *)
Lemma ei_head_B : @cf_head CfParams_preset = PresetReqAt.HEAD.
Proof. vm_compute. reflexivity. Qed.

Lemma ei_own_B : @pa_val rc B_prog_listing PAI (A_HI 4) + 0x590 = @pi_g_own_ran_out prh_img_B /\
  @pi_gz_own_ran_out prh_img_B = 1%nat.
Proof. split; vm_compute; reflexivity. Qed.

Lemma ei_most_w_B : @pi_gz_most prh_img_B = 8%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma ei_fp_B : @pi_fp prh_img_B F_LLVMFuzzerTestOneInput = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ei_rets_B : forall G r, In (G, r) (ec_call_rets (rc := rc) (L := B_prog_listing) (PA := PAI)) ->
  In r (@pi_call_rets prh_img_B F_LLVMFuzzerTestOneInput G).
Proof.
assert (HB : forallb (fun p => existsb (Z.eqb (snd p)) (@pi_call_rets prh_img_B F_LLVMFuzzerTestOneInput (fst p)))
  (ec_call_rets (rc := rc) (L := B_prog_listing) (PA := PAI)) = true) by (vm_compute; reflexivity).
intros G r H. pose proof (proj1 (forallb_forall _ _) HB (G, r) H) as X. cbv beta in X. cbn [fst snd] in X.
apply existsb_exists in X as (r' & Hr' & E). apply Z.eqb_eq in E. subst r'. exact Hr'.
Qed.

Lemma ei_pst_sep_B : pairwise zdisjoint PST.
Proof. apply (pairwise_of_b zdisjoint zdisjoint_b zdisjoint_of_b). vm_compute. reflexivity. Qed.

(* ei_pst without its ec_static_free half (which reads B) *)
Lemma ei_pst_img_B : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Proof.
assert (HB : forallb (fun r => iv_img_b rsegs (fst r) (snd r)) PST = true) by (vm_compute; reflexivity).
exact (pst_all_of_b (fun a => in_img rsegs a) (iv_img_b rsegs) (iv_img_sound rsegs) PST HB).
Qed.

Lemma ei_pst_ro_B : forall a, Exists (in_zr a) PST ->
  ~ in_roP SEGS (@pa_relro_lo rc B_prog_listing PAI) (@pa_relro_hi rc B_prog_listing PAI) a.
Proof.
assert (HB : forallb (fun r => iv_off_ro rsegs B_prog_relro_lo B_prog_relro_hi (fst r) (snd r)) PST = true)
  by (vm_compute; reflexivity).
exact (pst_all_of_b (fun a => ~ in_roP rsegs B_prog_relro_lo B_prog_relro_hi a)
  (iv_off_ro rsegs B_prog_relro_lo B_prog_relro_hi) (iv_off_ro_sound rsegs B_prog_relro_lo B_prog_relro_hi) PST HB).
Qed.

(* ei_sio without its ec_static_free half (which reads B) *)
Lemma ei_sio_img_B : forall a, ia_sio_img a -> in_img SEGS a /\ ~ Exists (in_zr a) PST.
Proof.
assert (H1 : forallb (fun r => iv_img_b rsegs (fst r) (snd r)) ia_sio_ivs = true) by (vm_compute; reflexivity).
assert (H2 : forallb (fun r => iv_off_pst PST (fst r) (snd r)) ia_sio_ivs = true) by (vm_compute; reflexivity).
intros a Ha. pose proof (ia_sio_img_ivs a Ha) as HE. split.
- exact (pst_all_of_b (fun a => in_img rsegs a) (iv_img_b rsegs) (iv_img_sound rsegs) ia_sio_ivs H1 a HE).
- exact (pst_all_of_b (fun a => ~ Exists (in_zr a) PST) (iv_off_pst PST) (iv_off_pst_sound PST) ia_sio_ivs H2 a HE).
Qed.

Lemma ei_sio_frame_B : forall rd rd' : reader, (forall a, ia_sio_img a -> rd' a = rd a) -> ia_sio rd -> ia_sio rd'.
Proof.
intros rd rd' Hf H. unfold ia_sio in H |- *. unfold rd32, rd64 in *. destruct H as (H1 & H2 & H3 & H4).
split; [|split; [|split]].
- rewrite (Hf 0x5fe9c1) by (left; reflexivity). exact H1.
- rewrite (Hf 0x5fe9c3) by (right; left; reflexivity). exact H2.
- intros k Hk. rewrite (Hf (0x5fee20 + Z.of_nat k)) by (right; right; left; lia). exact (H3 k Hk).
- intros k Hk. rewrite (Hf (0x5fee28 + Z.of_nat k)) by (right; right; right; lia). exact (H4 k Hk).
Qed.

(* ei_lits without its B half: both literals are read-only image bytes 64 bytes inside the image *)
Lemma ei_lits_ro_B : ia_lit_ro ia_mod_at (Z.of_nat (length ck_MOD_AT) + 1) /\
  ia_lit_ro ia_stamp (Z.of_nat (length ck_STAMP) + 1).
Proof.
assert (G : forall p n, (IMG_LO_B + 64 <=? p) = true -> (p + n + 64 <=? IMG_TOP_B) = true -> iv_ro_b rsegs p n = true ->
  ia_lit_ro p n).
{ intros p n H1 H2 H3. apply Z.leb_le in H1. apply Z.leb_le in H2. split; [exact H1 | split; [exact H2 |]].
  intros a Ha. exact (iv_ro_sound rsegs B_prog_relro_lo B_prog_relro_hi p n a H3 Ha). }
split; apply G; vm_compute; reflexivity.
Qed.

Lemma ei_pst_w_B : forall a, Exists (in_zr a) PST -> writable_at SEGS (fun _ => None) a.
Proof.
assert (HB : forallb (fun r => iv_w_b rsegs (fst r) (snd r)) PST = true) by (vm_compute; reflexivity).
exact (pst_all_of_b (fun a => writable_at rsegs (fun _ => None) a) (iv_w_b rsegs) (iv_w_sound rsegs) PST HB).
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. ec_img at the instance FOR EVERY B that has the facts which read B (the six premises: ei_sm1, ei_pal, the
      ec_static_free halves of ei_sio and ei_pst, the B half of ei_lits for each literal). Section 4 proves the six at
      the #102 B' runtime symbol record and so ec_img itself. *)
Theorem ec_img_B_given_syms : forall B : asyms,
  pc_stack_malloc (as_code B) LLVMF_FS_CLASS = @pa_sigma rc B_prog_listing PAI AS___asan_stack_malloc_1 ->
  PALib (L := B_prog_listing) (PI := PAI) B ->
  (forall a, ia_sio_img a -> ec_static_free B a) ->
  (forall a, Exists (in_zr a) PST -> ec_static_free B a) ->
  ia_lits_B B ia_mod_at (Z.of_nat (length ck_MOD_AT) + 1) ->
  ia_lits_B B ia_stamp (Z.of_nat (length ck_STAMP) + 1) ->
  ec_img (rc := rc) (cp := CfParams_preset) (PI := prh_img_B) (L := B_prog_listing) (PA := PAI)
    B ia_empty ia_mod_at ia_stamp ia_sio ia_sio_img.
Proof.
intros B Hsm1 Hpal Hsio Hpst Hl1 Hl2.
destruct ei_lits_ro_B as [(M1 & M2 & M3) (S1 & S2 & S3)].
constructor.
- exact ei_entry_B.
- exact Hsm1.
- exact Hpal.
- intros a Ha. destruct (ei_sio_img_B a Ha) as [I1 I2]. exact (conj (Hsio a Ha) (conj I1 I2)).
- exact ei_sio_frame_B.
- intros a Ha. exact (conj (Hpst a Ha) (ei_pst_img_B a Ha)).
- exact ei_frame_B.
- exact ei_pst_ro_B.
- exact ei_empty_B.
- exact ei_malloc_max_B.
- exact ei_head_B.
- exact ei_own_B.
- exact ei_most_w_B.
- exact ei_fp_B.
- exact ei_rets_B.
- exact ei_pst_sep_B.
- unfold kept_img. split.
  + split; [exact M1|]. split; [exact M2|]. intros a Ha. destruct (Hl1 a Ha) as (O1 & O2 & O3).
    exact (conj (M3 a Ha) (conj O1 (conj O2 O3))).
  + split; [exact S1|]. split; [exact S2|]. intros a Ha. destruct (Hl2 a Ha) as (O1 & O2 & O3).
    exact (conj (S3 a Ha) (conj O1 (conj O2 O3))).
- exact ei_pst_w_B.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The six facts that read the runtime symbol record, at the #102 B' record YD2l.TfibB (lib/Reusable/YD2l.v blob
      95803a8b9493, a Theorem Labs lane's working branch cb0d7a5ccaaf: as_code := YF0l.Tfib_code, blob
      4a405a3dba65, over lib/Reusable/YImgCellsB.v blob f1cc7493a79d; the cells, as_errno, as_const, as_owned_static and
      as_zero_shadow from lib/Reusable/YF0m.v blob f82202ebccdf; as_universe := lib/Reusable/YCej.v blob 8a099324acb0),
      each by computation on the record and the image, then ec_img at the concrete instance. The decision procedures
      are lib/A/Ent102InstA.v's section 4, restated here (this file does not import the A' image). *)
Definition z1_find (s v : Z) (l : list acell) : bool :=
  existsb (fun c => match c with
    | ACell (ANum s') (S O) (AV (ANum v')) => (s' =? s) && (v' =? v)
    | _ => false end)%bool l.
Lemma z1_find_In : forall s v l, z1_find s v l = true -> In (z1 (ANum s) v) l.
Proof.
intros s v l H. apply existsb_exists in H as (c & Hc & Hb).
destruct c as [ca cw cv]. destruct ca; try (cbn in Hb; discriminate Hb).
destruct cw as [|[|cw]]; try (cbn in Hb; discriminate Hb).
destruct cv as [e|m w]; try (cbn in Hb; discriminate Hb).
destruct e; try (cbn in Hb; discriminate Hb).
cbn in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. exact Hc.
Qed.
Definition zs_b (ZS : list (Z * Z)) (a : Z) : bool :=
  existsb (fun r => (fst r <=? a - a mod 8) && (a - a mod 8 + 8 <=? fst r + snd r))%bool ZS.
Definition cs_b (CS : list acell) (a : Z) : bool :=
  existsb (fun v => z1_find (shadow_addr a) v CS && ((v =? 0) || ((a mod 8 <? v) && (v <? 8))))%bool
    (map Z.of_nat (seq 0 8)).
Definition ro_shadow_b (ZS : list (Z * Z)) (CS : list acell) (a : Z) : bool := (zs_b ZS a || cs_b CS a)%bool.
Lemma ro_shadow_sound : forall B CS a, (forall ly c, In c CS -> In c (as_const B ly)) ->
  ro_shadow_b (as_zero_shadow B) CS a = true -> ro_shadow_ok B a.
Proof.
intros B CS a HC H. unfold ro_shadow_ok. unfold ro_shadow_b in H. apply orb_prop in H as [H|H].
- left. unfold zs_b in H. apply existsb_exists in H as ((q & m) & Hq & X). cbn [fst snd] in X.
  apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2.
  unfold in_zs. exists q, m. split; [exact Hq | split; lia].
- right. unfold cs_b in H. apply existsb_exists in H as (v & _ & X).
  apply andb_prop in X as [X1 X2]. exists v. split.
  + intros ly. exact (HC ly _ (z1_find_In _ _ _ X1)).
  + apply orb_prop in X2 as [X2|X2]; [left; apply Z.eqb_eq, X2|].
    right. apply andb_prop in X2 as [Y1 Y2]. apply Z.ltb_lt in Y1. apply Z.ltb_lt in Y2. lia.
Qed.
Definition sfree_b (OS : list (Z * Z)) (er lo n : Z) : bool :=
  (iv_off_pst OS lo n && ((lo + n <=? er) || (er + 4 <=? lo)))%bool.
Lemma sfree_sound : forall B lo n a, sfree_b (as_owned_static B) (as_errno B) lo n = true -> lo <= a < lo + n ->
  ec_static_free B a.
Proof.
intros B lo n a H Ha. unfold sfree_b in H. apply andb_prop in H as [H1 H2]. unfold ec_static_free. split.
- exact (iv_off_pst_sound _ lo n a H1 Ha).
- apply orb_prop in H2 as [Y|Y]; apply Z.leb_le in Y; lia.
Qed.
Definition lits_B_b (OS : list (Z * Z)) (er : Z) (ZS : list (Z * Z)) (CS : list acell) (p n : Z) : bool :=
  forallb (fun k => sfree_b OS er (p + Z.of_nat k) 1 && ro_shadow_b ZS CS (p + Z.of_nat k))%bool
    (seq 0 (Z.to_nat n)).
Lemma lits_B_sound : forall B CS p n, (forall ly c, In c CS -> In c (as_const B ly)) ->
  lits_B_b (as_owned_static B) (as_errno B) (as_zero_shadow B) CS p n = true -> ia_lits_B B p n.
Proof.
intros B CS p n HC H. unfold ia_lits_B. intros a Ha. unfold lits_B_b in H.
assert (Hk : In (Z.to_nat (a - p)) (seq 0 (Z.to_nat n))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) H _ Hk) as X. cbv beta in X.
rewrite Z2Nat.id in X by lia. replace (p + (a - p)) with a in X by lia.
apply andb_prop in X as [X1 X2].
destruct (sfree_sound B a 1 a X1 ltac:(lia)) as [F1 F2].
exact (conj F1 (conj F2 (ro_shadow_sound B CS a HC X2))).
Qed.

Local Notation TB := YD2l.TfibB.

(* ei_sm1: the class-1 frame-area entry of the record is the listing's __asan_stack_malloc_1 (0x3dda8) *)
Lemma ei_sm1_B : pc_stack_malloc (as_code TB) LLVMF_FS_CLASS = @pa_sigma rc B_prog_listing PAI AS___asan_stack_malloc_1.
Proof. vm_compute. reflexivity. Qed.

(* ei_pal: YC1fP's PALib at PI_prog_B and the record *)
Lemma ei_pal_B : PALib (L := B_prog_listing) (PI := PAI) TB.
Proof.
constructor.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- left. apply Z.leb_le. vm_compute. reflexivity.
- hnf. split; [|split].
  + split; apply Z.leb_le; vm_compute; reflexivity.
  + intros a Ha. exact (iv_img_sound rsegs (as_errno TB) 4 a ltac:(vm_compute; reflexivity) Ha).
  + split; apply YCej.memZL_In; vm_compute; reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- split; apply Z.ltb_lt; vm_compute; reflexivity.
- vm_compute. reflexivity.
- exact B_prog_got_uar_disj.
Qed.

(* ei_sio's static-free half: the four stdio cells are off every owned static and off errno *)
Lemma ei_sio_free_B : forall a, ia_sio_img a -> ec_static_free TB a.
Proof.
assert (HB : forallb (fun r => sfree_b (as_owned_static TB) (as_errno TB) (fst r) (snd r)) ia_sio_ivs = true)
  by (vm_compute; reflexivity).
intros a Ha.
exact (pst_all_of_b (ec_static_free TB) (sfree_b (as_owned_static TB) (as_errno TB)) (sfree_sound TB) ia_sio_ivs HB a
  (ia_sio_img_ivs a Ha)).
Qed.

(* ei_pst's static-free half: the seven ledger cells are off every owned static and off errno *)
Lemma ei_pst_free_B : forall a, Exists (in_zr a) PST -> ec_static_free TB a.
Proof.
assert (HB : forallb (fun r => sfree_b (as_owned_static TB) (as_errno TB) (fst r) (snd r)) PST = true)
  by (vm_compute; reflexivity).
exact (pst_all_of_b (ec_static_free TB) (sfree_b (as_owned_static TB) (as_errno TB)) (sfree_sound TB) PST HB).
Qed.

(* ei_lits' record half: each literal byte is off the owned statics and errno, and its shadow is a zero-shadow granule
   or the image's const shadow cell (modifiedAt's last granule 03, the stamp's 05) *)
Lemma ei_lits_B_B : ia_lits_B TB ia_mod_at (Z.of_nat (length ck_MOD_AT) + 1) /\
  ia_lits_B TB ia_stamp (Z.of_nat (length ck_STAMP) + 1).
Proof.
assert (HC : forall ly c, In c YF0m.Tfib_const_shadow -> In c (as_const TB ly)).
{ intros ly c Hc. change (as_const TB ly) with (YF0m.Tfib_const ly). unfold YF0m.Tfib_const.
  apply in_app_iff. right. apply in_app_iff. right. exact Hc. }
split; apply (lits_B_sound TB YF0m.Tfib_const_shadow _ _ HC); vm_compute; reflexivity.
Qed.

(* THE VACUITY GUARD at B': ec_img at the concrete instance *)
Theorem ec_img_B : ec_img (rc := rc) (cp := CfParams_preset) (PI := prh_img_B) (L := B_prog_listing) (PA := PAI)
  TB ia_empty ia_mod_at ia_stamp ia_sio ia_sio_img.
Proof.
destruct ei_lits_B_B as [Lm Ls].
exact (ec_img_B_given_syms TB ei_sm1_B ei_pal_B ei_sio_free_B ei_pst_free_B Lm Ls).
Qed.
End InstB.

Print Assumptions ei_entry_B.
Print Assumptions ei_frame_B.
Print Assumptions ei_empty_B.
Print Assumptions ei_malloc_max_B.
Print Assumptions ei_head_B.
Print Assumptions ei_own_B.
Print Assumptions ei_most_w_B.
Print Assumptions ei_fp_B.
Print Assumptions ei_rets_B.
Print Assumptions ei_pst_sep_B.
Print Assumptions ei_pst_img_B.
Print Assumptions ei_pst_ro_B.
Print Assumptions ei_sio_img_B.
Print Assumptions ei_sio_frame_B.
Print Assumptions ei_lits_ro_B.
Print Assumptions ei_pst_w_B.
Print Assumptions ec_img_B_given_syms.
Print Assumptions ei_sm1_B.
Print Assumptions ei_pal_B.
Print Assumptions ei_sio_free_B.
Print Assumptions ei_pst_free_B.
Print Assumptions ei_lits_B_B.
Print Assumptions ec_img_B.
