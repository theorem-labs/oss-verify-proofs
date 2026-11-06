(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset literal, image A' (#102 asan pin 1be0f53d96cb, unstripped twin bff8519bbe3e; facts
   8f3e7e1a07f1): the BRIDGE from the memnorm-keeping leaf walk literal_x_holds_mnI (lib/A/Prog/literal_mn.v, statement
   tliteral_leafXmn of lib/Prog/literal_xs_mn.v at VRA = 4: tliteral_leafX with (YAkMemnorm.memnorm segs memc ->
   YAkMemnorm.memnorm segs mem2) last in the post) to the caller-facing m-form text tliteral_specX at the kit of record
   decff67d721f, instantiated as the image-A texts are: (cp := CfParams_preset) (PI := prh_img_A)
   (RL := prh_room_live_a8) (PA := PI_prog_A).
   #102: relocated from the old-pin bridge (commit 34b0f96319c6, pin d83eb25dbf0d) by the
   alreloc of record c4338d099cfb8025 (no numeral of this file moved); the listings are the #102 ones of this tree's base
   commit 6240a87c3eb7 (Listing_prog 7ed1529926bd, PAImg_prog 505a51ff7d08, PAImg_leaves
   9c07e1905609; PRH_Img of record 934516a622e8).
   The text, read BY PATH:
    git rev-parse decff67d721f:proofs/omx-clap-core/fuzz_preset/lib/A/PRH_FnReader.v
     -> 0af3032ed375 (tliteral_specX :246-275, post fpostWm with S' = S; since the donor's kit 04388d628fb the text
     quantifies `most own` and its ledger prh_ledger .. ran most own carries #102's g_most / g_own_ran_out cells), its
     predicates
    git rev-parse decff67d721f:proofs/omx-clap-core/fuzz_preset/lib/A/PRH_Base.v
     -> 3004a98fe2d9 (fpre and fpostWm = fpostW at fQmn unchanged since 04388d628fb; prh_glob gains prh_most / prh_own,
     prh_pst gains (pi_g_most, ..) and (pi_g_own_ran_out, ..) as its 6th and 7th rows) and lib/A/PRH_Reader.v
     91d2dbd40054 (unchanged).
   The proof is the a3bdeca3920-text bridge's (lib/A/Prog/literal_bridge.v at origin/cold/h-verbs-1-lit-onrelocB
   6a1549f9a5bd) with three changes: fpre's fourth conjunct (raZ regs < alloc_ceiling) is unused; the post's witnesses
   are ly' := ly, S' := S, Hp' := Hp (literal calls only strlen and bcmp: no allocation, no fake frame), so S' = S is
   reflexivity; the fQmn keep is the leaf's last post conjunct. The leaf's call texts are the memnorm twins
   YGcallMxmn.astrlen_realizes_xrom / abcmp_realizes_xm (lib/Reusable/YGcallMxmn.v b47cf7942c3d), so ASTRLEN / ABCMP are
   those twins at PI_prog_A's entries (ASTRLEN at PI_prog_A's relro range).
   READ-ONLY MEMORY (2026-10-29): the leaf takes PresetRodata.arodata_okP SEGS rlo rhi B (aview ..) (lib/Prog/literal_xs.v),
   at rlo / rhi := PI_literal's relro range, = PI_prog_A's (lit_br_relro); fpre's second conjunct HROD (PRH_Base.v
   arodata_okP at pa_relro_lo / pa_relro_hi, the same body) is that premise. The former premise pal_rom_ok (no owned
   static and no errno byte in a read-only segment), which turned HROD into rom_view, is gone: it is FALSE at TfibB
   (68059ec877b).
   TRANSPORT PI_prog_A -> PI_literal (the leaf's listing instance; both have pa_segs := rsegs): by vm_compute over
   named values only (the lit_br_ Remarks); the leaf's PALibCore comes from PALib at PI_prog_A through palib_core.
   SECTION HYPOTHESES: LAWS (AR_laws_x, head length HL implicit), PAL (PALib at PI_prog_A), ASTRLEN / ABCMP.
   The caller window e: the leaf runs at STK := STK_literal + e, sp0 := spZ regs + e, FP := [(q, q + 8);
   (v, v + 4)], from the widened journal at entry (lit_br_init_W). Numerals: 16 (cf_head at CfParams_preset, by
   change), 8 / 4 / 24 (LENGTH: words, the cursor struct, the type cell), 4096, 2 ^ 47, 2 ^ 64 (LENGTH / DERIVED
   bounds). No address literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_leaves PAImg_leaves Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnReader CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import literal_xs literal_xs_mn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import literal_mn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

#[local] Notation PIL := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PAImg_leaves.PI_literal.
#[local] Notation PA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PAImg_prog.PI_prog_A.
#[local] Notation CP := CfParams_preset.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Remark lit_br_sigma : @pa_sigma _ A_prog_listing PA AS_literal = @pa_val _ literal_listing PIL A_TEXT.
Proof. vm_compute. reflexivity. Qed.
Remark lit_br_strlen : @pa_sigma _ literal_listing PIL AS___wrap_strlen = @pa_sigma _ A_prog_listing PA AS___wrap_strlen.
Proof. vm_compute. reflexivity. Qed.
Remark lit_br_bcmp : @pa_sigma _ literal_listing PIL AS___wrap_bcmp = @pa_sigma _ A_prog_listing PA AS___wrap_bcmp.
Proof. vm_compute. reflexivity. Qed.
Remark lit_br_free : @pa_sigma _ literal_listing PIL AS___wrap_free = @pa_sigma _ A_prog_listing PA AS___wrap_free.
Proof. vm_compute. reflexivity. Qed.
Remark lit_br_malloc : @pa_sigma _ literal_listing PIL AS___wrap_malloc = @pa_sigma _ A_prog_listing PA AS___wrap_malloc.
Proof. vm_compute. reflexivity. Qed.
Remark lit_br_obj0 : @pa_val _ literal_listing PIL (A_OBJ 0) = @pa_val _ A_prog_listing PA (A_OBJ 0).
Proof. vm_compute. reflexivity. Qed.
Remark lit_br_obj12 : @pa_val _ literal_listing PIL (A_OBJ 12) = @pa_val _ A_prog_listing PA (A_OBJ 12).
Proof. vm_compute. reflexivity. Qed.
Remark lit_br_base : @pa_val _ A_prog_listing PA A_TEXT <= @pa_val _ literal_listing PIL A_TEXT.
Proof. vm_compute. discriminate. Qed.
Remark lit_br_stk : @STK_literal prh_img_A = LIT_STK.
Proof. vm_compute. reflexivity. Qed.
Remark lit_br_pst_img : forallb (fun r => existsb (fun sg => (Z.of_N (seg_base sg) <=? fst r) &&
  (fst r + snd r <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) (@pa_segs _ A_prog_listing PA))
  (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.
Remark lit_br_relro : @pa_relro_lo _ literal_listing PIL = @pa_relro_lo _ A_prog_listing PA /\
  @pa_relro_hi _ literal_listing PIL = @pa_relro_hi _ A_prog_listing PA.
Proof. split; vm_compute; reflexivity. Qed.
(* the leaf instance's image top lies below the stack band (the leaf's off-image premise at pa_lo / pa_hi) *)
Remark lit_br_hi : @pa_hi _ literal_listing PIL < 2 ^ 46.
Proof. vm_compute. reflexivity. Qed.

Lemma lit_br_val_keep : forall segs H (m m' : word -> option byte) a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs H m' x = aview segs H m x) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v.
Proof.
intros segs H m m' a n v K V k Hk. rewrite (YCbq.mbyte_of_aview segs H H m m' (a + Z.of_nat k)) by (apply K; lia).
exact (V k Hk).
Qed.
Lemma lit_br_garr8_keep : forall segs H (m m' : word -> option byte) a (l : list Z),
  (forall x, a <= x < a + Z.of_nat (length l) -> aview segs H m' x = aview segs H m x) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H m') a l.
Proof.
intros segs H m m' a l K G. apply (YI00.garr8_frame segs _ _ _ _ G). intros x Hx.
apply (YCbq.mbyte_of_aview segs). apply K. exact Hx.
Qed.

#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.
Hypothesis ASTRLEN : YGcallMxmn.astrlen_realizes_xrom SEGS B ARx (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA)
  (@pa_sigma _ A_prog_listing PA AS___wrap_strlen).
Hypothesis ABCMP : YGcallMxmn.abcmp_realizes_xm SEGS B ARx (@pa_sigma _ A_prog_listing PA AS___wrap_bcmp).

Lemma lit_br_palc : PALibCore (L := literal_listing) (PI := PIL) B.
Proof.
destruct (palib_core B PAL) as [G0 C12 GC ENV FR ML RT].
pose proof lit_br_base as HB.
split.
- rewrite lit_br_obj0. exact G0.
- rewrite lit_br_obj12. exact C12.
- rewrite lit_br_obj0, lit_br_obj12. exact GC.
- exact ENV.
- rewrite lit_br_free. exact FR.
- rewrite lit_br_malloc. exact ML.
- lia.
Qed.
Lemma lit_br_astrlen : YGcallMxmn.astrlen_realizes_xrom (@pa_segs _ literal_listing PIL) B ARx (@pa_relro_lo _ literal_listing PIL)
  (@pa_relro_hi _ literal_listing PIL) (@pa_sigma _ literal_listing PIL AS___wrap_strlen).
Proof. destruct lit_br_relro as [E1 E2]. rewrite E1, E2, lit_br_strlen. exact ASTRLEN. Qed.
Lemma lit_br_abcmp : YGcallMxmn.abcmp_realizes_xm (@pa_segs _ literal_listing PIL) B ARx (@pa_sigma _ literal_listing PIL AS___wrap_bcmp).
Proof. rewrite lit_br_bcmp. exact ABCMP. Qed.

(* the start-of-walk journal at the widened caller window, built with the journal's constructor YCbqG.ajx_intro; the
   stretch stores no trace (S' = S), so its wild-trace budget is closed by YCbqG.wild_part_same *)
Lemma lit_br_init_W : forall STK e FP ly S Hp W regs mem md ch,
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch ->
  0 <= e -> e mod 16 = 0 -> spZ regs + e <= ly_top ly ->
  (forall a, spZ regs <= a < spZ regs + e -> apresent (w_H W) mem a) ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (STK + e) (spZ regs + e) FP ly S Hp W mem md [] ly S Hp W mem md 0.
Proof.
intros STK e FP ly S Hp W regs mem md ch (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) He0 He16 Hetop Hepres.
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
refine (ajx_intro (rc := rc) (SK := SK) (segs := SEGS) (B := B) (PST := @prh_pst prh_img_A) (ARx := ARx) (STK := STK + e)
  (sp0 := spZ regs + e) (FP := FP) (ly := ly) (S := S) (W := W) (mem := mem) (md := md) (own := []) (ly' := ly) (S' := S)
  (Hp' := Hp) (W' := W) (mem' := mem) (md' := md) (k := 0) (WS := []) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
- exact HAR.
- apply layout_le_refl.
- lia.
- apply wle_refl.
- apply aos_step_refl.
- reflexivity.
- lia.
- lia.
- intros; reflexivity.
- intros; reflexivity.
- intros; reflexivity.
- intros; reflexivity.
- intros p n i H1 H2; exfalso; exact (H2 H1).
- intros a Ha. destruct (Z_lt_le_dec a (spZ regs)) as [Hl|Hl]; [apply Hpres; lia | apply Hepres; lia].
- unfold astk_ok. repeat split; try lia.
- intros; reflexivity.
- exact HQT.
- apply wild_part_same.
Qed.

Theorem literal_holds : tliteral_specX (cp := CP) (PI := prh_img_A) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) B ARx SK.
Proof.
unfold tliteral_specX.
intros ly S Hp W regs mem md ch e q text len p d tb w cw slack ty v Lam peak cnt fail ran most own
  (HPRE & HROD & Hgap & Hraz) H10 H11 H12 H13 HPJ HWIN Hqs Hqe Hqra Hsrc Hhome Hcstr Hw63 Gw Hnz Hsl Hwsp Hty Hvnz Hv8 Hvat Hvra Hvq Hvt HLED.
pose proof lit_br_stk as HSTK. rewrite HSTK in HPRE, Hwsp |- *.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof HPJ as (Hqp & Hqend & Hqd & Hqrw & Hq8 & Htx0 & Htxl & Hptx & Hlen & Gtx & Hqtx & Hd).
pose proof Hsrc as (Gtx' & Ht4k & Htceil & Hamt & Hrat & Hhut).
pose proof Hcstr as ((Gw0 & Hnz0) & Hw4k & Hwceil & Hcw32 & Hamw8c & Hraw & Hhuw & Hvisw).
pose proof HLED as (HG & HND & HFA & HPM).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold (spZ regs) in SPR.
rewrite Hlen in Htceil, Hamt, Hrat, Hhut.
unfold LIT_STK, ESTACK in *.
assert (HV : 4096 <= v /\ amem_range v 4 /\ (forall x, v <= x < v + 4 -> ~ YG0d.in_img SEGS x) /\
  (spZ regs <= v \/ v + 4 <= spZ regs - (80 + 2 * 4096)) /\
  (forall x, v <= x < v + 4 ->
    (awr_byte ((80 + 2 * 4096) + e) (spZ regs + e) [(q, q + 8); (v, v + 4)] (ablocks B ly S) (ablocks B ly S) ly [] x \/
     wr_fp_frame [(q, q + 8); (v, v + 4)] S ly x) /\ apresent (w_H W) mem x) /\
  (forall a k, In (a, k) Lam -> forall x, v <= x < v + 4 -> ~ (a - 16 <= x < a - 8))).
{ assert (FPv : forall x, v <= x < v + 4 -> inFP [(q, q + 8); (v, v + 4)] x).
  { intros x Hx. exists (v, v + 4). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
  assert (HDK : forall a k, In (a, k) Lam -> In (a - 16, k + 16) (ablocks B ly S) /\ 0 <= k).
  { intros a k Hin. destruct (proj1 (Forall_forall _ _) HFA (a, k) Hin) as (Hk0 & Hab & _ & _ & _).
    cbn [fst snd] in Hk0, Hab. change (@cf_head CP) with 16 in Hab. split; [exact Hab | exact Hk0]. }
  assert (RQ : forall k, 0 < k -> req_size k = k) by (intros k0 Hk0; unfold req_size; destruct (Z.eqb_spec k0 0); lia).
  destruct Hvat as [(a1 & k1 & Hin1 & Ha1 & Hk1) | [(b & m & Hbin & Hnot & Hb1 & Hb2) |
    [(cid & pos & Hfin & Hf1 & Hf2) | (Hx1 & Hx2)]]].
  - destruct (HDK a1 k1 Hin1) as (Hab1 & Hk10).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hab1) as (Hb16 & Hb4k & Hbceil & Hbapp & Hbpres & Hbpw).
    rewrite (RQ (k1 + 16)) in Hbceil, Hbapp, Hbpres by lia.
    split; [lia|]. split; [unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL, kLowMemEnd in *; lia|].
    split.
    { intros x Hx. refine (proj2 (alx_client_img _ _ _ LAWS ly S Hp W mem md x HAR _)). left.
      exists (a1 - 16), (k1 + 16). split; [exact Hab1 | rewrite (RQ (k1 + 16)) by lia; lia]. }
    split; [right; lia|]. split.
    { intros x Hx. split; [left; right; left; split; [exact (FPv x Hx)|] | apply (proj1 (Hbpres x ltac:(lia)))].
      exists (a1 - 16), (k1 + 16). split; [exact Hab1 | rewrite (RQ (k1 + 16)) by lia; lia]. }
    intros a k Hin x Hx Hh. destruct (HDK a k Hin) as (Hab & Hk0).
    destruct (Z.eq_dec a a1) as [->|Hne]; [lia|].
    pose proof (sep_blocks_x _ _ _ LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hab1 ltac:(intros E; injection E; intros; lia)) as Hdj.
    unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite !RQ in Hdj by lia. lia.
  - destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hbin) as (Hb16 & Hb4k & Hbceil & Hbapp & Hbpres & Hbpw).
    change (@cf_head CP) with 16 in Hnot.
    rewrite (RQ m) in Hbceil, Hbapp, Hbpres by lia.
    split; [lia|]. split; [unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL, kLowMemEnd in *; lia|].
    split.
    { intros x Hx. refine (proj2 (alx_client_img _ _ _ LAWS ly S Hp W mem md x HAR _)). left.
      exists b, m. split; [exact Hbin | rewrite (RQ m) by lia; lia]. }
    split; [right; lia|]. split.
    { intros x Hx. split; [left; right; left; split; [exact (FPv x Hx)|] | apply (proj1 (Hbpres x ltac:(lia)))].
      exists b, m. split; [exact Hbin | rewrite (RQ m) by lia; lia]. }
    intros a k Hin x Hx Hh. destruct (HDK a k Hin) as (Hab & Hk0).
    destruct (Z.eq_dec b (a - 16)) as [Eb|Nb]; [destruct (Z.eq_dec m (k + 16)) as [Em|Nm]|].
    + apply Hnot. replace (b + 16, m - 16) with (a, k) by (f_equal; lia). exact Hin.
    + pose proof (sep_blocks_x _ _ _ LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hbin ltac:(intros E; injection E; intros; lia)) as Hdj.
      unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite !RQ in Hdj by lia. lia.
    + pose proof (sep_blocks_x _ _ _ LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hbin ltac:(intros E; injection E; intros; lia)) as Hdj.
      unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite !RQ in Hdj by lia. lia.
  - destruct (alx_frames _ _ _ LAWS ly S Hp W mem md cid pos HAR Hfin) as (Hf32 & Hfapp & Hfpres & Hfsh).
    destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as (_ & Hfb).
    pose proof (proj1 (Forall_forall _ _) Hfb (cid, pos) Hfin) as (Hf4k & Hfceil). cbn [fst snd] in Hf4k, Hfceil.
    split; [lia|]. split; [unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL, kLowMemEnd in *; lia|].
    split.
    { intros x Hx. refine (proj2 (alx_client_img _ _ _ LAWS ly S Hp W mem md x HAR _)). right. left.
      exists cid, pos. split; [exact Hfin | lia]. }
    split; [right; lia|]. split.
    { intros x Hx. split; [right; split; [exact (FPv x Hx)|] | apply (proj1 (Hfpres x ltac:(lia)))].
      exists cid, pos. split; [exact Hfin | unfold in_zr, frame_rng; cbn [fst snd]; lia]. }
    intros a k Hin x Hx Hh. destruct (HDK a k Hin) as (Hab & Hk0).
    pose proof (sep_block_frame_x _ _ _ LAWS ly S Hp W mem md _ _ cid pos HAR Hab Hfin) as Hdj.
    unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite RQ in Hdj by lia. lia.
  - split; [lia|]. split; [unfold amem_range, kLowMemEnd in *; right; lia|].
    split.
    { intros x Hx Hi. pose proof (Hsegs x Hi) as Hlo. unfold kLowMemEnd in Hlo. lia. }
    split; [left; lia|]. split.
    { intros x Hx. split; [left; left; lia | apply Hepres; lia]. }
    intros a k Hin x Hx Hh. destruct (HDK a k Hin) as (Hab & Hk0).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & Hbceil & _).
    rewrite RQ in Hbceil by lia. lia. }
destruct HV as (HV4k & HVam & HVimg & HVsp & HVwr & HVhd).
assert (IGS : forall x, Exists (in_zr x) (@prh_pst prh_img_A) -> YG0d.in_img SEGS x).
{ intros x Hx. apply Exists_exists in Hx as (r & Hr & Hz). unfold in_zr in Hz.
  pose proof lit_br_pst_img as Hc. rewrite forallb_forall in Hc.
  exact (lit_in_img_rng SEGS (fst r) (snd r) (Hc r Hr) x Hz). }
rewrite lit_br_sigma.
pose proof (literal_x_holds_mnI (fx := fx) (rc := rc) (HL := HL) SK B (@prh_pst prh_img_A) ARx LAWS lit_br_palc lit_br_astrlen
  lit_br_abcmp) as LEAF.
unfold tliteral_leafXmn in LEAF.
change (@pa_segs _ literal_listing PIL) with SEGS in LEAF.
unfold LIT_STK, ESTACK in LEAF.
eapply SRr_mono.
{ apply (LEAF ((80 + 2 * 4096) + e) (spZ regs + e) [(q, q + 8); (v, v + 4)] ly S Hp W mem md [] ly S Hp W mem md 0
    regs q w ty v p text len tb cw slack).
  - exact (lit_br_init_W (80 + 2 * 4096) e [(q, q + 8); (v, v + 4)] ly S Hp W regs mem md ch HPRE He0 He16 Hetop Hepres).
  - exact Hra.
  - exact Hgp.
  - exact Htp.
  - exact H10.
  - exact H11.
  - exact H12.
  - exact H13.
  - exact Hal16.
  - lia.
  - lia.
  - exact Hq8.
  - lia.
  - unfold amem_range, kLowMemEnd in *. right. lia.
  - unfold YCbq.off_img_at. right. pose proof lit_br_hi as Hhi. lia.
  - left. exact Hqs.
  - intros x Hx. split; [left; lia | apply Hepres; lia].
  - exact Hqp.
  - exact Hqend.
  - exact (range_addressable_sub _ _ q 24 q 16 Hqra ltac:(lia) ltac:(lia)).
  - exact Htx0.
  - exact Hptx.
  - exact Htxl.
  - exact Hlen.
  - exact Gtx.
  - exact Hamt.
  - exact Hrat.
  - exact Hhut.
  - right. lia.
  - lia.
  - exact Hcw32.
  - exact Hw63.
  - exact Gw.
  - exact Hnz.
  - exact Hsl.
  - unfold amem_range, YGcfStr.amem_range8 in *. lia.
  - exact Hamw8c.
  - exact Hraw.
  - exact Hhuw.
  - exact Hwsp.
  - destruct lit_br_relro as [E1 E2]. rewrite E1, E2. exact HROD.
  - exact Hty.
  - exact Hv8.
  - exact HV4k.
  - exact HVam.
  - exact HVimg.
  - exact HVsp.
  - exact HVwr.
  - exact Hvra.
  - lia. }
intros W2 c2 _ HPOST. unfold tliteral_leaf_postXmn in HPOST.
destruct HPOST as (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2 & HRES & HMN).
unfold LIT_STK, ESTACK in HK2, HRES.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Kq8 : forall x, q + 8 <= x < q + 24 -> aview SEGS (w_H W) mem2 x = aview SEGS (w_H W) mem x).
{ intros x Hx. apply HK2; lia. }
assert (Ktx : forall x, text <= x < text + Z.of_nat (length tb) -> aview SEGS (w_H W) mem2 x = aview SEGS (w_H W) mem x).
{ intros x Hx. apply HK2; lia. }
assert (Kst : forall x, Exists (in_zr x) (@prh_pst prh_img_A) -> aview SEGS (w_H W) mem2 x = aview SEGS (w_H W) mem x).
{ intros x Hx. pose proof (IGS x Hx) as Hi. pose proof (Hsegs x Hi) as Hlo. unfold kLowMemEnd in Hlo.
  apply HK2; [lia | lia | lia | intros Hvx; exact (HVimg x Hvx Hi)]. }
assert (Khd : forall a k x, In (a, k) Lam -> a - 16 <= x < a - 8 -> aview SEGS (w_H W) mem2 x = aview SEGS (w_H W) mem x).
{ intros a k x Hin Hx. destruct (proj1 (Forall_forall _ _) HFA (a, k) Hin) as (Hk0 & Hab & _ & _ & _).
  cbn [fst snd] in Hk0, Hab. change (@cf_head CP) with 16 in Hab.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & Hb4k & Hbceil & _).
  assert (Rq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
  rewrite Rq in Hbceil.
  apply HK2; [lia | lia | lia | intros Hvx; exact (HVhd a k Hin x Hvx Hx)]. }
assert (Hrw2 : rd_rw SEGS (mrestrict (w_H W) mem2) q 24).
{ intros x Hx. apply (YCbq.apresent_writable SEGS). apply Hpres2. lia. }
assert (HLED2 : prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W mem2 Lam peak cnt fail ran most own).
{ destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & GR).
  split; [|split; [exact HND | split; [|exact HPM]]].
  - split; [eapply lit_br_val_keep; [intros x Hx; apply Kst; unfold prh_pst; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact G1]|].
    split; [eapply lit_br_val_keep; [intros x Hx; apply Kst; unfold prh_pst; apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact G2]|].
    split; [eapply lit_br_val_keep; [intros x Hx; apply Kst; unfold prh_pst; apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact G3]|].
    split; [eapply lit_br_val_keep; [intros x Hx; apply Kst; unfold prh_pst; apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact G4]|].
    split; [eapply lit_br_val_keep; [intros x Hx; apply Kst; unfold prh_pst; apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact G5]|].
    (* #102's two cells (prh_most / prh_own, prh_pst's 6th and 7th rows): kept as the five above *)
    split; [split; [eapply lit_br_val_keep; [intros x Hx; apply Kst; unfold prh_pst; apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact G6] | exact G6r]|].
    split; [split; [eapply lit_br_val_keep; [intros x Hx; apply Kst; unfold prh_pst; apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact G7] | exact G7r]|].
    exact GR.
  - apply Forall_forall. intros [a k] Hin. destruct (proj1 (Forall_forall _ _) HFA (a, k) Hin) as (Hk0 & Hab & HHp & Ha16 & Hhd).
    cbn [fst snd] in *. split; [exact Hk0|]. split; [exact Hab|]. split; [exact HHp|]. split; [exact Ha16|].
    change (@cf_head CP) with 16 in *.
    eapply lit_br_val_keep; [intros x Hx; apply (Khd a k x Hin); lia | exact Hhd]. }
unfold fpostWm, fpostW, fQmn. exists ly, S, Hp, regs2, mem2, md2, 0. cbv beta.
split; [reflexivity|]. split; [exact HJ2|].
split.
{ intros a Ha Hf. apply HK2; [lia | lia | |].
  - intros Hq'. apply Hf. exists (q, q + 8). split; [left; reflexivity | cbn [fst snd]; lia].
  - intros Hv'. apply Hf. exists (v, v + 4). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
split; [exact HP2|]. split; [|exact HMN].
split; [intros Hr; exact Hr|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HLED2|].
unfold rest_atR. destruct HRES as [(Hpt & R0 & QH & QV) | (Hpf & R0 & KM)].
- rewrite Hpt. split; [exact R0|]. split; [|exact QV].
  pose proof Hpt as Hpt'. apply lit_prefixb_nth in Hpt' as (Hl & _). rewrite length_skipn in Hl.
  split; [exact QH|]. split; [eapply lit_br_val_keep; [intros x Hx; apply Kq8; lia | exact Hqend]|].
  split; [eapply lit_br_val_keep; [intros x Hx; apply Kq8; lia | exact Hqd]|].
  split; [exact Hrw2|]. split; [exact Hq8|]. split; [exact Htx0|]. split; [exact Htxl|]. split; [lia|].
  split; [exact Hlen|]. split; [exact (lit_br_garr8_keep _ _ mem _ _ _ Ktx Gtx)|]. split; [exact Hqtx | exact Hd].
- rewrite Hpf. split; [exact R0|].
  pose proof HVam as HVam'. unfold amem_range, kLowMemEnd in HVam'.
  assert (KM' : forall x, spZ regs <= x < 2 ^ 47 \/ 0 <= x < spZ regs - (80 + 2 * 4096) -> aview SEGS (w_H W) mem2 x = aview SEGS (w_H W) mem x).
  { intros x Hx. apply KM; lia. }
  split.
  + split; [eapply lit_br_val_keep; [intros x Hx; apply KM'; lia | exact Hqp]|].
    split; [eapply lit_br_val_keep; [intros x Hx; apply KM'; lia | exact Hqend]|].
    split; [eapply lit_br_val_keep; [intros x Hx; apply KM'; lia | exact Hqd]|].
    split; [exact Hrw2|]. split; [exact Hq8|]. split; [exact Htx0|]. split; [exact Htxl|]. split; [exact Hptx|].
    split; [exact Hlen|]. split; [eapply lit_br_garr8_keep; [intros x Hx; apply KM'; lia | exact Gtx]|].
    split; [exact Hqtx | exact Hd].
  + intros a [Ha|Ha]; apply KM'; lia.
Qed.
End b.
Check literal_holds.
Print Assumptions literal_holds.
