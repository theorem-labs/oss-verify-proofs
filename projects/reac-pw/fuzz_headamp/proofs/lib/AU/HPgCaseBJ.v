(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 692 of its 736 lines of code are new or changed and 246 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v, with its module paths and module names changed; 639 of its 687 lines of code are new or changed and 688 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEntBCut.v at f1adc59eebf (its case-entry and
   join bridges eb_D_facts, eb_D_input, eb_D_keep, eb_cstr_kept, eb_D_img, eb_J_of, eb_J_post) for
   reac-pw/fuzz_headamp's image B: restated over lib/AU/HPgSeg.v's cuts hsu_cut_D / hsu_cut_J at image B's record
   headamp_himg_B, with image B's class-4 frame (1024 bytes, 116 shadow bytes), its e62 pod object at F+0x210,
   its real frame of 0x220 bytes and write range [R, R+0x198), image B's strings, globals and cells, and a join
   bridge for any case (its registers and real-frame cells as parameters) in place of role's cases 1/4/5/9 only. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the two bridges between
   lib/AU/HPgSeg.v's cut states at ent_build's case entries (hsu_cut_D, pcs hsu_pc_D: the nine table targets and
   case 9's 0x82004) and at the join J (hsu_cut_J, 0x82618), and the facts a walk of one case uses. Proves no
   function (kind: segment lemma). Every case piece of the image-B builder (W6a cases 2 and 3, W6b cases 1, 4, 5
   and 9, W6c cases 6, 7 and 8) goes hsu_cut_D -> its case block -> hsu_cut_J through these lemmas.

   THE STATE AT A CASE ENTRY (HPgSeg.hsu_L_D, image B's registers): s0 = S, s1 = R (x9) the real frame's base,
   s3 = shadow_addr F (x19), s11 = SHADOW_OFF (x27), s8 = the `v / 10` multiplier (x24), s6 = F + 0xe0 (x22),
   s9 = F + 0x20 (x25); a7 = c - 1 (x17), s2 = c (x18) the cursor after the kind byte, t1 = |r| + 1 (x6),
   s4 = |r| (x20) what is left after it, t2 = 10 (x7), a6 = 1 (x16), s7 = -8 (x23), a3 = the kind byte
   sign-extended (x13, not on case 9); the real-frame cells of HPgSeg.hsu_Kc and hsu_L_Dc (among them
   R+0x40 = F+0x220, R+0xe8 = -(F+0x219), R+0x118 = F+0x218, R+0x130 = F+0x210 = &e62, R+0x138 = pp+0x4000,
   R+0x148 = pp, R+0x150 = shadow_addr (pp+0x4000), R+0x158 = |es|); e62 = 104 zero bytes with its 13 shadow
   granules 0 (hsu_PJ = HPgMem.hmu_sh with e62 in scope).
   THE STATE AT J (HPgSeg.hsu_cut_J): a3 = the cursor after the pod (x13), t1 = what is left (x6),
   s2 = pp+0x4000 (x18), s4 = &e62 (x20), s7 = pp (x23), e62 = Layout.ent_mem of the pod; the registers of
   HPgSeg.hsu_Rc0 and every real-frame cell of hsu_L_Dc as at the case entry.

   cj_D_facts: the journal, the bounds of R, F and pp, e62 = 0^104 and its shadow, the frame's bytes present,
     rom_view at the cut (the registers and cells: cj_D_at over hsu_L_D).
   cj_D_input: the input bytes after the kind byte at the case entry.
   cj_D_keep: every image byte, and every shadow byte outside F's 116 shadow bytes, as at the segment's start.
   cj_D_img: image B's strings (hd_cstr), registered globals and 8-byte cells at the case entry.
   cj_J_of: hsu_cut_J at the join from the journal, the registers the case keeps or sets, the bytes it keeps
     (every byte outside the callees' stack below R, the real-frame cells ws it writes and e62), and e62.
   cj_J_post: the same from a case block's post (HPgSteps.hdu_blk_postE at 0x82618).
   cj_e62_tyszv: e62's 104 bytes from the three words a case stores (type, size, a 4-byte body) and the zero
     tail ent_build's memset left (cases 2, 3 and 4). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Spa.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0q YP03.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgSteps.
Import ListNotations.
(* the cut record's projections, with the segments implicit *)
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the frame's shadow at a case entry: e62's granules in scope, the rest the prologue's *)
Lemma cj_PJ : hsu_PJ headamp_himg_B = hmu_sh false false false false false true false false.
Proof. vm_compute. reflexivity. Qed.
Lemma cj_PJ_len : Z.of_nat (length (hsu_PJ headamp_himg_B)) = 116.
Proof. vm_compute. reflexivity. Qed.
Lemma cj_shA_len : Z.of_nat (length headamp_B_shA) = 116.
Proof. vm_compute. reflexivity. Qed.

(* the 8-byte real-frame cells of a case entry's list (HPgSeg.hsu_Kc and hsu_L_Dc): a case keeps them *)
Definition cj_cells : list Z :=
  [0x8; 0x10; 0x18; 0x20; 0x28; 0x30; 0x38; 0x40; 0x48; 0x50; 0x60; 0x68; 0x70; 0x78; 0xa0; 0xa8; 0xb0; 0xb8;
   0xc0; 0xc8; 0xd0; 0xd8; 0xe0; 0xe8; 0xf0; 0xf8; 0x100; 0x108; 0x118; 0x120; 0x130; 0x138; 0x148; 0x150;
   0x98; 0x88; 0x90; 0x128; 0x80; 0x140; 0x158].
(* the registers of hsu_Rc0, and sp, gp, tp: a case keeps them *)
Definition cj_kregs : list Z := [2; 3; 4; 8; 9; 19; 22; 24; 25; 27].
(* the real-frame cells ws a case writes: 8-aligned 8-byte cells inside M01's real-frame range [R, R+0x198)
   (HPgImgB hi_w1), none of them a cell of the case entry's list *)
Definition cj_ws_ok (ws : list Z) : bool :=
  forallb (fun o => (0 <=? o) && (o + 8 <=? 0x198) && (o mod 8 =? 0) && negb (existsb (Z.eqb o) cj_cells)) ws.
(* the bytes a case may change: its callees' stack below R, the cells ws and e62 *)
Definition cj_wr (R F : Z) (ws : list Z) : Z -> Prop :=
  fun a => (R - T_SEG_STK <= a < R) \/ Exists (fun o => R + o <= a < R + o + 8) ws \/
           (F + HSU_E62 <= a < F + HSU_E62 + 104).
(* the registers a case may change: none of cj_kregs *)
Definition cj_clob_ok (clob : list (bv 5)) : bool :=
  forallb (fun r : bv 5 => negb (existsb (Z.eqb (bv_unsigned r)) cj_kregs)) clob.

Lemma cj_ws_apart : forall ws R o i, cj_ws_ok ws = true -> In o cj_cells -> 0 <= i < 8 ->
  ~ Exists (fun o' => R + o' <= R + o + i < R + o' + 8) ws.
Proof.
  intros ws R o i Hws Ho Hi Hex. apply Exists_exists in Hex as (o' & Hin & Hr).
  unfold cj_ws_ok in Hws. rewrite forallb_forall in Hws. specialize (Hws o' Hin).
  apply andb_prop in Hws as [Hws Hn]. apply andb_prop in Hws as [Hws Hm]. apply andb_prop in Hws as [_ _].
  apply Z.eqb_eq in Hm. apply negb_true_iff in Hn.
  assert (Hmo : o mod 8 = 0).
  { unfold cj_cells in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [<-|Ho]; [reflexivity|]). destruct Ho. }
  cbv beta in Hr.
  pose proof (Z.div_mod o' 8 ltac:(lia)) as D1. pose proof (Z.div_mod o 8 ltac:(lia)) as D2.
  rewrite Hm in D1. rewrite Hmo in D2. set (q1 := o' / 8) in *. set (q2 := o / 8) in *.
  assert (E : o' = o) by lia. clear D1 D2 q1 q2. subst o'.
  assert (Ht : existsb (Z.eqb o) cj_cells = true)
    by (apply existsb_exists; exists o; split; [exact Ho | apply Z.eqb_refl]).
  rewrite Ht in Hn. discriminate Hn.
Qed.
Lemma cj_ws_range : forall ws o, cj_ws_ok ws = true -> In o ws -> 0 <= o /\ o + 8 <= 0x198.
Proof.
  intros ws o Hws Hin. unfold cj_ws_ok in Hws. rewrite forallb_forall in Hws. specialize (Hws o Hin).
  apply andb_prop in Hws as [Hws _]. apply andb_prop in Hws as [Hws _]. apply andb_prop in Hws as [H0 H1].
  apply Z.leb_le in H0. apply Z.leb_le in H1. lia.
Qed.
Lemma cj_clob_keep : forall clob (rg : Z), cj_clob_ok clob = true -> In rg cj_kregs -> ~ In (Z_to_bv 5 rg) clob.
Proof.
  intros clob rg Hc Hrg Hin. unfold cj_clob_ok in Hc. rewrite forallb_forall in Hc. specialize (Hc _ Hin).
  apply negb_true_iff in Hc.
  assert (Ht : existsb (Z.eqb (bv_unsigned (Z_to_bv 5 rg))) cj_kregs = true).
  { unfold cj_kregs in Hrg. cbn [In] in Hrg.
    repeat (destruct Hrg as [<-|Hrg]; [vm_compute; reflexivity|]). destruct Hrg. }
  rewrite Ht in Hc. discriminate Hc.
Qed.

(* the bytes [lo, hi) lie in one segment of the image *)
Definition cj_in_seg_b (lo hi : Z) : bool :=
  existsb (fun sg => (Z.of_N (seg_base sg) <=? lo) && (hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) rsegs.
Lemma cj_in_seg : forall lo hi a, cj_in_seg_b lo hi = true -> lo <= a < hi -> in_img rsegs a.
Proof.
  intros lo hi a Hb Ha. unfold cj_in_seg_b in Hb. apply existsb_exists in Hb as (sg & Hin & Hs).
  apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hin | lia].
Qed.
(* image B's strings with their NUL's 8-byte word, its globals and its cells lie in the image *)
Lemma cj_strs_in_img : forallb (fun s => cj_in_seg_b (fst s) (fst s + Z.of_nat (length (snd s)) + 8)) headamp_B_strs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cj_globs_in_img : forallb (fun g => cj_in_seg_b (fst g) (fst g + snd g)) headamp_B_globs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cj_cells_in_img : forallb (fun c => cj_in_seg_b (fst c) (fst c + 8)) headamp_B_cells = true.
Proof. vm_compute. reflexivity. Qed.

(* the first block's image is PP_SIZE bytes *)
Lemma cj_pc_len : forall sh ps es, hsu_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat -> (length ps <= 2)%nat ->
  Z.of_nat (length (pc_image (PbCut sh ps (Some es)))) = Layout.PP_SIZE.
Proof.
  intros sh ps es (Hsh & Hkv & Hall & Hps3) Hes Hes32 Hps2.
  assert (Hpv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [| exact Hkv]; intros kv [_ H]; exact H).
  unfold pc_image. apply length_pp_image.
  - destruct (pc_buf_len_open sh ps es Hpv Hall Hes) as [L _]. cbn [pc_shape pc_props pc_open]. lia.
  - unfold pc_ents. cbn [pc_props pc_open]. destruct (first_params ps) as [[iv|es']|] eqn:E; [cbn; lia | | lia].
    unfold first_params in E. destruct (find _ _) as [kv|] eqn:Fd; [|discriminate]. cbn in E. injection E as E.
    apply find_some in Fd as [Hin _]. rewrite Forall_forall in Hpv. specialize (Hpv kv Hin). rewrite E in Hpv. exact Hpv.
  - unfold pc_ents. cbn [pc_props pc_open]. destruct (first_params ps) as [[iv|es']|] eqn:E; [constructor | |].
    + unfold first_params in E. destruct (find _ _) as [kv|] eqn:Fd; [|discriminate]. cbn in E. injection E as E.
      apply find_some in Fd as [Hin _]. apply all_ents_Forall in Hall. rewrite Forall_forall in Hall.
      specialize (Hall kv Hin). rewrite E in Hall. cbn beta iota in Hall.
      eapply Forall_impl; [| exact Hall]. intros e' (_ & Hb & Hs). lia.
    + eapply Forall_impl; [| exact Hes]. intros e' (_ & Hb & Hs). lia.
Qed.

(* the shadow hull of an application range below 2^47 lies in the shadow band *)
Lemma cj_hull_band : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 - 1 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> kLowMemEnd <= s < kHighMemBeg.
Proof.
  intros x n s H0 Hn Hx Hs. unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg in *.
  assert (A1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (A2 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  assert (A3 : 0 <= (x + n - 1) / 8) by (apply Z.div_pos; lia).
  rewrite (Z.add_comm 0x7fff8000 (x / 8)), (Z.add_comm 0x7fff8000 ((x + n - 1) / 8)) in Hs.
  replace 0x7fff8000 with (0xffff000 * 8) in Hs by reflexivity.
  rewrite !Z.div_add in Hs by lia.
  assert (B1 : 0 <= x / 8 / 8) by (apply Z.div_pos; lia).
  assert (B2 : (x + n - 1) / 8 / 8 < 2 ^ 41) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma cj_suffix_trans : forall (rest rr r' : list byte), hsu_suffix rest rr -> is_rest r' rr -> hsu_suffix rest r'.
Proof.
  intros rest rr r' (j & Hj & Erj) (k & Ek). subst rr r'. rewrite skipn_skipn.
  destruct (Nat.le_gt_cases (k + j) (length rest)) as [Hle|Hgt].
  - exists (k + j)%nat. split; [exact Hle | reflexivity].
  - exists (length rest). split; [lia|]. rewrite !skipn_all2 by (rewrite ?length_skipn; lia). reflexivity.
Qed.

(* e62's 104 bytes from a case's three stored words (type, size, a 4-byte body) and the zero tail *)
Lemma cj_e62_tyszv : forall (H : word -> bool) mem a ty v,
  val_mem rsegs (mrestrict H mem) a 4 ty -> val_mem rsegs (mrestrict H mem) (a + 4) 4 4 ->
  val_mem rsegs (mrestrict H mem) (a + 8) 4 v ->
  (forall i, 0 <= i < 92 -> aview rsegs H mem (a + 12 + i) = Some 0) ->
  garr8 rsegs (mrestrict H mem) a (hd_zbytes (ent_mem (Ent ty 4 (le32 v)))).
Proof.
  intros H mem a ty v V0 V4 V8 Vz.
  change (garr8 rsegs (mrestrict H mem) a (hd_zbytes (ent_mem (Ent ty 4 (le32 v)))))
    with (hm_bytes rsegs H mem a (ent_mem (Ent ty 4 (le32 v)))).
  unfold ent_mem. cbn [e_type e_size e_body]. unfold le32. rewrite length_Z_to_le_bytes.
  apply hm_bytes_app. split; [apply hm_bytes_of_val; exact V0|].
  rewrite length_Z_to_le_bytes. change (Z.of_nat 4) with 4.
  apply hm_bytes_app. split; [apply hm_bytes_of_val; exact V4|].
  rewrite length_Z_to_le_bytes. change (Z.of_nat 4) with 4. replace (a + 4 + 4) with (a + 8) by lia.
  apply hm_bytes_app. split; [apply hm_bytes_of_val; exact V8|].
  rewrite length_Z_to_le_bytes. change (Z.of_nat 4) with 4. replace (a + 8 + 4) with (a + 12) by lia.
  apply (proj2 (hm_bytes_aview rsegs H mem (a + 12) (zeros (96 - 4)))). intros i Hi.
  unfold zeros in *. rewrite repeat_length in Hi. unfold NUL. rewrite nth_repeat.
  rewrite (Vz (Z.of_nat i) ltac:(lia)). reflexivity.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

Lemma cj_at : forall H mem regs e (L : list (hd_loc * Z)) l v,
  hsu_at rsegs H mem regs e L -> In (l, v) L -> hd_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HA Hin. exact (proj1 (Forall_forall _ _) HA (l, v) Hin). Qed.

Lemma cj_frame_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos Hle. unfold frame_addr. destruct Hle as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. Qed.

Lemma cj_val_small : forall H mem a v, 0 <= v < 2 ^ 64 ->
  val_mem rsegs (mrestrict H mem) a 8 (v mod 2 ^ 64) -> val_mem rsegs (mrestrict H mem) a 8 v.
Proof. intros H mem a v Hv V. rewrite Z.mod_small in V by lia. exact V. Qed.
Lemma cj_val_mod : forall H mem a v, 0 <= v < 2 ^ 64 ->
  val_mem rsegs (mrestrict H mem) a 8 v -> val_mem rsegs (mrestrict H mem) a 8 (v mod 2 ^ 64).
Proof. intros H mem a v Hv V. rewrite Z.mod_small by lia. exact V. Qed.

(* a location of a case entry's list holds its value *)
Lemma cj_D_at : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 l v,
  hsu_cut_D rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  In (l, v) (hsu_L_D rsegs cx sh np ps cnt es rest r kd) ->
  hd_at rsegs (w_H W2) mem2 regs2 (x_e cx) l v.
Proof. intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 l v HD Hin. exact (cj_at _ _ _ _ _ l v (proj1 (proj2 HD)) Hin). Qed.

(* ============================== the case entry ============================== *)
Lemma cj_D_facts : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  hsu_start_M01 rsegs B headamp_himg_B cx rest ->
  hsu_cut_D rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem2 md2 (x_k cx) /\
  getr regs2 2 = w64 (e_R (x_e cx)) /\ getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
  (* bounds *)
  alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ e_R (x_e cx) + 0x220 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  e_R (x_e cx) mod 32 = 0 /\ x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK /\
  In (4, x_pos cx) (x_own cx) /\ In (4, x_pos cx) (frames S2) /\ e_F (x_e cx) = frame_addr ly2 4 (x_pos cx) /\
  4096 <= e_F (x_e cx) /\ e_F (x_e cx) + 1024 <= alloc_ceiling /\ e_F (x_e cx) mod 32 = 0 /\
  in_app (e_F (x_e cx)) 1024 /\
  In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2) /\ 4096 <= e_pp (x_e cx) /\
  e_pp (x_e cx) + Layout.PP_SIZE <= alloc_ceiling /\ zdisjoint (e_pp (x_e cx), Layout.PP_SIZE) (e_F (x_e cx), 1024) /\
  1 <= hsu_cur rsegs cx rest r /\ hsu_cur rsegs cx rest r + Z.of_nat (length r) <= 2 ^ 47 - 1 /\
  (* e62, the frame, the stack window *)
  (forall i, 0 <= i < 104 -> mbyte rsegs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + HSU_E62 + i) = Some (Z_to_bv 8 0)) /\
  (forall o, 0 <= o < 1024 -> apresent (w_H W2) mem2 (e_F (x_e cx) + o)) /\
  range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_F (x_e cx) + HSU_E62) 104 /\
  (forall a, x_sp0 cx - x_STK cx <= a < x_sp0 cx -> apresent (w_H W2) mem2 a) /\
  hd_fsh rsegs (w_H W2) mem2 (e_F (x_e cx)) (hsu_PJ headamp_himg_B) /\
  rom_view rsegs W2 mem2.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof (@asan_consts rc) as (Hceil & _).
  destruct HST as (HPRE & HL1 & Hlen & HIN).
  destruct HPRE as (HJc & Hnev & HR2 & Hgp & Htp & ES & ER32 & ERS & ESTK & Hown & EF & Hfsh0 & Hcap & Hnull
    & Haro & Hglobs & Hrz & Hstrs & Hcells & Hguard & Hrom & Hfresh).
  destruct Hfresh as (Hpp0 & Hppb & Hnpp).
  destruct HD as (HPB & HAT & HFSH & HPP & HE0 & Hsrr & Hfu & Hkd & Hrr).
  destruct HPB as (HCORE & HIN' & Hsr & Hsrr' & Hwf & Hlen' & Hps & Htie & Hsh & Hnp & Hlp & Hnp3 & Hsh7 & Hps2 & Hcnt
    & Hesw & Hes32 & Hesc).
  destruct HCORE as (HJ & Hspr & Hfr & Hperm & Hio & Hmo & Hkept).
  pose proof HJ as (HAR & Hlyle & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hc1 & Hc2 & Hc3 & Hc4 & _).
  pose proof HJc as (_ & Hlyle_c & _).
  cbn [hi_cid hi_rsz headamp_himg_B] in Hown, EF, ERS.
  assert (HTS : T_SEG_STK = 16384) by reflexivity.
  assert (HRb : alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ e_R (x_e cx) + 0x220 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47)
    by (rewrite HTS in *; lia).
  assert (HspR : spZ (x_regs cx) = e_R (x_e cx)).
  { unfold spZ. rewrite HR2. unfold w64. apply unsigned_lit_small. rewrite HTS in HRb. lia. }
  (* the frame *)
  assert (HinF : In (4, x_pos cx) (frames S2)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  assert (EF2 : e_F (x_e cx) = frame_addr ly2 4 (x_pos cx)).
  { rewrite EF, (cj_frame_addr_le _ _ _ 4 (x_pos cx) Hlyle_c), (cj_frame_addr_le _ _ _ 4 (x_pos cx) Hlyle). reflexivity. }
  destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) HAR HinF) as (HF1 & HF2 & HF3).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 4 (x_pos cx) HAR HinF) as (HF32 & _ & HFp & _).
  rewrite <- EF2 in HF1, HF2, HF3, HF32, HFp. change (fs_frame_bytes 4) with 1024 in HF1, HF2, HF3, HFp.
  (* pp *)
  assert (Hpp2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
    by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppb]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp2) as (_ & Hp1 & Hp2 & _).
  assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
  rewrite Hrq in Hp2.
  pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ 4 (x_pos cx) HAR Hpp2 HinF) as Hsep.
  rewrite Hrq, <- EF2 in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
  (* the cursor *)
  destruct HIN as (Hel & Hgar & Hra & Hhull & Hamr & Hsrc0 & Hsrc63 & Hdis).
  destruct Hsr as (j & Hj & Er).
  assert (Hlr : length r = (length rest - j)%nat) by (rewrite Er, length_skipn; reflexivity).
  assert (Hcur : hsu_cur rsegs cx rest r = e_src (x_e cx) + Z.of_nat j) by (unfold hsu_cur; rewrite Hlr; lia).
  assert (Hhi : e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 47 - 1).
  { unfold amem_range in Hamr.
    unfold kHighMemBeg, kHighMemEnd, kLowMemEnd in Hamr. lia. }
  (* e62 *)
  assert (HF8 : e_F (x_e cx) mod 8 = 0).
  { apply (proj1 (Z.mod_divide (e_F (x_e cx)) 32 ltac:(discriminate))) in HF32. destruct HF32 as [c Hc]. rewrite Hc.
    replace (c * 32) with ((c * 4) * 8) by ring. apply Z_mod_mult. }
  assert (Ez : forall i, 0 <= i < 104 ->
    mbyte rsegs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + HSU_E62 + i) = Some (Z_to_bv 8 0)).
  { intros i Hi. apply hm_aview_mbyte.
    change (hsu_obj_at rsegs cx W2 mem2 HSU_E62 (zeros 104))
      with (hm_bytes rsegs (w_H W2) mem2 (e_F (x_e cx) + HSU_E62) (zeros 104)) in HE0.
    pose proof (proj1 (hm_bytes_aview rsegs (w_H W2) mem2 _ (zeros 104)) HE0 (Z.to_nat i)
      ltac:(unfold zeros; rewrite repeat_length; lia)) as V.
    rewrite Z2Nat.id in V by lia. rewrite V. unfold zeros, NUL. rewrite nth_repeat. reflexivity. }
  assert (HraE : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_F (x_e cx) + HSU_E62) 104).
  { unfold hsu_fsh_at in HFSH. rewrite cj_PJ in HFSH.
    pose proof (hmu_B_ra_e62 rsegs (w_H W2) mem2 _ false false false false false false false 0 104 HFSH HF8
      ltac:(lia) ltac:(lia)) as X.
    unfold HMU_E62 in X. unfold HSU_E62. rewrite Z.add_0_r in X. exact X. }
  (* rom_view at the cut: a read-only byte lies outside the stack below R and outside the segment's writes *)
  assert (HromD : rom_view rsegs W2 mem2).
  { intros a Ha. rewrite <- (Hrom a Ha).
    destruct Ha as (sg & Hsg & _ & Hr). assert (Himg : in_img rsegs a) by (exists sg; split; [exact Hsg | lia]).
    pose proof (img_segs_low a Himg) as Hlow.
    unfold kLowMemEnd in Hlow.
    apply Hkept; [lia | rewrite HspR; rewrite HTS in HRb; lia |].
    unfold hsu_E1. intros [Hw | Hw]; [| exact (blk_img rsegs B LAWS _ _ _ _ _ _ _ a HAR Hpp2 ltac:(rewrite Hrq; lia) Himg)].
    unfold hd_inw in Hw. cbn [hi_w1 headamp_himg_B] in Hw.
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { apply (frm_img rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) a HAR HinF); [| exact Himg].
      rewrite <- EF2. change (fs_frame_bytes 4) with 1024. lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { unfold shadow_addr, SHADOW_OFF in Hw. pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)). lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [rewrite HTS in HRb; lia|].
    apply Exists_nil in Hw. exact Hw. }
  split; [exact HJ|].
  split; [exact (eq_trans (Hspr 2 ltac:(lia)) HR2)|].
  split; [exact (eq_trans (Hspr 3 ltac:(lia)) Hgp)|].
  split; [exact (eq_trans (Hspr 4 ltac:(lia)) Htp)|].
  split; [exact (proj1 HRb)|]. split; [exact (proj1 (proj2 HRb))|]. split; [exact (proj2 (proj2 HRb))|].
  split; [exact ER32|]. split; [exact ESTK|].
  split; [exact Hown|]. split; [exact HinF|]. split; [exact EF2|].
  split; [exact HF1|]. split; [exact HF2|]. split; [exact HF32|]. split; [exact HF3|].
  split; [exact Hpp2|]. split; [exact Hp1|]. split; [exact Hp2|]. split; [exact Hsep|].
  split; [rewrite Hcur; lia|]. split; [rewrite Hcur, Hlr; lia|].
  split; [exact Ez|].
  split; [intros o Ho; exact (proj1 (HFp (e_F (x_e cx) + o) ltac:(lia)))|].
  split; [exact HraE|].
  split; [exact Hpres|].
  split; [exact HFSH|].
  exact HromD.
Qed.

Ltac cj_facts HST HD :=
  let H := fresh "HDF" in
  pose proof (cj_D_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HST HD) as H;
  destruct H as (HJ & R2 & R3 & R4 & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp
    & Hpp & Hpp1 & Hpp2 & Hsep & Hc1 & Hc2 & Ez & HFp & HraE & Hpres & HFSHD & HromD).

(* ============================== the input at the case entry ============================== *)
Lemma cj_D_input : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  hsu_start_M01 rsegs B headamp_himg_B cx rest ->
  hsu_cut_D rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  garr8 rsegs (mrestrict (w_H W2) mem2) (hsu_cur rsegs cx rest r) (hd_zbytes r) /\
  range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (hsu_cur rsegs cx rest r) (Z.of_nat (length r)) /\
  (0 < Z.of_nat (length r) -> shadow_hull_vis (aview rsegs (w_H W2) mem2) (hsu_cur rsegs cx rest r) (Z.of_nat (length r))) /\
  amem_range (hsu_cur rsegs cx rest r) (Z.of_nat (length r)) /\
  (forall a, hsu_cur rsegs cx rest r <= a < hsu_cur rsegs cx rest r + Z.of_nat (length r) ->
     ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx) + 0x198) /\ ~ (e_F (x_e cx) + 0x20 <= a < e_F (x_e cx) + 0x278) /\
     ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE)).
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof (@asan_consts rc) as (Hceil & _ & EHB & EHE & ELE).
  cj_facts HST HD.
  destruct HST as (HPRE & _ & _ & HIN).
  destruct HPRE as (HJc & _ & HR2 & _ & _ & _ & _ & _ & _ & _ & _ & Hfsh0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfresh).
  destruct Hfresh as (_ & Hppb & _).
  destruct HD as (HPB & _). destruct HPB as (HCORE & _ & Hsr & _).
  destruct HCORE as (_ & _ & _ & _ & _ & _ & Hkept).
  destruct HIN as (Hel & Hgar & Hra & Hhull & Hamr & Hsrc0 & Hsrc63 & Hdis).
  destruct Hsr as (j & Hj & Er).
  assert (HTS : T_SEG_STK = 16384) by reflexivity.
  assert (Hlr : length r = (length rest - j)%nat) by (rewrite Er, length_skipn; reflexivity).
  assert (Hcur : hsu_cur rsegs cx rest r = e_src (x_e cx) + Z.of_nat j) by (unfold hsu_cur; rewrite Hlr; lia).
  assert (Hhi : e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 47 - 1).
  { unfold amem_range in Hamr. unfold kHighMemBeg, kHighMemEnd, kLowMemEnd in Hamr. lia. }
  assert (HspR : spZ (x_regs cx) = e_R (x_e cx)).
  { unfold spZ. rewrite HR2. unfold w64. apply unsigned_lit_small. rewrite HTS in BR1. lia. }
  (* the bytes the walk may have changed since the segment's start *)
  set (Wr := fun a => ~ (0 <= a < 2 ^ 64) \/ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) \/
    hsu_E1 rsegs headamp_himg_B cx a).
  assert (KE : forall x, ~ Wr x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W cx)) (x_memc cx) x).
  { intros x Hx. unfold Wr in Hx. cbv beta in Hx.
    destruct (Z_le_gt_dec 0 x) as [X0 | X0]; [| exfalso; apply Hx; left; lia].
    destruct (Z_lt_ge_dec x (2 ^ 64)) as [X1 | X1]; [| exfalso; apply Hx; left; lia].
    apply Hkept; [lia | rewrite HspR; intros X; apply Hx; right; left; exact X | intros X; apply Hx; right; right; exact X]. }
  pose proof HJc as (HARc & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppb) as (_ & _ & _ & Hppapp & _).
  change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hppapp.
  assert (HFE : in_app (e_F (x_e cx) + 0x20) 0x258) by (apply (in_app_sub (e_F (x_e cx)) 1024); [exact HFapp | lia | lia | lia]).
  (* a shadow byte of an input byte avoids everything the segment may have written *)
  assert (SHW : forall x, e_src (x_e cx) <= x < e_src (x_e cx) + e_left (x_e cx) -> ~ Wr (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as Hb.
    unfold kLowMemEnd, kHighMemBeg in Hb.
    intros [Hw | [Hw | Hw]]; [lia | rewrite HTS in *; lia |].
    destruct Hw as [Hw | Hw].
    - unfold hd_inw in Hw. cbn [hi_w1 headamp_himg_B] in Hw.
      apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
      { exact (hm_shadow_not_app x _ _ ltac:(unfold kHighMemEnd; lia) HFE ltac:(lia)). }
      apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
      { cbn [hi_shA headamp_himg_B] in Hfsh0.
        pose proof (hm_ra_not_fsh rsegs _ _ _ _ _ _ Hra Hfsh0 hmu_sh_P0_big x Hx) as X.
        rewrite cj_shA_len in X. exact (X ltac:(lia)). }
      apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [rewrite HTS in *; lia|].
      apply Exists_nil in Hw. exact Hw.
    - exact (hm_shadow_not_app x _ _ ltac:(unfold kHighMemEnd; lia) Hppapp Hw). }
  split.
  { (* the bytes *)
    assert (B0 : hm_bytes rsegs (w_H (x_W cx)) (x_memc cx) (e_src (x_e cx)) rest) by exact Hgar.
    pose proof (hm_bytes_slice rsegs _ _ _ rest j (length rest - j) B0 ltac:(lia)) as B1.
    unfold hm_slice in B1. rewrite firstn_all2 in B1 by (rewrite length_skipn; lia). rewrite <- Er, <- Hcur in B1.
    change (garr8 rsegs (mrestrict (w_H W2) mem2) (hsu_cur rsegs cx rest r) (hd_zbytes r))
      with (hm_bytes rsegs (w_H W2) mem2 (hsu_cur rsegs cx rest r) r).
    refine (hm_bytes_kept_wr rsegs Wr _ _ _ _ _ r B1 KE _).
    intros x Hx. rewrite Hlr in Hx. destruct (Hdis x ltac:(lia)) as (D1 & D2 & D3).
    unfold Wr, hsu_E1. intros [Hw | [Hw | [Hw | Hw]]]; [lia | exact (D1 Hw) | exact (D2 Hw) | exact (D3 Hw)]. }
  split.
  { (* the shadow *)
    apply (hm_ra_kept_wr rsegs Wr (w_H (x_W cx)) (x_memc cx)); [| exact KE |].
    + apply (range_addressable_sub _ _ _ _ _ _ Hra); lia.
    + intros x Hx. apply SHW. lia. }
  split.
  { (* the shadow hull *)
    intros Hn. apply (hm_hull_kept rsegs (w_H (x_W cx)) (x_memc cx)).
    + apply (hm_hull_sub _ _ _ _ _ (Hhull ltac:(lia))); lia.
    + intros s Hs Hns.
      pose proof (cj_hull_band (hsu_cur rsegs cx rest r) (Z.of_nat (length r)) s ltac:(lia) Hn ltac:(lia) Hs) as Hb.
      unfold kLowMemEnd, kHighMemBeg in Hb.
      destruct (Z_lt_le_dec s (shadow_addr (e_F (x_e cx)))) as [Hs1 | Hs1];
        [| destruct (Z_lt_le_dec s (shadow_addr (e_F (x_e cx)) + 116)) as [Hs2 | Hs2]].
      2: { replace s with (shadow_addr (e_F (x_e cx)) + (s - shadow_addr (e_F (x_e cx)))) by lia.
        rewrite (HFSHD (s - shadow_addr (e_F (x_e cx))) ltac:(rewrite cj_PJ_len; lia)). discriminate. }
      all: rewrite KE; [exact Hns|].
      all: intros [Hw | [Hw | [Hw | Hw]]]; [lia | rewrite HTS in *; lia | |
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hppapp; lia].
      all: unfold hd_inw in Hw; cbn [hi_w1 headamp_himg_B] in Hw.
      all: apply Exists_cons in Hw; destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw;
        [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFE; lia |].
      all: apply Exists_cons in Hw; destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [lia|].
      all: apply Exists_cons in Hw; destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [rewrite HTS in *; lia|].
      all: apply Exists_nil in Hw; exact Hw. }
  split.
  - unfold amem_range in *. lia.
  - intros a Ha. destruct (Hdis a ltac:(lia)) as (D1 & D2 & D3). split; [| split; [| exact D3]].
    + intros Hx. apply D2. unfold hd_inw. cbn [hi_w1 headamp_himg_B].
      apply Exists_cons. right. apply Exists_cons. right. apply Exists_cons. left. cbn [fst snd hd_xv].
      destruct (Z_lt_le_dec a (e_R (x_e cx))) as [Hl|Hl]; [exfalso; apply D1; lia | lia].
    + intros Hx. apply D2. unfold hd_inw. cbn [hi_w1 headamp_himg_B]. apply Exists_cons. left. cbn [fst snd hd_xv]. lia.
Qed.

(* ============================== what the walk kept since the segment's start ============================== *)
Lemma cj_D_keep : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  hsu_start_M01 rsegs B headamp_himg_B cx rest ->
  hsu_cut_D rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  (forall a, in_img rsegs a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a) /\
  (forall s, kLowMemEnd <= s < kHighMemBeg ->
     ~ (shadow_addr (e_F (x_e cx)) <= s < shadow_addr (e_F (x_e cx)) + 116) ->
     aview rsegs (w_H W2) mem2 s = aview rsegs (w_H (x_W cx)) (x_memc cx) s).
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof (@asan_consts rc) as (Hceil & _ & EHB & EHE & ELE).
  cj_facts HST HD.
  destruct HST as (HPRE & _ & _ & _).
  destruct HPRE as (_ & _ & HR2 & _).
  destruct HD as (HPB & _). destruct HPB as (HCORE & _).
  destruct HCORE as (_ & _ & _ & _ & _ & _ & Hkept).
  pose proof HJ as (HAR & _).
  assert (HTS : T_SEG_STK = 16384) by reflexivity. rewrite HTS in BR1.
  assert (HspR : spZ (x_regs cx) = e_R (x_e cx)).
  { unfold spZ. rewrite HR2. unfold w64. apply unsigned_lit_small. lia. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (_ & _ & _ & Hppapp & _).
  change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hppapp.
  split.
  - intros a Himg. pose proof (img_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow.
    apply Hkept; [lia | rewrite HspR, HTS; lia |].
    unfold hsu_E1. intros [Hw | Hw].
    2: { apply (blk_img rsegs B LAWS _ _ _ _ _ _ _ a HAR Hpp); [| exact Himg].
         change (req_size Layout.PP_SIZE) with Layout.PP_SIZE. lia. }
    unfold hd_inw in Hw. cbn [hi_w1 headamp_himg_B] in Hw.
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { apply (frm_img rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) a HAR HinF); [| exact Himg].
      rewrite <- EF2. change (fs_frame_bytes 4) with 1024. lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { unfold shadow_addr, SHADOW_OFF in Hw. pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)). lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [lia|].
    apply Exists_nil in Hw. exact Hw.
  - intros s Hs HnF. unfold kLowMemEnd, kHighMemBeg in Hs.
    apply Hkept; [lia | rewrite HspR, HTS; lia |].
    unfold hsu_E1. intros [Hw | Hw].
    2: { unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, Layout.PP_SIZE in Hppapp.
         unfold Layout.PP_SIZE in Hw. lia. }
    unfold hd_inw in Hw. cbn [hi_w1 headamp_himg_B] in Hw.
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw.
    { unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia. }
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [lia|].
    apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; cbn [fst snd hd_xv] in Hw; [lia|].
    apply Exists_nil in Hw. exact Hw.
Qed.

(* A string of the image (hd_cstr) whose bytes and NUL word lie in the image, at a later state: its bytes, its NUL
   and its NUL word's tail are image bytes (kept); the shadow bytes of its bytes are outside F's shadow bytes (at
   the earlier state they mark the string usable, and the prologue's pattern marks no byte of F usable); a shadow
   byte of its hull is one of F's shadow bytes (present at the later state) or kept. *)
Lemma cj_cstr_kept : forall H mem H' mem' F pat a s,
  hd_cstr rsegs H mem a s ->
  (forall x, a <= x < a + Z.of_nat (length s) + 8 -> in_img rsegs x) ->
  hd_fsh rsegs H mem F headamp_B_shA -> hd_fsh rsegs H' mem' F pat -> Z.of_nat (length pat) = 116 ->
  (forall x, in_img rsegs x -> aview rsegs H' mem' x = aview rsegs H mem x) ->
  (forall u, kLowMemEnd <= u < kHighMemBeg -> ~ (shadow_addr F <= u < shadow_addr F + 116) ->
     aview rsegs H' mem' u = aview rsegs H mem u) ->
  hd_cstr rsegs H' mem' a s.
Proof.
  intros H mem H' mem' F pat a s (Hb & Hn & Hf & Ha0 & Ha63 & Himg & Ham & Hra & Hhull & Htl) Hseg P0 PJ PJlen K1 K2.
  pose proof (@asan_consts rc) as (_ & _ & EHB & EHE & ELE).
  assert (Hlow : forall i, 0 <= i <= Z.of_nat (length s) -> 0 <= a + i < kLowMemEnd)
    by (intros i Hi; exact (img_segs_low _ (Himg i Hi))).
  pose proof (Hlow (Z.of_nat (length s)) ltac:(lia)) as Hend. unfold kLowMemEnd in Hend, Hlow.
  split; [intros i Hi; rewrite K1 by (apply Himg; lia); exact (Hb i Hi)|].
  split; [rewrite K1 by (apply Himg; lia); exact Hn|].
  do 5 (split; [assumption|]).
  split.
  - apply (hm_ra_kept rsegs H mem); [exact Hra|]. intros x Hx.
    pose proof (Hlow (x - a) ltac:(lia)) as Hx'.
    pose proof (hm_ra_not_fsh rsegs H mem F headamp_B_shA a _ Hra P0 hmu_sh_P0_big x Hx) as HnF.
    rewrite cj_shA_len in HnF.
    apply K2; [pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as X; exact X
              | exact HnF].
  - split.
    + apply (hm_hull_kept rsegs H mem); [exact Hhull|]. intros u Hu Hne.
      pose proof (cj_hull_band a (Z.of_nat (length s) + 1) u ltac:(lia) ltac:(lia) ltac:(lia) Hu) as Hband.
      destruct (Z_lt_le_dec u (shadow_addr F)) as [Hu1 | Hu1];
        [| destruct (Z_lt_le_dec u (shadow_addr F + 116)) as [Hu2 | Hu2]].
      2: { replace u with (shadow_addr F + (u - shadow_addr F)) by lia.
           rewrite (PJ (u - shadow_addr F) ltac:(rewrite PJlen; lia)). discriminate. }
      all: rewrite K2; [exact Hne | exact Hband | lia].
    + intros x Hx. rewrite K1; [exact (Htl x Hx)|]. apply Hseg.
      pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)). lia.
Qed.

(* ============================== what a case reads of the image ============================== *)
Lemma cj_D_img : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  hsu_start_M01 rsegs B headamp_himg_B cx rest ->
  hsu_cut_D rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  (forall a s, In (a, s) headamp_B_strs -> hd_cstr rsegs (w_H W2) mem2 a s) /\
  (forall a n, In (a, n) headamp_B_globs -> range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF a n) /\
  (forall a v, In (a, v) headamp_B_cells -> val_mem rsegs (mrestrict (w_H W2) mem2) a 8 v).
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof (@asan_consts rc) as (_ & _ & EHB & EHE & ELE).
  pose proof (cj_D_keep cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as (K1 & K2).
  pose proof HD as (_ & _ & HFSH & _). unfold hsu_fsh_at in HFSH.
  destruct HST as (HPRE & _).
  destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfsh0 & _ & _ & _ & Hglobs & _ & Hstrs & Hcells & _).
  cbn [hi_shA hi_globs hi_strs hi_cells headamp_himg_B] in Hfsh0, Hglobs, Hstrs, Hcells.
  split; [| split].
  - intros a s Hin.
    assert (Hseg : forall x, a <= x < a + Z.of_nat (length s) + 8 -> in_img rsegs x).
    { intros x Hx. pose proof (proj1 (forallb_forall _ _) cj_strs_in_img (a, s) Hin) as Hb. cbn [fst snd] in Hb.
      exact (cj_in_seg _ _ x Hb Hx). }
    apply (cj_cstr_kept (w_H (x_W cx)) (x_memc cx) (w_H W2) mem2 (e_F (x_e cx)) (hsu_PJ headamp_himg_B) a s).
    + exact (proj1 (Forall_forall _ _) Hstrs (a, s) Hin).
    + exact Hseg.
    + exact Hfsh0.
    + exact HFSH.
    + exact cj_PJ_len.
    + exact K1.
    + exact K2.
  - intros a n Hin.
    assert (Hseg : forall x, a <= x < a + n -> in_img rsegs x).
    { intros x Hx. pose proof (proj1 (forallb_forall _ _) cj_globs_in_img (a, n) Hin) as Hb. cbn [fst snd] in Hb.
      exact (cj_in_seg _ _ x Hb Hx). }
    pose proof (proj1 (Forall_forall _ _) Hglobs (a, n) Hin) as Hra. cbn [fst snd] in Hra.
    apply (hm_ra_kept rsegs (w_H (x_W cx)) (x_memc cx)); [exact Hra|]. intros x Hx.
    pose proof (img_segs_low x (Hseg x Hx)) as Hlow. unfold kLowMemEnd in Hlow.
    apply K2.
    + pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as X. exact X.
    + pose proof (hm_ra_not_fsh rsegs _ _ _ _ a n Hra Hfsh0 hmu_sh_P0_big x Hx) as HnF.
      rewrite cj_shA_len in HnF. exact HnF.
  - intros a v Hin.
    assert (Hseg : forall x, a <= x < a + 8 -> in_img rsegs x).
    { intros x Hx. pose proof (proj1 (forallb_forall _ _) cj_cells_in_img (a, v) Hin) as Hb. cbn [fst snd] in Hb.
      exact (cj_in_seg _ _ x Hb Hx). }
    unfold hd_ro_cells in Hcells.
    pose proof (proj1 (Forall_forall _ _) Hcells _ Hin) as V0. cbn [fst snd] in V0.
    apply hm_val_of_bytes. apply (hm_bytes_kept rsegs (w_H (x_W cx)) (x_memc cx)).
    { apply hm_bytes_of_val. exact V0. }
    intros x Hx. rewrite length_Z_to_le_bytes in Hx. apply K1. apply Hseg. lia.
Qed.

(* ============================== the join ============================== *)
(* the locations of hsu_L_Dc: a register of hsu_Rc0 or a real-frame cell of cj_cells *)
Lemma cj_Dc_locs : forall (cx : hsu_scx rsegs) sh np ps cnt es l v, In (l, v) (hsu_L_Dc rsegs cx sh np ps cnt es) ->
  (exists rg, l = LReg rg /\ In rg cj_kregs) \/ (exists o, l = LCell XR o /\ In o cj_cells).
Proof.
  intros cx sh np ps cnt es l v Hin. cbv [hsu_L_Dc hsu_Rc0 hsu_Kc app] in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin];
    [injection Hin as <- _;
     first [left; eexists; split; [reflexivity | cbv [cj_kregs In]; tauto]
           | right; eexists; split; [reflexivity | cbv [cj_cells In]; tauto]] |]).
  destruct Hin.
Qed.

Lemma cj_J_of : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 ed r' ws,
  hsu_start_M01 rsegs B headamp_himg_B cx rest ->
  hsu_cut_D rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  ameter_laws MT -> cj_ws_ok ws = true ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly3 S3 W3 mem3 md3 (x_k cx) ->
  frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
  (forall rg : Z, In rg cj_kregs -> getr regs3 (Z_to_bv 5 rg) = getr regs2 (Z_to_bv 5 rg)) ->
  getr regs3 13 = w64 (hsu_cur rsegs cx rest r') ->
  getr regs3 6 = w64 (Z.of_nat (length r')) ->
  getr regs3 18 = w64 (e_pp (x_e cx) + Layout.OFF_LEN) ->
  getr regs3 20 = w64 (e_F (x_e cx) + HSU_E62) ->
  getr regs3 23 = w64 (e_pp (x_e cx)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ cj_wr (e_R (x_e cx)) (e_F (x_e cx)) ws a ->
     aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  garr8 rsegs (mrestrict (w_H W3) mem3) (e_F (x_e cx) + HSU_E62) (hd_zbytes (ent_mem ed)) ->
  (ed, r') = ent_build rr ->
  hsu_cut_J rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r' ed ly3 S3 W3 regs3 mem3 md3.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 ed r' ws HST HD MTL Hws
    HJ3 Hf3 Hp3 Hio3 Hmo3 Hregs H13 H6 H18 H20 H23 K3 E3 Hed.
  pose proof (@asan_consts rc) as (Hceil & _ & EHB & EHE & ELE).
  cj_facts HST HD.
  assert (HTS : T_SEG_STK = 16384) by reflexivity. rewrite HTS in BR1, BR5.
  destruct HD as (HPB & HAT & HFSH & HPP & HE0 & Hsrr & Hfu & Hkd & Hrr).
  destruct HPB as (HCORE & HIN' & Hsr & Hsrr' & Hwf & Hlen' & Hps & Htie & Hsh & Hnp & Hlp & Hnp3 & Hsh7 & Hps2 & Hcnt
    & Hesw & Hes32 & Hesc).
  destruct HCORE as (_ & Hspr & Hfr & Hperm & Hio & Hmo & Hkept).
  (* what the case may have written since the case entry *)
  set (Wr := fun a => ~ (0 <= a < 2 ^ 64) \/ cj_wr (e_R (x_e cx)) (e_F (x_e cx)) ws a).
  assert (KE : forall x, ~ Wr x -> aview rsegs (w_H W3) mem3 x = aview rsegs (w_H W2) mem2 x).
  { intros x Hx. unfold Wr in Hx.
    assert (Hx0 : 0 <= x < 2 ^ 64).
    { destruct (Z_le_gt_dec 0 x) as [H0|H0]; [|exfalso; apply Hx; left; lia].
      destruct (Z_lt_ge_dec x (2 ^ 64)) as [H1|H1]; [lia|exfalso; apply Hx; left; lia]. }
    apply K3; [exact Hx0 | intros H; apply Hx; right; exact H]. }
  assert (HspR : spZ (x_regs cx) = e_R (x_e cx)).
  { unfold spZ. pose proof (Hspr 2 ltac:(lia)) as X.
    assert (X2 : getr (x_regs cx) 2 = w64 (e_R (x_e cx))) by (rewrite <- R2; symmetry; exact X).
    rewrite X2. unfold w64. apply unsigned_lit_small. lia. }
  (* a byte of Wr in [0, 2^64) is in the stack below R, the real frame's cells [R, R+0x198) or the frame *)
  assert (WrIn : forall a, Wr a -> 0 <= a < 2 ^ 64 ->
    (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) \/ (e_R (x_e cx) <= a < e_R (x_e cx) + 0x198) \/
    (e_F (x_e cx) + 0x20 <= a < e_F (x_e cx) + 0x278)).
  { intros a [Hw | Hw] Ha; [exfalso; exact (Hw Ha)|].
    destruct Hw as [Hw | [Hw | Hw]]; [left; exact Hw | | right; right; unfold HSU_E62 in Hw; lia].
    apply Exists_exists in Hw as (o & Hin & Ho). cbv beta in Ho. pose proof (cj_ws_range ws o Hws Hin). right; left; lia. }
  pose proof (cj_pc_len sh ps es Hwf Hesw Hes32 Hps2) as Hlpp.
  unfold hsu_cut_J. split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* the pod loop's base *)
    unfold hsu_pod_base. split.
    { unfold hsu_core, hsu_mid. split; [exact HJ3|]. split.
      { intros rg Hrg. rewrite (Hregs rg ltac:(unfold cj_kregs; cbn [In]; lia)). exact (Hspr rg Hrg). }
      split; [rewrite Hf3; exact Hfr|]. split; [eapply Permutation_trans; [exact Hp3 | exact Hperm]|].
      split; [exact (same_io_trans _ _ _ Hio Hio3)|].
      split; [exact (mle_station MT _ _ _ 0 0 MTL Hmo Hmo3)|].
      intros a Ha Hs HE1. rewrite KE; [exact (Hkept a Ha Hs HE1)|]. rewrite HspR in Hs.
      intros Hw. destruct (WrIn a Hw Ha) as [Hw' | [Hw' | Hw']]; [exact (Hs Hw') | |].
      - apply HE1. unfold hsu_E1, hd_inw. left. cbn [hi_w1 headamp_himg_B].
        apply Exists_cons. right. apply Exists_cons. right. apply Exists_cons. left. cbn [fst snd hd_xv]. lia.
      - apply HE1. unfold hsu_E1, hd_inw. left. cbn [hi_w1 headamp_himg_B].
        apply Exists_cons. left. cbn [fst snd hd_xv]. lia. }
    split; [exact HIN'|].
    split; [exact (cj_suffix_trans rest rr r' Hsrr' ltac:(pose proof (ent_build_rest rr) as X; rewrite <- Hed in X; exact X))|].
    repeat (split; [eassumption|]). exact Hesc.
  - (* the registers and cells *)
    unfold hsu_at_cx, hsu_at. apply Forall_forall. intros [l v] Hf.
    apply in_app_or in Hf as [Hf | Hf].
    + assert (HfD : In (l, v) (hsu_L_D rsegs cx sh np ps cnt es rest r kd))
        by (unfold hsu_L_D; apply in_or_app; left; exact Hf).
      apply (hm_at_kept rsegs _ _ _ _ regs2 regs3 (x_e cx) l v (cj_at _ _ _ _ _ l v HAT HfD)).
      apply (hm_keeps_of rsegs Wr _ _ _ _ _ _ _ l KE).
      destruct (cj_Dc_locs cx sh np ps cnt es l v Hf) as [(rg & -> & Hrg) | (o & -> & Ho)].
      * exact (Hregs rg Hrg).
      * intros i Hi. cbn [hd_xv]. intros Hw.
        assert (Hob : 0 <= o < 0x198) by (unfold cj_cells in Ho; cbn [In] in Ho; lia).
        destruct Hw as [Hw | Hw]; [apply Hw; lia|].
        destruct Hw as [Hw | [Hw | Hw]]; [lia | exact (cj_ws_apart ws (e_R (x_e cx)) o i Hws Ho Hi Hw) |].
        unfold HSU_E62 in Hw. lia.
    + cbn [In] in Hf. destruct Hf as [E | [E | [E | [E | [E | []]]]]]; injection E as <- <-; cbn [hd_at].
      * exact H13.
      * exact H6.
      * exact H18.
      * exact H20.
      * exact H23.
  - (* the frame's shadow *)
    unfold hsu_fsh_at. apply (hm_fsh_kept rsegs (w_H W2) mem2). { exact HFSHD. }
    intros i Hi. apply KE. rewrite cj_PJ_len in Hi.
    unfold shadow_addr, SHADOW_OFF in *. pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (e_F (x_e cx)) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_mod (e_F (x_e cx)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_F (x_e cx)) 8 ltac:(lia)).
    intros Hw. destruct (WrIn _ Hw ltac:(lia)) as [Hw' | [Hw' | Hw']]; [lia | lia |].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia.
  - (* the first block *)
    unfold hsu_pp_at. unfold hsu_pp_at in HPP.
    change (garr8 rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx)) (hd_zbytes (pc_image (PbCut sh ps (Some es)))))
      with (hm_bytes rsegs (w_H W2) mem2 (e_pp (x_e cx)) (pc_image (PbCut sh ps (Some es)))) in HPP.
    change (garr8 rsegs (mrestrict (w_H W3) mem3) (e_pp (x_e cx)) (hd_zbytes (pc_image (PbCut sh ps (Some es)))))
      with (hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx)) (pc_image (PbCut sh ps (Some es)))).
    refine (hm_bytes_kept_wr rsegs Wr (w_H W2) mem2 (w_H W3) mem3 _ _ HPP KE _).
    intros x Hx Hw. rewrite Hlpp in Hx. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
    destruct (WrIn _ Hw ltac:(lia)) as [Hw' | [Hw' | Hw']]; lia.
  - exact E3.
  - exact Hed.
  - pose proof (ent_build_wf rr) as X. rewrite <- Hed in X. exact X.
Qed.

(* ============================== the join, from a case block's post ============================== *)
(* what the block leaves at J: the five registers of hsu_cut_J and e62 *)
Definition cj_J_R (R F pp c : Z) (r rr : list byte) : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop :=
fun W2 regs2 mem2 =>
getr regs2 13 = w64 (c + Z.of_nat (length r) - Z.of_nat (length (snd (ent_build rr)))) /\
getr regs2 6 = w64 (Z.of_nat (length (snd (ent_build rr)))) /\
getr regs2 18 = w64 (pp + Layout.OFF_LEN) /\ getr regs2 20 = w64 (F + HSU_E62) /\ getr regs2 23 = w64 pp /\
garr8 rsegs (mrestrict (w_H W2) mem2) (F + HSU_E62) (hd_zbytes (ent_mem (fst (ent_build rr)))).

Lemma cj_J_post : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 clob ws W3 c3,
  hsu_start_M01 rsegs B headamp_himg_B cx rest ->
  hsu_cut_D rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  ameter_laws MT -> cj_clob_ok clob = true -> cj_ws_ok ws = true ->
  hdu_blk_postE B MT (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) (x_k cx) regs2 ly2 S2 W2 mem2 md2 (bi_J headamp_bld_B) clob
    (cj_wr (e_R (x_e cx)) (e_F (x_e cx)) ws)
    (cj_J_R (e_R (x_e cx)) (e_F (x_e cx)) (e_pp (x_e cx)) (hsu_cur rsegs cx rest r) r rr) W3 c3 ->
  exists regs3 mem3 md3 ly3 S3, c3 = cfg_at rsegs (bi_J headamp_bld_B) regs3 mem3 md3 /\
    hsu_cut_J rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr (snd (ent_build rr)) (fst (ent_build rr))
      ly3 S3 W3 regs3 mem3 md3.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 clob ws W3 c3 HST HD MTL Hcl Hws HP.
  destruct HP as (ly3 & S3 & regs3 & mem3 & md3 & Ec & HJ3 & Hr3 & Hf3 & Hp3 & Hio3 & Hmo3 & Hm3 & HR3).
  destruct HR3 as (H13 & H6 & H18 & H20 & H23 & E3).
  exists regs3, mem3, md3, ly3, S3. split; [exact Ec|].
  eapply (cj_J_of cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
    (fst (ent_build rr)) (snd (ent_build rr)) ws HST HD MTL Hws HJ3).
  - exact Hf3.
  - exact Hp3.
  - exact Hio3.
  - exact Hmo3.
  - intros rg Hrg. apply Hr3.
    + clear - Hrg. unfold cj_kregs in Hrg. cbn [In] in Hrg.
      repeat (destruct Hrg as [<-|Hrg]; [vm_compute; intros X; discriminate X|]). destruct Hrg.
    + exact (cj_clob_keep clob rg Hcl Hrg).
  - rewrite H13. unfold hsu_cur. f_equal. lia.
  - exact H6.
  - exact H18.
  - exact H20.
  - exact H23.
  - exact Hm3.
  - exact E3.
  - destruct (ent_build rr); reflexivity.
Qed.
End w.

Print Assumptions cj_PJ.
Print Assumptions cj_ws_apart.
Print Assumptions cj_clob_keep.
Print Assumptions cj_strs_in_img.
Print Assumptions cj_globs_in_img.
Print Assumptions cj_cells_in_img.
Print Assumptions cj_pc_len.
Print Assumptions cj_hull_band.
Print Assumptions cj_suffix_trans.
Print Assumptions cj_e62_tyszv.
Print Assumptions cj_D_at.
Print Assumptions cj_D_facts.
Print Assumptions cj_D_input.
Print Assumptions cj_D_keep.
Print Assumptions cj_cstr_kept.
Print Assumptions cj_D_img.
Print Assumptions cj_Dc_locs.
Print Assumptions cj_J_of.
Print Assumptions cj_J_post.
