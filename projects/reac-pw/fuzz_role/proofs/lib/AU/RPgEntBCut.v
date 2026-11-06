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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v, with its module paths and module names changed; 505 of its 551 lines of code are new or changed and 690 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEntBCut.v at d1ed1a6d9011 for reac-pw/fuzz_rate's
   image A: module paths changed; the cut states are lib/A/RtPgSeg.v's and the block context and entry premise are
   lib/A/RtPgW6aBase.v's w6_ctx and lib/A/RtPgW6bBase.v's w6b_in (rate's registers and real-frame cells); the image
   record is RtPgImgA.rate_himg_A (six write ranges, the 56-byte frame shadow); the entry bridge also carries the
   image's strings, the vocab cells and their registered global to the cut (w6b_s_ok, w6b_vocab_ok) and e's shadow
   hull; the join bridge starts from RtPgSteps.rts_post's state (a new layout and frame list, w6b_clob, w6b_wr,
   w6b_J_R). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEntBCut.v at 32f84792c2a6; for image B
   (fuzz_rate.asan-ubsan): the cut states are lib/AU/RtPgSegB.v's and the block statements lib/AU/RtPgW6bBaseB.v's
   (w6bb_ctx, w6bb_in with the input premise w6bb_inp, w6bb_J_R, w6bb_clob, w6bb_wr); the image record is
   RtPgImgB.rate_himg_B (six write ranges, the 88-byte prologue shadow of the class-4 frame of 1024 bytes); the pod
   object is e62 at F + 0x210; image B's case-entry registers and real-frame cells (the cell R+0x100 holds the
   complement of &e62.body, stated as 2^64 - 1 - (F + 0x218)), vocab at 0x9bdc0; the join's registers s2, s6, s10
   and t1. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgEntBCutB.v at a191d52e2a9a for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths changed; the cut states are lib/AU/RPgSeg.v's
   (rs_) and the block statements lib/AU/RPgW6bBase.v's (w6bb_ctx, w6bb_in, w6bb_inp, w6bb_J_R, w6bb_clob,
   w6bb_wr); the image record is lib/AU/RPgImgA.v's role_himg_B (five write ranges) and role's segment pre
   lib/A/RPgCSpec.v rl_seg_pre (the frame's prologue shadow is its twelfth conjunct); the real frame is 0x200
   bytes; the case-entry registers are role B's (s11 the shadow offset, a6 the kind byte's address, s4 = 1) and the
   cells R+0x48, 0xf0, 0x110, 0x130, 0x140, 0x158; ent_build.s is at 0x21160 and ent_build.vocab at 0x9a7a0; the
   join's registers are a3, t1, s6 and a5. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the two bridges between
   lib/AU/RPgSeg.v's cut states at ent_build's case entries (rs_cut_D, pcs 0x810d0, 0x80f34, 0x8113c, 0x812d4) and
   at the join J (rs_cut_J, 0x818d8) and the block statements of lib/AU/RPgW6bBase.v. Proves no function (kind:
   segment lemma).

   ebb_D: what rs_start_M01 and rs_cut_D give at a case entry, in the form w6bb_case_stmt asks: the kind byte b with
     rr = b :: r, the block context w6bb_ctx (the harness's journal, the real frame [R, R + 0x200), the class-4 frame
     for locals, rom_view at the cut), the entry premise w6bb_in (image B's registers sp, s1, s3, s11, s2, a6, s6, t1,
     s4, a3 and the cells R+0x48, 0xf0, 0x110, 0x130, 0x140, 0x158, e62 = 0^104 in scope with its shadow hull, the
     input left with its shadow and hull, apart from the callees' stack, the real-frame cells the cases touch and the
     frame's objects) and the image data the cases read (ent_build.s, ent_build.vocab and its nine strings), each
     carried from the segment's start: image bytes lie outside the callees' stack, the frame, pp and the real frame; a
     shadow byte of the image or of the input lies in the shadow band, and one that is marked usable is not one of
     the frame's 88 shadow bytes at the start (all 0xf1 .. 0xf8).
   ebb_J_of: rs_cut_J at the join from a case's rl_wpost: the journal, the registers outside w6bb_clob as at the
     case entry, the bytes outside w6bb_wr as at the case entry, and w6bb_J_R (a3, t1, s6, a5 and e62 =
     Layout.ent_mem of the pod Model.ent_build makes of rr). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YE00 YE01 YM05 YP03 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgMem RPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgSeg RPgW6bBase.
Import ListNotations.
(* the cut record's projections, with the segments implicit as inside lib/AU/RPgSeg.v *)
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


(* ============================== image and frame facts ============================== *)
(* the frame's shadow at a case entry: e62's granules in scope, the rest the prologue's *)
Lemma ebb_PJ : rs_PJ = rm_sh false false false false false true false.
Proof. vm_compute. reflexivity. Qed.
Lemma ebb_PJ_len : Z.of_nat (length rs_PJ) = 88.
Proof. vm_compute. reflexivity. Qed.
Lemma ebb_shA_len : Z.of_nat (length role_B_shA) = 88.
Proof. vm_compute. reflexivity. Qed.

(* M01's write ranges besides pp (RPgImgA hi_w1), as five intervals *)
Lemma ebb_inw : forall e a, rl_inw e (hi_w1 role_himg_B) a <->
  (e_F e + 0x20 <= a < e_F e + 0x278) \/ (shadow_addr (e_F e) + 4 <= a < shadow_addr (e_F e) + 79) \/
  (e_R e + 0x10 <= a < e_R e + 0x40) \/ (e_R e + 0x48 <= a < e_R e + 0x160) \/
  (e_R e + 0x178 <= a < e_R e + 0x198).
Proof.
  intros e a. unfold rl_inw. cbn [hi_w1 role_himg_B]. rewrite !Exists_cons, Exists_nil. cbn [fst snd rl_xv].
  split; intros H; lia.
Qed.

(* the 72 bytes of ent_build.vocab (.data.rel.ro) lie in a loaded segment *)
Lemma ebb_img_vocab : forall i, 0 <= i < 72 -> in_img rsegs (W6BB_VOCAB + i).
Proof.
  intros i Hi.
  assert (Hb : existsb (fun sg => (Z.of_N (seg_base sg) <=? W6BB_VOCAB) &&
                                  (W6BB_VOCAB + 72 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) rsegs = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in Hb as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hin | lia].
Qed.

(* ent_build.vocab's nine cells and strings among the image's registered cells and strings *)
Lemma ebb_vocab_cells : forall i, 0 <= i < 9 -> In (W6BB_VOCAB + 8 * i, w6bb_vptr i) role_B_cells.
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
  repeat (destruct E as [-> | E]; [vm_compute; repeat (first [left; reflexivity | right]) |]).
  subst i. vm_compute. repeat (first [left; reflexivity | right]).
Qed.
Lemma ebb_vocab_strs : forall i, 0 <= i < 9 ->
  In (w6bb_vptr i, map (fun x : byte => bv_unsigned x) (nth (Z.to_nat i) vocab [])) role_B_strs.
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
  repeat (destruct E as [-> | E]; [vm_compute; repeat (first [left; reflexivity | right]) |]).
  subst i. vm_compute. repeat (first [left; reflexivity | right]).
Qed.

(* the shadow hull of an application range below 2^47 lies in the shadow band *)
Lemma ebb_hull_band : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 - 1 ->
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

Lemma ebb_suffix_trans : forall (rest rr r' : list byte), rs_suffix rest rr -> is_rest r' rr -> rs_suffix rest r'.
Proof.
  intros rest rr r' (j & Hj & Erj) (k & Ek). subst rr r'. rewrite skipn_skipn.
  destruct (Nat.le_gt_cases (k + j) (length rest)) as [Hle|Hgt].
  - exists (k + j)%nat. split; [exact Hle | reflexivity].
  - exists (length rest). split; [lia|]. rewrite !skipn_all2 by lia. reflexivity.
Qed.

(* a byte outside a write set {not a word address} \/ P \/ Q *)
Lemma ebb_notwr : forall (P Q : Z -> Prop) x, ~ (~ (0 <= x < 2 ^ 64) \/ P x \/ Q x) ->
  0 <= x < 2 ^ 64 /\ ~ P x /\ ~ Q x.
Proof.
  intros P Q x H. split; [| split; intros X; apply H; right; [left | right]; exact X].
  destruct (Z_le_gt_dec 0 x); destruct (Z_lt_ge_dec x (2 ^ 64)); try lia; exfalso; apply H; left; lia.
Qed.

(* ============================== the first block's image is PP_SIZE bytes ============================== *)
Lemma ebb_pc_len : forall sh ps es, rs_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat -> (length ps <= 2)%nat ->
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

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

Lemma ebb_at : forall H mem regs e (L : list (rl_loc * Z)) l v,
  rs_at rsegs H mem regs e L -> In (l, v) L -> rl_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HA Hin. exact (proj1 (Forall_forall _ _) HA (l, v) Hin). Qed.

Lemma ebb_frame_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos Hle. unfold frame_addr. destruct Hle as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. Qed.

Lemma ebb_val_small : forall H mem a v, 0 <= v < 2 ^ 64 ->
  val_mem rsegs (mrestrict H mem) a 8 (v mod 2 ^ 64) -> val_mem rsegs (mrestrict H mem) a 8 v.
Proof. intros H mem a v Hv V. rewrite Z.mod_small in V by lia. exact V. Qed.

(* a cell that holds the complement of x (RtPgBase.rl_at keeps it mod 2^64) holds 2^64 - 1 - x *)
Lemma ebb_val_lnot : forall H mem a x, 0 <= x < 2 ^ 64 ->
  val_mem rsegs (mrestrict H mem) a 8 (Z.lnot x mod 2 ^ 64) -> val_mem rsegs (mrestrict H mem) a 8 (2 ^ 64 - 1 - x).
Proof.
  intros H mem a x Hx V.
  replace (2 ^ 64 - 1 - x) with (Z.lnot x mod 2 ^ 64); [exact V|].
  assert (E : Z.lnot x = - x - 1) by (unfold Z.lnot; lia).
  rewrite E. replace (- x - 1) with ((2 ^ 64 - 1 - x) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* ---- carrying the segment start's shadow facts to a later memory ----
   KB: every shadow-band byte outside the frame's 88 shadow bytes is as at the start; the frame's shadow bytes are
   readable now; at the start they are the prologue's (all >= 8), so a usable byte's shadow byte is not one of them. *)
Lemma ebb_ra_kept : forall H mem H' mem' F a n,
  range_addressable (aview rsegs H mem) SHADOW_OFF a n -> rl_fsh rsegs H mem F role_B_shA ->
  0 <= a -> a + n <= kHighMemEnd ->
  (forall x, kLowMemEnd <= x < kHighMemBeg -> ~ (shadow_addr F <= x < shadow_addr F + 88) ->
     aview rsegs H' mem' x = aview rsegs H mem x) ->
  range_addressable (aview rsegs H' mem') SHADOW_OFF a n.
Proof.
  intros H mem H' mem' F a n RA Hfsh Ha Hn KB.
  apply (rm_ra_kept rsegs H mem); [exact RA|]. intros x Hx.
  apply KB; [exact (rm_shadow_band x ltac:(lia)) |].
  pose proof (rm_ra_not_fsh rsegs H mem F role_B_shA a n RA Hfsh rm_sh_P0_big x Hx) as X.
  rewrite ebb_shA_len in X. exact X.
Qed.

Lemma ebb_cstr_kept : forall H mem H' mem' F a s,
  rl_cstr rsegs H mem a s -> rl_fsh rsegs H mem F role_B_shA ->
  (forall x, in_img rsegs x -> aview rsegs H' mem' x = aview rsegs H mem x) ->
  (forall x, kLowMemEnd <= x < kHighMemBeg -> ~ (shadow_addr F <= x < shadow_addr F + 88) ->
     aview rsegs H' mem' x = aview rsegs H mem x) ->
  (forall x, shadow_addr F <= x < shadow_addr F + 88 -> aview rsegs H' mem' x <> None) ->
  rl_cstr rsegs H' mem' a s.
Proof.
  intros H mem H' mem' F a s (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9) Hfsh KI KB KF.
  assert (Hlow : a + Z.of_nat (length s) < kLowMemEnd).
  { pose proof (rl_segs_low _ (C6 (Z.of_nat (length s)) ltac:(lia))) as X. lia. }
  unfold kLowMemEnd in Hlow.
  split; [intros i Hi; rewrite KI by (apply C6; lia); exact (C1 i Hi)|].
  split; [rewrite KI by (apply C6; lia); exact C2|].
  split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|]. split; [exact C7|].
  split.
  - apply (ebb_ra_kept H mem H' mem' F a _ C8 Hfsh); [lia | unfold kHighMemEnd; lia | exact KB].
  - intros t Ht.
    pose proof (ebb_hull_band a (Z.of_nat (length s) + 1) t ltac:(lia) ltac:(lia) ltac:(lia) Ht) as Hb.
    destruct (Z_lt_le_dec t (shadow_addr F)) as [T1|T1];
      [| destruct (Z_lt_le_dec t (shadow_addr F + 88)) as [T2|T2]].
    + rewrite KB by lia. exact (C9 t Ht).
    + exact (KF t ltac:(lia)).
    + rewrite KB by lia. exact (C9 t Ht).
Qed.

Ltac ebb_in := cbn [rs_L_D rs_L_Dc rs_L_Dc0 rs_Rc0 rs_Kc rs_podc app];
  repeat (first [left; reflexivity | right]).

(* ============================== the case entry: the frame, pp, R and the carried memory ============================== *)
Lemma ebb_D_facts : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  rs_start_M01 rsegs B cx rest ->
  rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem2 md2 (x_k cx) /\
  getr regs2 2 = w64 (e_R (x_e cx)) /\ getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
  spZ (x_regs cx) = e_R (x_e cx) /\
  alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ e_R (x_e cx) + 0x200 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  e_R (x_e cx) mod 16 = 0 /\ x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK /\
  In (4, x_pos cx) (x_own cx) /\ In (4, x_pos cx) (frames S2) /\ e_F (x_e cx) = frame_addr ly2 4 (x_pos cx) /\
  4096 <= e_F (x_e cx) /\ e_F (x_e cx) + 1024 <= alloc_ceiling /\ e_F (x_e cx) mod 32 = 0 /\
  in_app (e_F (x_e cx)) 1024 /\
  In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2) /\ 4096 <= e_pp (x_e cx) /\
  e_pp (x_e cx) + Layout.PP_SIZE <= alloc_ceiling /\ in_app (e_pp (x_e cx)) Layout.PP_SIZE /\
  zdisjoint (e_pp (x_e cx), Layout.PP_SIZE) (e_F (x_e cx), 1024) /\
  (forall x, in_img rsegs x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W cx)) (x_memc cx) x) /\
  (forall x, kLowMemEnd <= x < kHighMemBeg ->
     ~ (shadow_addr (e_F (x_e cx)) <= x < shadow_addr (e_F (x_e cx)) + 88) ->
     aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W cx)) (x_memc cx) x) /\
  rl_fsh rsegs (w_H W2) mem2 (e_F (x_e cx)) rs_PJ /\
  rl_fsh rsegs (w_H (x_W cx)) (x_memc cx) (e_F (x_e cx)) role_B_shA /\
  rom_view rsegs W2 mem2.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof asan_consts as (Hceil & _).
  destruct HST as (HPRE & Hfsh0 & HL1 & Hlen & HIN).
  destruct HPRE as (HJc & Hnev & HR2 & Hgp & Htp & ES & ER16 & ERS & ESTK & Hown & EF & Hfsh1 & Hpp0 & Hppb
    & Hfl & Haro & Hglobs & Hrz & Hstrs & Hcells & Hrom & Hnfresh).
  destruct HD as (HPB & HAT & HFSH & HPP & HE0 & Hsrr & Hfu & Hkd & Hrr).
  destruct HPB as (HCORE & HIN' & Hsr & Hsrr' & Hwf & Hlen' & Hps & Htie & Hsh & Hnp & Hlp & Hnp3 & Hsh7 & Hps2 & Hcnt
    & Hesw & Hes32 & Hesc).
  destruct HCORE as (HJ & Hspr & Hfr & Hperm & Hio & Hmo & Hkept).
  pose proof HJ as (HAR & Hlyle & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hc1 & Hc2 & Hc3 & Hc4 & _).
  pose proof HJc as (_ & Hlyle_c & _).
  cbn [hi_cid hi_rsz hi_shA role_himg_B] in Hown, EF, ERS, Hfsh0.
  assert (HTS : T_SEG_STK = 16384) by reflexivity.
  assert (HRb : alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ e_R (x_e cx) + 0x200 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47)
    by lia.
  assert (HspR : spZ (x_regs cx) = e_R (x_e cx)).
  { unfold spZ. rewrite HR2. unfold w64. apply unsigned_lit_small. lia. }
  (* the frame *)
  assert (HinF : In (4, x_pos cx) (frames S2)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  assert (EF2 : e_F (x_e cx) = frame_addr ly2 4 (x_pos cx)).
  { rewrite EF, (ebb_frame_addr_le _ _ _ 4 (x_pos cx) Hlyle_c), (ebb_frame_addr_le _ _ _ 4 (x_pos cx) Hlyle).
    reflexivity. }
  destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) HAR HinF) as (HF1 & HF2 & HF3).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 4 (x_pos cx) HAR HinF) as (HF32 & _ & HFp & _).
  rewrite <- EF2 in HF1, HF2, HF3, HF32, HFp. change (fs_frame_bytes 4) with 1024 in HF1, HF2, HF3, HFp.
  (* pp *)
  assert (Hpp2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
    by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppb]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp2) as (_ & Hp1 & Hp2 & Happ & _).
  assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
  rewrite Hrq in Hp2, Happ.
  pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ 4 (x_pos cx) HAR Hpp2 HinF) as Hsep.
  rewrite Hrq, <- EF2 in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
  (* an image byte lies outside everything the segment may have written *)
  assert (KI : forall x, in_img rsegs x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W cx)) (x_memc cx) x).
  { intros x Hx. pose proof (rl_segs_low x Hx) as Hlow. unfold kLowMemEnd in Hlow.
    apply Hkept; [lia | rewrite HspR; lia |].
    unfold rs_E1. intros [Hw | Hw].
    - apply ebb_inw in Hw. destruct Hw as [Hw | [Hw | Hw]].
      + apply (frm_img rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) x HAR HinF); [| exact Hx].
        rewrite <- EF2. change (fs_frame_bytes 4) with 1024. lia.
      + unfold shadow_addr, SHADOW_OFF in Hw. pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)). lia.
      + lia.
    - exact (blk_img rsegs B LAWS _ _ _ _ _ _ _ x HAR Hpp2 ltac:(rewrite Hrq; lia) Hx). }
  (* a shadow-band byte outside the frame's shadow lies outside everything the segment may have written *)
  assert (KB : forall x, kLowMemEnd <= x < kHighMemBeg ->
     ~ (shadow_addr (e_F (x_e cx)) <= x < shadow_addr (e_F (x_e cx)) + 88) ->
     aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W cx)) (x_memc cx) x).
  { intros x Hx Hnf. unfold kLowMemEnd, kHighMemBeg in Hx.
    apply Hkept; [lia | rewrite HspR; lia |].
    unfold rs_E1. intros [Hw | Hw].
    - apply ebb_inw in Hw. destruct Hw as [Hw | [Hw | Hw]].
      + unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HF3. lia.
      + lia.
      + lia.
    - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia. }
  (* rom_view at the cut *)
  assert (HromD : rom_view rsegs W2 mem2).
  { apply (rm_rom_kept rsegs (x_W cx) W2 (x_memc cx) mem2 Hrom). intros a Ha. apply KI.
    destruct Ha as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | lia]. }
  split; [exact HJ|].
  split; [exact (eq_trans (Hspr 2 ltac:(lia)) HR2)|].
  split; [exact (eq_trans (Hspr 3 ltac:(lia)) Hgp)|].
  split; [exact (eq_trans (Hspr 4 ltac:(lia)) Htp)|].
  split; [exact HspR|].
  split; [exact (proj1 HRb)|]. split; [exact (proj1 (proj2 HRb))|]. split; [exact (proj2 (proj2 HRb))|].
  split; [exact ER16|]. split; [exact ESTK|].
  split; [exact Hown|]. split; [exact HinF|]. split; [exact EF2|].
  split; [exact HF1|]. split; [exact HF2|]. split; [exact HF32|]. split; [exact HF3|].
  split; [exact Hpp2|]. split; [exact Hp1|]. split; [exact Hp2|]. split; [exact Happ|]. split; [exact Hsep|].
  split; [exact KI|]. split; [exact KB|].
  split; [exact HFSH|]. split; [exact Hfsh0|].
  exact HromD.
Qed.

(* ============================== the case entry: the input ============================== *)
Lemma ebb_D_input : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  rs_start_M01 rsegs B cx rest ->
  rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  (exists b, rr = b :: r /\ bv_unsigned b = kd) /\
  0 < rs_cur rsegs cx rest r - 1 /\
  w6bb_inp W2 mem2 (e_R (x_e cx)) (e_F (x_e cx)) (rs_cur rsegs cx rest r) r.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof asan_consts as (Hceil & _).
  pose proof (ebb_D_facts cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (HJ & R2 & R3 & R4 & HspR & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp
     & Hpp & Hpp1 & Hpp2 & Hppapp & Hsep & KI & KB & HFSHD & Hfsh0 & HromD).
  destruct HST as (_ & _ & _ & _ & HIN).
  destruct HD as (HPB & _ & _ & _ & _ & Hsrr & Hfu & Hkd & Hrr).
  destruct HPB as (HCORE & _ & Hsr & _).
  destruct HCORE as (_ & _ & _ & _ & _ & _ & Hkept).
  destruct HIN as (Hel & Hgar & Hra & Hhull & Hamr & Hsrc0 & Hsrc63 & Hdis).
  destruct Hsr as (j & Hj & Er).
  destruct Hsrr as (j' & Hj' & Err).
  assert (HTS : T_SEG_STK = 16384) by reflexivity.
  assert (Hlr : length r = (length rest - j)%nat) by (rewrite Er, length_skipn; reflexivity).
  assert (Hlrr : length rr = (length rest - j')%nat) by (rewrite Err, length_skipn; reflexivity).
  destruct rr as [|b r0]; [congruence|].
  cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as Ekd Er0. subst r0.
  cbn [length] in Hlrr.
  assert (Hcur : rs_cur rsegs cx rest r = e_src (x_e cx) + Z.of_nat j) by (unfold rs_cur; rewrite Hlr; lia).
  set (c := rs_cur rsegs cx rest r) in *.
  assert (Hend : c + Z.of_nat (length r) = e_src (x_e cx) + e_left (x_e cx)) by (rewrite Hcur, Hlr, Hel; lia).
  assert (Hhi : e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 47 - 1).
  { unfold amem_range in Hamr. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. lia. }
  (* the bytes the walk may have changed since the segment's start *)
  set (Wr := fun a => ~ (0 <= a < 2 ^ 64) \/ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) \/ rs_E1 rsegs cx a).
  assert (KE : forall x, ~ Wr x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W cx)) (x_memc cx) x).
  { intros x Hx. unfold Wr in Hx.
    destruct (ebb_notwr (fun a => e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) (rs_E1 rsegs cx) x Hx)
      as (H1 & H2 & H3).
    apply Hkept; [exact H1 | rewrite HspR; exact H2 | exact H3]. }
  assert (HFE : in_app (e_F (x_e cx) + 0x20) 0x258)
    by (apply (in_app_sub (e_F (x_e cx)) 1024); [exact HFapp | lia | lia | lia]).
  (* a shadow byte of an input byte avoids everything the segment may have written *)
  assert (SHW : forall x, e_src (x_e cx) <= x < e_src (x_e cx) + e_left (x_e cx) -> ~ Wr (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. pose proof (rm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as Hb.
    unfold kLowMemEnd, kHighMemBeg in Hb.
    unfold Wr, rs_E1. intros [Hw | [Hw | [Hw | Hw]]]; [lia | lia | |].
    - apply ebb_inw in Hw. destruct Hw as [Hw | [Hw | Hw]].
      + exact (rm_shadow_not_app x _ _ ltac:(unfold kHighMemEnd; lia) HFE ltac:(lia)).
      + exact (rm_ra_not_fsh rsegs _ _ _ _ _ _ Hra Hfsh0 rm_sh_P0_big x Hx ltac:(rewrite ebb_shA_len; lia)).
      + lia.
    - exact (rm_shadow_not_app x _ _ ltac:(unfold kHighMemEnd; lia) Hppapp Hw). }
  split; [exists b; split; [reflexivity | symmetry; exact Ekd]|].
  split; [rewrite Hcur; lia|].
  unfold w6bb_inp. split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* the bytes *)
    assert (B0 : rm_bytes rsegs (w_H (x_W cx)) (x_memc cx) (e_src (x_e cx)) rest) by exact Hgar.
    pose proof (rm_bytes_slice rsegs _ _ _ rest j (length rest - j) B0 ltac:(lia)) as B1.
    unfold rm_slice in B1. rewrite firstn_all2 in B1 by (rewrite length_skipn; lia). rewrite <- Er in B1.
    rewrite <- Hcur in B1.
    refine (rm_bytes_kept_wr rsegs Wr _ _ _ _ _ r B1 KE _).
    intros x Hx. destruct (Hdis x ltac:(lia)) as (D1 & D2 & D3).
    unfold Wr, rs_E1. intros [Hw | [Hw | [Hw | Hw]]]; [lia | exact (D1 Hw) | exact (D2 Hw) | exact (D3 Hw)].
  - (* their shadow *)
    apply (rm_ra_kept_wr rsegs Wr (w_H (x_W cx)) (x_memc cx)); [| exact KE |].
    + apply (range_addressable_sub _ _ _ _ _ _ Hra); lia.
    + intros x Hx. apply SHW. lia.
  - lia.
  - lia.
  - unfold amem_range in *. lia.
  - (* the input's shadow hull *)
    intros Hn. apply (rm_hull_kept rsegs (w_H (x_W cx)) (x_memc cx)).
    + apply (rm_hull_sub _ _ _ _ _ (Hhull ltac:(lia))); lia.
    + intros s Hs Hns.
      pose proof (ebb_hull_band c (Z.of_nat (length r)) s ltac:(lia) Hn ltac:(lia) Hs) as Hb.
      destruct (Z_lt_le_dec s (shadow_addr (e_F (x_e cx)))) as [Hs1 | Hs1];
        [| destruct (Z_lt_le_dec s (shadow_addr (e_F (x_e cx)) + 88)) as [Hs2 | Hs2]].
      2: { replace s with (shadow_addr (e_F (x_e cx)) + (s - shadow_addr (e_F (x_e cx)))) by lia.
           rewrite (HFSHD (s - shadow_addr (e_F (x_e cx))) ltac:(rewrite ebb_PJ_len; lia)). discriminate. }
      all: rewrite KB; [exact Hns | exact Hb | lia].
  - (* apart from the callees' stack, the real-frame cells the cases touch and the frame's objects *)
    intros a Ha. destruct (Hdis a ltac:(lia)) as (D1 & D2 & _).
    pose proof (fun X => D2 (proj2 (ebb_inw (x_e cx) a) X)) as D2'.
    split; [exact D1 | split; intros X; apply D2'; tauto].
Qed.

(* ============================== the case entry: the image data the cases read ============================== *)
Lemma ebb_D_img : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  rs_start_M01 rsegs B cx rest ->
  rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  w6bb_s_ok W2 mem2 /\ w6bb_vocab_ok W2 mem2.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof (ebb_D_facts cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
     & _ & _ & _ & _ & _ & KI & KB & HFSHD & Hfsh0 & _).
  destruct HST as (HPRE & _).
  destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hglobs & _ & Hstrs & Hcells & _).
  cbn [hi_globs hi_strs hi_cells role_himg_B] in Hglobs, Hstrs, Hcells.
  assert (KF : forall x, shadow_addr (e_F (x_e cx)) <= x < shadow_addr (e_F (x_e cx)) + 88 ->
    aview rsegs (w_H W2) mem2 x <> None).
  { intros x Hx. replace x with (shadow_addr (e_F (x_e cx)) + (x - shadow_addr (e_F (x_e cx)))) by lia.
    rewrite (HFSHD (x - shadow_addr (e_F (x_e cx))) ltac:(rewrite ebb_PJ_len; lia)). discriminate. }
  rewrite Forall_forall in Hstrs, Hglobs. unfold rl_ro_cells in Hcells. rewrite Forall_forall in Hcells.
  split.
  - unfold w6bb_s_ok.
    replace (map (fun x : byte => bv_unsigned x) S9) with [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101]
      by (vm_compute; reflexivity).
    pose proof (Hstrs (0x21160, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101])
      ltac:(unfold role_B_strs; repeat (first [left; reflexivity | right]))) as HS9.
    exact (ebb_cstr_kept _ _ _ _ _ _ _ HS9 Hfsh0 KI KB KF).
  - split.
    + pose proof (Hglobs (W6BB_VOCAB, 72) ltac:(unfold role_B_globs; repeat (first [left; reflexivity | right]))) as HG.
      cbn [fst snd] in HG.
      apply (ebb_ra_kept _ _ _ _ _ _ _ HG Hfsh0); [unfold W6BB_VOCAB; lia | unfold W6BB_VOCAB, kHighMemEnd; lia | exact KB].
    + intros i Hi. split.
      * pose proof (Hcells _ (ebb_vocab_cells i Hi)) as V. cbn [fst snd] in V.
        apply (rm_val_of_bytes rsegs). apply (rm_bytes_kept rsegs (w_H (x_W cx)) (x_memc cx)).
        { apply rm_bytes_of_val. exact V. }
        intros x Hx. rewrite length_Z_to_le_bytes in Hx. apply KI.
        replace x with (W6BB_VOCAB + (x - W6BB_VOCAB)) by lia. apply ebb_img_vocab. lia.
      * exact (ebb_cstr_kept _ _ _ _ _ _ _ (Hstrs _ (ebb_vocab_strs i Hi)) Hfsh0 KI KB KF).
Qed.

(* ============================== the case entry: everything w6bb_case_stmt asks ============================== *)
Lemma ebb_D : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  rs_start_M01 rsegs B cx rest ->
  rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  (exists b, rr = b :: r /\ bv_unsigned b = kd) /\
  w6bb_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_k cx)
    ly2 S2 W2 mem2 md2 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx) /\
  w6bb_in B W2 mem2 regs2 (e_R (x_e cx)) (e_F (x_e cx)) (rs_cur rsegs cx rest r) (e_pp (x_e cx)) kd r /\
  w6bb_s_ok W2 mem2 /\ w6bb_vocab_ok W2 mem2.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof asan_consts as (Hceil & _).
  pose proof (ebb_D_facts cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (HJ & R2 & R3 & R4 & HspR & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp
     & Hpp & Hpp1 & Hpp2 & Hppapp & Hsep & KI & KB & HFSHD & Hfsh0 & HromD).
  pose proof (ebb_D_input cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as (Hb & Hc1 & Hwin).
  pose proof (ebb_D_img cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as (HS & HV).
  destruct HD as (_ & HAT & _ & _ & HE0 & _ & _ & Hkd & _).
  assert (AT : forall l v, In (l, v) (rs_L_D rsegs cx sh np ps cnt es rest r kd) ->
    rl_at rsegs (w_H W2) mem2 regs2 (x_e cx) l v)
    by (intros l v Hin; exact (ebb_at _ _ _ _ _ l v HAT Hin)).
  assert (HTS : T_SEG_STK = 16384) by reflexivity.
  assert (HPPS : Layout.PP_SIZE = 19744) by reflexivity.
  assert (HF8 : e_F (x_e cx) mod 8 = 0).
  { pose proof (Z.div_mod (e_F (x_e cx)) 32 ltac:(lia)). pose proof (Z.div_mod (e_F (x_e cx)) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (e_F (x_e cx)) 8 ltac:(lia)). lia. }
  split; [exact Hb|].
  split.
  { unfold w6bb_ctx. split; [exact HJ|]. split; [exact BR4|]. split; [exact BR2|]. split; [exact BR5|].
    split; [exact Hown|]. split; [exact EF2|]. exact HromD. }
  split; [| split; [exact HS | exact HV]].
  unfold w6bb_in.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  split; [exact (AT (LReg 9) _ ltac:(ebb_in))|].
  split; [exact (AT (LReg 27) _ ltac:(ebb_in))|].
  split; [exact (AT (LReg 19) _ ltac:(ebb_in))|].
  split; [exact (AT (LReg 18) _ ltac:(ebb_in))|].
  split; [exact (AT (LReg 16) _ ltac:(ebb_in))|].
  split; [exact (AT (LReg 22) _ ltac:(ebb_in))|].
  split; [exact (AT (LReg 6) _ ltac:(ebb_in))|].
  split; [exact (AT (LReg 20) _ ltac:(ebb_in))|].
  split.
  { intros H9. apply (AT (LReg 13)). unfold rs_L_D. apply in_or_app. right. apply in_or_app. right.
    apply Z.eqb_neq in H9. rewrite H9. right. left. reflexivity. }
  split; [apply ebb_val_small; [lia | exact (AT (LCell XR 0x48) _ ltac:(ebb_in))]|].
  split; [apply ebb_val_lnot; [lia | exact (AT (LCell XR 0xf0) _ ltac:(ebb_in))]|].
  split; [apply ebb_val_small; [lia | exact (AT (LCell XR 0x110) _ ltac:(ebb_in))]|].
  split; [apply ebb_val_small; [unfold Layout.PP_SIZE in Hpp2; lia | exact (AT (LCell XR 0x130) _ ltac:(ebb_in))]|].
  split; [apply ebb_val_small; [unfold Layout.PP_SIZE in Hpp2; lia | exact (AT (LCell XR 0x140) _ ltac:(ebb_in))]|].
  split; [apply ebb_val_small; [lia | exact (AT (LCell XR 0x158) _ ltac:(ebb_in))]|].
  split; [exact Hkd|]. split; [exact Hpp1|].
  split; [unfold Layout.PP_SIZE in Hpp2; lia|].
  split; [exact HF1|]. split; [exact HF2|]. split; [exact HF32|]. split; [exact HFapp|].
  split.
  { (* e62 = 0^104 *)
    intros i Hi.
    destruct (HE0 (Z.to_nat i) ltac:(unfold rs_u8s, zeros; rewrite length_map, rm_length_repeat; lia)) as [V _].
    rewrite Z2Nat.id in V by lia. specialize (V 0%nat ltac:(lia)). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
    rewrite V. f_equal. unfold rs_u8s. rewrite (rm_nth_map (zeros 104) (Z.to_nat i)).
    unfold zeros. rewrite (rm_nth_repeat _ _ 104 (Z.to_nat i)) by lia. reflexivity. }
  split.
  { (* e62's shadow: its 13 granules are in scope *)
    pose proof HFSHD as HF'. rewrite ebb_PJ in HF'.
    pose proof (rm_B_ra_e62 rsegs (w_H W2) mem2 _ false false false false false false 0 104 HF' HF8
      ltac:(lia) ltac:(lia)) as X.
    unfold RM_E62 in X. rewrite Z.add_0_r in X. exact X. }
  split.
  { (* e62's shadow hull lies inside the frame's 88 shadow bytes *)
    intros s Hs.
    assert (Hin : shadow_addr (e_F (x_e cx)) <= s < shadow_addr (e_F (x_e cx)) + 88).
    { unfold shadow_addr in *.
      pose proof (Z.div_mod (e_F (x_e cx)) 8 ltac:(lia)) as D0.
      pose proof (Z.div_mod (e_F (x_e cx) + 0x210) 8 ltac:(lia)) as D1.
      pose proof (Z.mod_pos_bound (e_F (x_e cx) + 0x210) 8 ltac:(lia)) as M1.
      pose proof (Z.div_mod (e_F (x_e cx) + 0x210 + 104 - 1) 8 ltac:(lia)) as D2.
      pose proof (Z.mod_pos_bound (e_F (x_e cx) + 0x210 + 104 - 1) 8 ltac:(lia)) as M2.
      pose proof (Z.div_mod (SHADOW_OFF + (e_F (x_e cx) + 0x210) / 8) 8 ltac:(lia)) as D3.
      pose proof (Z.mod_pos_bound (SHADOW_OFF + (e_F (x_e cx) + 0x210) / 8) 8 ltac:(lia)) as M3.
      pose proof (Z.div_mod (SHADOW_OFF + (e_F (x_e cx) + 0x210 + 104 - 1) / 8) 8 ltac:(lia)) as D4.
      pose proof (Z.mod_pos_bound (SHADOW_OFF + (e_F (x_e cx) + 0x210 + 104 - 1) / 8) 8 ltac:(lia)) as M4.
      lia. }
    replace s with (shadow_addr (e_F (x_e cx)) + (s - shadow_addr (e_F (x_e cx)))) by lia.
    rewrite (HFSHD (s - shadow_addr (e_F (x_e cx))) ltac:(rewrite ebb_PJ_len; lia)). discriminate. }
  split; [exact Hc1|]. exact Hwin.
Qed.

(* ============================== the join ============================== *)
Lemma ebb_J_of : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
  rs_start_M01 rsegs B cx rest ->
  rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly3 S3 W3 mem3 md3 (x_k cx) ->
  (forall rg : bv 5, bv_unsigned rg <> 0 -> ~ In rg w6bb_clob -> getr regs3 rg = getr regs2 rg) ->
  frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 ->
  mo_le MT S2 S3 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ w6bb_wr (e_R (x_e cx)) (e_F (x_e cx)) a ->
     aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  w6bb_J_R (e_R (x_e cx)) (e_F (x_e cx)) (rs_cur rsegs cx rest r) (e_pp (x_e cx)) r rr W3 regs3 mem3 ->
  rs_cut_J rsegs B MT cx sh np ps cnt es rest rr (snd (ent_build rr)) (fst (ent_build rr)) ly3 S3 W3 regs3 mem3 md3.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HST HD HJ3 Hr3 Hf3 Hp3
    Hio3 Hmo3 Hm3 HR3.
  pose proof asan_consts as (Hceil & _).
  pose proof (ebb_D_facts cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (HJ & R2 & R3 & R4 & HspR & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp
     & Hpp & Hpp1 & Hpp2 & Hppapp & Hsep & KI & KB & HFSHD & Hfsh0 & HromD).
  assert (HTS : T_SEG_STK = 16384) by reflexivity.
  destruct HD as (HPB & HAT & HFSH & HPP & HE0 & Hsrr & Hfu & Hkd & Hrr).
  destruct HPB as (HCORE & HIN' & Hsr & Hsrr' & Hwf & Hlen' & Hps & Htie & Hsh & Hnp & Hlp & Hnp3 & Hsh7 & Hps2 & Hcnt
    & Hesw & Hes32 & Hesc).
  destruct HCORE as (_ & Hspr & Hfr & Hperm & Hio & Hmo & Hkept).
  destruct HR3 as (R22 & R15 & R13 & R6 & E3).
  (* the registers outside w6bb_clob that the cut lists *)
  assert (Hregs : forall n, In n [2; 3; 4; 8; 9; 19; 21; 23; 25; 27] ->
    getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<- | Hn];
      [apply Hr3; [vm_compute; lia | intros Hin; apply (in_map (@bv_unsigned 5)) in Hin; vm_compute in Hin; lia] |]).
    destruct Hn. }
  pose proof (ebb_pc_len sh ps es Hwf Hesw Hes32 Hps2) as Hlpp.
  unfold rs_cut_J. split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* the pod loop's base *)
    unfold rs_pod_base. split.
    { unfold rs_core, rs_mid. split; [exact HJ3|]. split.
      { intros rg Hrg. rewrite <- (Hspr rg Hrg). apply Hregs. cbn [In]. lia. }
      split; [rewrite Hf3; exact Hfr|].
      split; [exact (Permutation_trans Hp3 Hperm)|].
      split; [exact (same_io_trans _ _ _ Hio Hio3)|].
      split; [exact (mle_station MT _ _ _ 0 0 MTL Hmo Hmo3)|].
      intros a Ha Hs HE1. rewrite Hm3; [exact (Hkept a Ha Hs HE1) | exact Ha |].
      rewrite HspR in Hs. unfold w6bb_wr. intros [Hw | Hw]; [exact (Hs Hw) |].
      apply HE1. unfold rs_E1. left. apply (proj2 (ebb_inw _ _)). lia. }
    split; [exact HIN'|].
    split; [exact (ebb_suffix_trans rest rr _ Hsrr' (ent_build_rest rr))|].
    repeat (split; [eassumption|]). exact Hesc.
  - (* the registers and cells *)
    unfold rs_at_cx, rs_at. apply Forall_forall. intros [l v] Hf.
    apply in_app_or in Hf as [Hf | Hf].
    + assert (A : rl_at rsegs (w_H W2) mem2 regs2 (x_e cx) l v).
      { apply (ebb_at _ _ _ _ _ l v HAT). unfold rs_L_D, rs_L_Dc. apply in_or_app. left. apply in_or_app. left.
        exact Hf. }
      apply (rm_at_kept rsegs _ _ _ _ regs2 regs3 (x_e cx) l v A).
      cbn [rs_L_Dc0 rs_Rc0 rs_Kc rs_podc app In] in Hf.
      repeat (destruct Hf as [Hf | Hf];
        [injection Hf as <- <-; cbn [rm_keeps rl_xv];
         first [ solve [apply Hregs; cbn [In]; lia]
               | solve [intros i Hi; apply Hm3; [lia | unfold w6bb_wr; lia]] ] |]).
      destruct Hf.
    + cbn [In] in Hf. destruct Hf as [E | [E | [E | [E | []]]]]; injection E as <- <-; cbn [fst snd rl_at].
      * etransitivity; [exact R13|]. f_equal. unfold rs_cur. lia.
      * exact R6.
      * exact R22.
      * exact R15.
  - (* the frame's shadow *)
    unfold rs_fsh_at. apply (rm_fsh_kept rsegs (w_H W2) mem2); [exact HFSH|].
    intros i Hi. rewrite ebb_PJ_len in Hi.
    unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (e_F (x_e cx)) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_mod (e_F (x_e cx)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_F (x_e cx)) 8 ltac:(lia)).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
    apply Hm3; [lia | unfold w6bb_wr; lia].
  - (* the first block *)
    unfold rs_pp_at. unfold rs_pp_at in HPP.
    apply (rm_bytes_kept rsegs (w_H W2) mem2); [exact HPP|].
    intros x Hx. rewrite Hlpp in Hx. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
    apply Hm3; [lia | unfold w6bb_wr; lia].
  - exact E3.
  - symmetry. apply surjective_pairing.
  - exact (ent_build_wf rr).
Qed.
End w.

