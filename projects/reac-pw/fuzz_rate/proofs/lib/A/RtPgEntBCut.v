(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEntBCut.v at d1ed1a6d9011 for reac-pw/fuzz_rate's
   image A: module paths changed; the cut states are lib/A/RtPgSeg.v's and the block context and entry premise are
   lib/A/RtPgW6aBase.v's w6_ctx and lib/A/RtPgW6bBase.v's w6b_in (rate's registers and real-frame cells); the image
   record is RtPgImgA.rate_himg_A (six write ranges, the 56-byte frame shadow); the entry bridge also carries the
   image's strings, the vocab cells and their registered global to the cut (w6b_s_ok, w6b_vocab_ok) and e's shadow
   hull; the join bridge starts from RtPgSteps.rts_post's state (a new layout and frame list, w6b_clob, w6b_wr,
   w6b_J_R). *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the two bridges between
   lib/A/RtPgSeg.v's cut states at ent_build's case entries (rs_cut_D, pcs 0x81334 .. 0x81954) and at the join J
   (rs_cut_J, 0x81e00) and the block statements of lib/A/RtPgW6bBase.v. Proves no function (kind: segment lemma).

   eb_D: what rs_start_M01 and rs_cut_D give at a case entry, in the form w6b_case_stmt asks: the kind byte b with
     rr = b :: r, the block context w6_ctx (the harness's journal, the real frame, the frame for locals, rom_view at
     the cut), the entry premise w6b_in (rate's registers and the cells R+0x60, 0xb0, 0xc0, 0xe8, 0x108, 0x118,
     0x138, e = 0^104 in scope with its shadow hull, the input left with its shadow and hull, apart from the frame's
     objects) and the image data the cases read (ent_build.s, ent_build.vocab and its nine strings), each carried
     from the segment's start: image bytes lie outside the callees' stack, the frame, pp and the real frame; a shadow
     byte of the image or of the input lies in the shadow band, and one that is marked usable is not one of the
     frame's shadow bytes at the start (all 0xf1 .. 0xf8).
   eb_J_of: rs_cut_J at the join from a case's rts_post: the journal, the registers outside w6b_clob as at the case
     entry, the bytes outside w6b_wr as at the case entry, and w6b_J_R (s6, s7, s10, s11, s9, s8 and e =
     Layout.ent_mem of the pod Model.ent_build makes of rr). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YE00 YE01 YM05 YP03 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgMem RtPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgSeg RtPgW6aBase RtPgW6bBase.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
(* the cut record's projections, with the segments implicit as inside lib/A/RtPgSeg.v *)
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

(* image A's loaded segments, as RtPgSteps names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ============================== image and frame facts ============================== *)
(* the frame's shadow at a case entry: e's granules in scope, the rest the prologue's *)
Lemma eb_PJ : rs_PJ = rtm_sh false false false true false false false.
Proof. vm_compute. reflexivity. Qed.
Lemma eb_PJ_len : Z.of_nat (length rs_PJ) = 56.
Proof. vm_compute. reflexivity. Qed.
Lemma eb_shA_len : Z.of_nat (length rate_A_shA) = 56.
Proof. vm_compute. reflexivity. Qed.

(* M01's write ranges besides pp (RtPgImgA hi_w1), as six intervals *)
Lemma eb_inw : forall e a, rt_inw e (hi_w1 rate_himg_A) a <->
  (q_F e + 0x20 <= a < q_F e + 0x158) \/ (shadow_addr (q_F e) + 4 <= a < shadow_addr (q_F e) + 43) \/
  (q_R e + 0x10 <= a < q_R e + 0x38) \/ (q_R e + 0x60 <= a < q_R e + 0x120) \/
  (q_R e + 0x128 <= a < q_R e + 0x140) \/ (q_R e + 0x158 <= a < q_R e + 0x178).
Proof.
  intros e a. unfold rt_inw. cbn [hi_w1 rate_himg_A]. rewrite !Exists_cons, Exists_nil. cbn [fst snd rt_xv].
  split; intros H; lia.
Qed.

(* the 72 bytes of ent_build.vocab (.data.rel.ro) lie in a loaded segment *)
Lemma eb_img_vocab : forall i, 0 <= i < 72 -> in_img rsegs (W6B_VOCAB + i).
Proof.
  intros i Hi.
  assert (Hb : existsb (fun sg => (Z.of_N (seg_base sg) <=? W6B_VOCAB) &&
                                  (W6B_VOCAB + 72 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) rsegs = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in Hb as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hin | lia].
Qed.

(* ent_build.vocab's nine cells and strings among the image's registered cells and strings *)
Lemma eb_vocab_cells : forall i, 0 <= i < 9 -> In (W6B_VOCAB + 8 * i, w6b_vptr i) rate_A_cells.
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
  repeat (destruct E as [-> | E]; [vm_compute; repeat (first [left; reflexivity | right]) |]).
  subst i. vm_compute. repeat (first [left; reflexivity | right]).
Qed.
Lemma eb_vocab_strs : forall i, 0 <= i < 9 ->
  In (w6b_vptr i, map (fun x : byte => bv_unsigned x) (nth (Z.to_nat i) vocab [])) rate_A_strs.
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
  repeat (destruct E as [-> | E]; [vm_compute; repeat (first [left; reflexivity | right]) |]).
  subst i. vm_compute. repeat (first [left; reflexivity | right]).
Qed.

(* the shadow hull of an application range below 2^47 lies in the shadow band *)
Lemma eb_hull_band : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 - 1 ->
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

Lemma eb_suffix_trans : forall (rest rr r' : list byte), rs_suffix rest rr -> is_rest r' rr -> rs_suffix rest r'.
Proof.
  intros rest rr r' (j & Hj & Erj) (k & Ek). subst rr r'. rewrite skipn_skipn.
  destruct (Nat.le_gt_cases (k + j) (length rest)) as [Hle|Hgt].
  - exists (k + j)%nat. split; [exact Hle | reflexivity].
  - exists (length rest). split; [lia|]. rewrite !skipn_all2 by lia. reflexivity.
Qed.

(* a byte outside a write set {not a word address} \/ P \/ Q *)
Lemma eb_notwr : forall (P Q : Z -> Prop) x, ~ (~ (0 <= x < 2 ^ 64) \/ P x \/ Q x) ->
  0 <= x < 2 ^ 64 /\ ~ P x /\ ~ Q x.
Proof.
  intros P Q x H. split; [| split; intros X; apply H; right; [left | right]; exact X].
  destruct (Z_le_gt_dec 0 x); destruct (Z_lt_ge_dec x (2 ^ 64)); try lia; exfalso; apply H; left; lia.
Qed.

(* ============================== the first block's image is PP_SIZE bytes ============================== *)
Lemma eb_pc_len : forall sh ps es, rs_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat -> (length ps <= 2)%nat ->
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

Lemma eb_at : forall H mem regs e (L : list (rt_loc * Z)) l v,
  rs_at rsegs H mem regs e L -> In (l, v) L -> rt_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HA Hin. exact (proj1 (Forall_forall _ _) HA (l, v) Hin). Qed.

Lemma eb_frame_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos Hle. unfold frame_addr. destruct Hle as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. Qed.

Lemma eb_val_small : forall H mem a v, 0 <= v < 2 ^ 64 ->
  val_mem rsegs (mrestrict H mem) a 8 (v mod 2 ^ 64) -> val_mem rsegs (mrestrict H mem) a 8 v.
Proof. intros H mem a v Hv V. rewrite Z.mod_small in V by lia. exact V. Qed.

(* ---- carrying the segment start's shadow facts to a later memory ----
   KB: every shadow-band byte outside the frame's 56 shadow bytes is as at the start; the frame's shadow bytes are
   readable now; at the start they are the prologue's (all >= 8), so a usable byte's shadow byte is not one of them. *)
Lemma eb_ra_kept : forall H mem H' mem' F a n,
  range_addressable (aview rsegs H mem) SHADOW_OFF a n -> rt_fsh rsegs H mem F rate_A_shA ->
  0 <= a -> a + n <= kHighMemEnd ->
  (forall x, kLowMemEnd <= x < kHighMemBeg -> ~ (shadow_addr F <= x < shadow_addr F + 56) ->
     aview rsegs H' mem' x = aview rsegs H mem x) ->
  range_addressable (aview rsegs H' mem') SHADOW_OFF a n.
Proof.
  intros H mem H' mem' F a n RA Hfsh Ha Hn KB.
  apply (rtm_ra_kept rsegs H mem); [exact RA|]. intros x Hx.
  apply KB; [exact (rtm_shadow_band x ltac:(lia)) |].
  pose proof (rtm_ra_not_fsh rsegs H mem F rate_A_shA a n RA Hfsh rtm_sh_P0_big x Hx) as X.
  rewrite eb_shA_len in X. exact X.
Qed.

Lemma eb_cstr_kept : forall H mem H' mem' F a s,
  rt_cstr rsegs H mem a s -> rt_fsh rsegs H mem F rate_A_shA ->
  (forall x, in_img rsegs x -> aview rsegs H' mem' x = aview rsegs H mem x) ->
  (forall x, kLowMemEnd <= x < kHighMemBeg -> ~ (shadow_addr F <= x < shadow_addr F + 56) ->
     aview rsegs H' mem' x = aview rsegs H mem x) ->
  (forall x, shadow_addr F <= x < shadow_addr F + 56 -> aview rsegs H' mem' x <> None) ->
  rt_cstr rsegs H' mem' a s.
Proof.
  intros H mem H' mem' F a s (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9) Hfsh KI KB KF.
  assert (Hlow : a + Z.of_nat (length s) < kLowMemEnd).
  { pose proof (rts_segs_low _ (C6 (Z.of_nat (length s)) ltac:(lia))) as X. lia. }
  unfold kLowMemEnd in Hlow.
  split; [intros i Hi; rewrite KI by (apply C6; lia); exact (C1 i Hi)|].
  split; [rewrite KI by (apply C6; lia); exact C2|].
  split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|]. split; [exact C7|].
  split.
  - apply (eb_ra_kept H mem H' mem' F a _ C8 Hfsh); [lia | unfold kHighMemEnd; lia | exact KB].
  - intros t Ht.
    pose proof (eb_hull_band a (Z.of_nat (length s) + 1) t ltac:(lia) ltac:(lia) ltac:(lia) Ht) as Hb.
    destruct (Z_lt_le_dec t (shadow_addr F)) as [T1|T1];
      [| destruct (Z_lt_le_dec t (shadow_addr F + 56)) as [T2|T2]].
    + rewrite KB by lia. exact (C9 t Ht).
    + exact (KF t ltac:(lia)).
    + rewrite KB by lia. exact (C9 t Ht).
Qed.

Ltac eb_in := cbn [rs_L_D rs_L_Dc rs_L_Dc0 rs_Rc rs_Rc0 rs_Kc rs_Hc rs_podc app];
  repeat (first [left; reflexivity | right]).

(* ============================== the case entry: the frame, pp, R and the carried memory ============================== *)
Lemma eb_D_facts : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  rs_start_M01 rsegs B cx rest ->
  rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem2 md2 (x_k cx) /\
  getr regs2 2 = w64 (q_R (x_e cx)) /\ getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
  spZ (x_regs cx) = q_R (x_e cx) /\
  alloc_ceiling + T_SEG_STK <= q_R (x_e cx) /\ q_R (x_e cx) + 0x1e0 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  q_R (x_e cx) mod 16 = 0 /\ x_sp0 cx - x_STK cx <= q_R (x_e cx) - T_SEG_STK /\
  In (3, x_pos cx) (x_own cx) /\ In (3, x_pos cx) (frames S2) /\ q_F (x_e cx) = frame_addr ly2 3 (x_pos cx) /\
  4096 <= q_F (x_e cx) /\ q_F (x_e cx) + 512 <= alloc_ceiling /\ q_F (x_e cx) mod 32 = 0 /\
  in_app (q_F (x_e cx)) 512 /\
  In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2) /\ 4096 <= q_pp (x_e cx) /\
  q_pp (x_e cx) + Layout.PP_SIZE <= alloc_ceiling /\ in_app (q_pp (x_e cx)) Layout.PP_SIZE /\
  zdisjoint (q_pp (x_e cx), Layout.PP_SIZE) (q_F (x_e cx), 512) /\
  (forall x, in_img rsegs x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W cx)) (x_memc cx) x) /\
  (forall x, kLowMemEnd <= x < kHighMemBeg ->
     ~ (shadow_addr (q_F (x_e cx)) <= x < shadow_addr (q_F (x_e cx)) + 56) ->
     aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W cx)) (x_memc cx) x) /\
  rt_fsh rsegs (w_H W2) mem2 (q_F (x_e cx)) rs_PJ /\
  rt_fsh rsegs (w_H (x_W cx)) (x_memc cx) (q_F (x_e cx)) rate_A_shA /\
  rom_view rsegs W2 mem2.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof asan_consts as (Hceil & _).
  destruct HST as (HPRE & Hfsh0 & HL1 & Hlen & HIN).
  destruct HPRE as (HJc & Hnev & HR2 & Hgp & Htp & ES & ER16 & ERS & ESTK & Hown & EF & Hpp0 & Hppb & Hhdr
    & Haro & Hglobs & Hrz & Hstrs & Hcells & Hrom & Hnfresh & Hi32 & Hu64).
  destruct HD as (HPB & HAT & HFSH & HPP & HE0 & Hsrr & Hfu & Hkd & Hrr).
  destruct HPB as (HCORE & HIN' & Hsr & Hsrr' & Hwf & Hlen' & Hps & Htie & Hsh & Hnp & Hlp & Hnp3 & Hsh7 & Hps2 & Hcnt
    & Hesw & Hes32 & Hesc).
  destruct HCORE as (HJ & Hspr & Hfr & Hperm & Hio & Hmo & Hkept).
  pose proof HJ as (HAR & Hlyle & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hc1 & Hc2 & Hc3 & Hc4 & _).
  pose proof HJc as (_ & Hlyle_c & _).
  cbn [hi_cid hi_rsz hi_shA rate_himg_A] in Hown, EF, ERS, Hfsh0.
  assert (HTS : T_SEG_STK = 16384) by reflexivity.
  assert (HRb : alloc_ceiling + T_SEG_STK <= q_R (x_e cx) /\ q_R (x_e cx) + 0x1e0 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47)
    by lia.
  assert (HspR : spZ (x_regs cx) = q_R (x_e cx)).
  { unfold spZ. rewrite HR2. unfold w64. apply unsigned_lit_small. lia. }
  (* the frame *)
  assert (HinF : In (3, x_pos cx) (frames S2)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  assert (EF2 : q_F (x_e cx) = frame_addr ly2 3 (x_pos cx)).
  { rewrite EF, (eb_frame_addr_le _ _ _ 3 (x_pos cx) Hlyle_c), (eb_frame_addr_le _ _ _ 3 (x_pos cx) Hlyle). reflexivity. }
  destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 3 (x_pos cx) HAR HinF) as (HF1 & HF2 & HF3).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (x_pos cx) HAR HinF) as (HF32 & _ & HFp & _).
  rewrite <- EF2 in HF1, HF2, HF3, HF32, HFp. change (fs_frame_bytes 3) with 512 in HF1, HF2, HF3, HFp.
  (* pp *)
  assert (Hpp2 : In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
    by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppb]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp2) as (_ & Hp1 & Hp2 & Happ & _).
  assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
  rewrite Hrq in Hp2, Happ.
  pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ 3 (x_pos cx) HAR Hpp2 HinF) as Hsep.
  rewrite Hrq, <- EF2 in Hsep. change (fs_frame_bytes 3) with 512 in Hsep.
  (* an image byte lies outside everything the segment may have written *)
  assert (KI : forall x, in_img rsegs x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W cx)) (x_memc cx) x).
  { intros x Hx. pose proof (rts_segs_low x Hx) as Hlow. unfold kLowMemEnd in Hlow.
    apply Hkept; [lia | rewrite HspR; lia |].
    unfold rs_E1. intros [Hw | Hw].
    - apply eb_inw in Hw. destruct Hw as [Hw | [Hw | Hw]].
      + apply (frm_img rsegs B LAWS _ _ _ _ _ 3 (x_pos cx) x HAR HinF); [| exact Hx].
        rewrite <- EF2. change (fs_frame_bytes 3) with 512. lia.
      + unfold shadow_addr, SHADOW_OFF in Hw. pose proof (Z.div_pos (q_F (x_e cx)) 8 ltac:(lia) ltac:(lia)). lia.
      + lia.
    - exact (blk_img rsegs B LAWS _ _ _ _ _ _ _ x HAR Hpp2 ltac:(rewrite Hrq; lia) Hx). }
  (* a shadow-band byte outside the frame's shadow lies outside everything the segment may have written *)
  assert (KB : forall x, kLowMemEnd <= x < kHighMemBeg ->
     ~ (shadow_addr (q_F (x_e cx)) <= x < shadow_addr (q_F (x_e cx)) + 56) ->
     aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W cx)) (x_memc cx) x).
  { intros x Hx Hnf. unfold kLowMemEnd, kHighMemBeg in Hx.
    apply Hkept; [lia | rewrite HspR; lia |].
    unfold rs_E1. intros [Hw | Hw].
    - apply eb_inw in Hw. destruct Hw as [Hw | [Hw | Hw]].
      + unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HF3. lia.
      + lia.
      + lia.
    - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia. }
  (* rom_view at the cut *)
  assert (HromD : rom_view rsegs W2 mem2).
  { apply (rtm_rom_kept rsegs (x_W cx) W2 (x_memc cx) mem2 Hrom). intros a Ha. apply KI.
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
Lemma eb_D_input : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  rs_start_M01 rsegs B cx rest ->
  rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  (exists b, rr = b :: r /\ bv_unsigned b = kd) /\
  0 < rs_cur rsegs cx rest r - 1 /\
  w6_in W2 mem2 (q_R (x_e cx)) (rs_cur rsegs cx rest r) r /\
  (0 < Z.of_nat (length r) ->
     shadow_hull_vis (aview rsegs (w_H W2) mem2) (rs_cur rsegs cx rest r) (Z.of_nat (length r))) /\
  (forall a, rs_cur rsegs cx rest r <= a < rs_cur rsegs cx rest r + Z.of_nat (length r) ->
     ~ (q_F (x_e cx) + 0x20 <= a < q_F (x_e cx) + 0x158)).
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof asan_consts as (Hceil & _).
  pose proof (eb_D_facts cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
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
  assert (Hcur : rs_cur rsegs cx rest r = q_src (x_e cx) + Z.of_nat j) by (unfold rs_cur; rewrite Hlr; lia).
  set (c := rs_cur rsegs cx rest r) in *.
  assert (Hend : c + Z.of_nat (length r) = q_src (x_e cx) + q_left (x_e cx)) by (rewrite Hcur, Hlr, Hel; lia).
  assert (Hhi : q_src (x_e cx) + q_left (x_e cx) <= 2 ^ 47 - 1).
  { unfold amem_range in Hamr. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. lia. }
  (* the bytes the walk may have changed since the segment's start *)
  set (Wr := fun a => ~ (0 <= a < 2 ^ 64) \/ (q_R (x_e cx) - T_SEG_STK <= a < q_R (x_e cx)) \/ rs_E1 rsegs cx a).
  assert (KE : forall x, ~ Wr x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W cx)) (x_memc cx) x).
  { intros x Hx. unfold Wr in Hx.
    destruct (eb_notwr (fun a => q_R (x_e cx) - T_SEG_STK <= a < q_R (x_e cx)) (rs_E1 rsegs cx) x Hx) as (H1 & H2 & H3).
    apply Hkept; [exact H1 | rewrite HspR; exact H2 | exact H3]. }
  assert (HFE : in_app (q_F (x_e cx) + 0x20) 0x138)
    by (apply (in_app_sub (q_F (x_e cx)) 512); [exact HFapp | lia | lia | lia]).
  (* a shadow byte of an input byte avoids everything the segment may have written *)
  assert (SHW : forall x, q_src (x_e cx) <= x < q_src (x_e cx) + q_left (x_e cx) -> ~ Wr (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. pose proof (rtm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as Hb.
    unfold kLowMemEnd, kHighMemBeg in Hb.
    unfold Wr, rs_E1. intros [Hw | [Hw | [Hw | Hw]]]; [lia | lia | |].
    - apply eb_inw in Hw. destruct Hw as [Hw | [Hw | Hw]].
      + exact (rtm_shadow_not_app x _ _ ltac:(unfold kHighMemEnd; lia) HFE ltac:(lia)).
      + exact (rtm_ra_not_fsh rsegs _ _ _ _ _ _ Hra Hfsh0 rtm_sh_P0_big x Hx ltac:(rewrite eb_shA_len; lia)).
      + lia.
    - exact (rtm_shadow_not_app x _ _ ltac:(unfold kHighMemEnd; lia) Hppapp Hw). }
  split; [exists b; split; [reflexivity | symmetry; exact Ekd]|].
  split; [rewrite Hcur; lia|].
  split.
  { unfold w6_in. split; [| split; [| split; [| split; [| split]]]].
    - (* the bytes *)
      assert (B0 : rtm_bytes rsegs (w_H (x_W cx)) (x_memc cx) (q_src (x_e cx)) rest) by exact Hgar.
      pose proof (rtm_bytes_slice rsegs _ _ _ rest j (length rest - j) B0 ltac:(lia)) as B1.
      unfold rtm_slice in B1. rewrite firstn_all2 in B1 by (rewrite length_skipn; lia). rewrite <- Er in B1.
      rewrite <- Hcur in B1.
      refine (rtm_bytes_kept_wr rsegs Wr _ _ _ _ _ r B1 KE _).
      intros x Hx. destruct (Hdis x ltac:(lia)) as (D1 & D2 & D3).
      unfold Wr, rs_E1. intros [Hw | [Hw | [Hw | Hw]]]; [lia | exact (D1 Hw) | exact (D2 Hw) | exact (D3 Hw)].
    - (* their shadow *)
      apply (rtm_ra_kept_wr rsegs Wr (w_H (x_W cx)) (x_memc cx)); [| exact KE |].
      + apply (range_addressable_sub _ _ _ _ _ _ Hra); lia.
      + intros x Hx. apply SHW. lia.
    - lia.
    - lia.
    - unfold amem_range in *. lia.
    - intros a Ha. destruct (Hdis a ltac:(lia)) as (D1 & D2 & D3).
      pose proof (fun X => D2 (proj2 (eb_inw (x_e cx) a) X)) as D2'.
      split; [exact D1 | split; intros X; apply D2'; tauto]. }
  split.
  { (* the input's shadow hull *)
    intros Hn. apply (rtm_hull_kept rsegs (w_H (x_W cx)) (x_memc cx)).
    + apply (rtm_hull_sub _ _ _ _ _ (Hhull ltac:(lia))); lia.
    + intros s Hs Hns.
      pose proof (eb_hull_band c (Z.of_nat (length r)) s ltac:(lia) Hn ltac:(lia) Hs) as Hb.
      destruct (Z_lt_le_dec s (shadow_addr (q_F (x_e cx)))) as [Hs1 | Hs1];
        [| destruct (Z_lt_le_dec s (shadow_addr (q_F (x_e cx)) + 56)) as [Hs2 | Hs2]].
      2: { replace s with (shadow_addr (q_F (x_e cx)) + (s - shadow_addr (q_F (x_e cx)))) by lia.
           rewrite (HFSHD (s - shadow_addr (q_F (x_e cx))) ltac:(rewrite eb_PJ_len; lia)). discriminate. }
      all: rewrite KB; [exact Hns | exact Hb | lia]. }
  intros a Ha. destruct (Hdis a ltac:(lia)) as (_ & D2 & _).
  intros X. apply D2. apply eb_inw. left. exact X.
Qed.

(* ============================== the case entry: the image data the cases read ============================== *)
Lemma eb_D_img : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  rs_start_M01 rsegs B cx rest ->
  rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  w6b_s_ok W2 mem2 /\ w6b_vocab_ok W2 mem2.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof (eb_D_facts cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
     & _ & _ & _ & _ & _ & KI & KB & HFSHD & Hfsh0 & _).
  destruct HST as (HPRE & _).
  destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hglobs & _ & Hstrs & Hcells & _).
  cbn [hi_globs hi_strs hi_cells rate_himg_A] in Hglobs, Hstrs, Hcells.
  assert (KF : forall x, shadow_addr (q_F (x_e cx)) <= x < shadow_addr (q_F (x_e cx)) + 56 ->
    aview rsegs (w_H W2) mem2 x <> None).
  { intros x Hx. replace x with (shadow_addr (q_F (x_e cx)) + (x - shadow_addr (q_F (x_e cx)))) by lia.
    rewrite (HFSHD (x - shadow_addr (q_F (x_e cx))) ltac:(rewrite eb_PJ_len; lia)). discriminate. }
  rewrite Forall_forall in Hstrs, Hglobs. unfold rt_ro_cells in Hcells. rewrite Forall_forall in Hcells.
  split.
  - unfold w6b_s_ok.
    replace (map (fun x : byte => bv_unsigned x) S9) with [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101]
      by (vm_compute; reflexivity).
    pose proof (Hstrs (0x21200, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101])
      ltac:(unfold rate_A_strs; repeat (first [left; reflexivity | right]))) as HS9.
    exact (eb_cstr_kept _ _ _ _ _ _ _ HS9 Hfsh0 KI KB KF).
  - split.
    + pose proof (Hglobs (W6B_VOCAB, 72) ltac:(unfold rate_A_globs; repeat (first [left; reflexivity | right]))) as HG.
      cbn [fst snd] in HG.
      apply (eb_ra_kept _ _ _ _ _ _ _ HG Hfsh0); [unfold W6B_VOCAB; lia | unfold W6B_VOCAB, kHighMemEnd; lia | exact KB].
    + intros i Hi. split.
      * pose proof (Hcells _ (eb_vocab_cells i Hi)) as V. cbn [fst snd] in V.
        apply (rtm_val_of_bytes rsegs). apply (rtm_bytes_kept rsegs (w_H (x_W cx)) (x_memc cx)).
        { apply rtm_bytes_of_val. exact V. }
        intros x Hx. rewrite length_Z_to_le_bytes in Hx. apply KI.
        replace x with (W6B_VOCAB + (x - W6B_VOCAB)) by lia. apply eb_img_vocab. lia.
      * exact (eb_cstr_kept _ _ _ _ _ _ _ (Hstrs _ (eb_vocab_strs i Hi)) Hfsh0 KI KB KF).
Qed.

(* ============================== the case entry: everything w6b_case_stmt asks ============================== *)
Lemma eb_D : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2,
  rs_start_M01 rsegs B cx rest ->
  rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  (exists b, rr = b :: r /\ bv_unsigned b = kd) /\
  w6_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_k cx)
    ly2 S2 W2 mem2 md2 (q_R (x_e cx)) (q_F (x_e cx)) (x_pos cx) /\
  w6b_in B W2 mem2 regs2 (q_R (x_e cx)) (q_F (x_e cx)) (rs_cur rsegs cx rest r)
    (shadow_addr (q_pp (x_e cx) + 0x4000)) (q_pp (x_e cx)) kd r /\
  w6b_s_ok W2 mem2 /\ w6b_vocab_ok W2 mem2.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD.
  pose proof asan_consts as (Hceil & _).
  pose proof (eb_D_facts cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (HJ & R2 & R3 & R4 & HspR & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp
     & Hpp & Hpp1 & Hpp2 & Hppapp & Hsep & KI & KB & HFSHD & Hfsh0 & HromD).
  pose proof (eb_D_input cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (Hb & Hc1 & Hwin & Hhull & Hdis).
  pose proof (eb_D_img cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as (HS & HV).
  destruct HD as (_ & HAT & _ & _ & HE0 & _ & _ & Hkd & _).
  assert (AT : forall l v, In (l, v) (rs_L_D rsegs cx sh np ps cnt es rest r kd) ->
    rt_at rsegs (w_H W2) mem2 regs2 (x_e cx) l v)
    by (intros l v Hin; exact (eb_at _ _ _ _ _ l v HAT Hin)).
  assert (HTS : T_SEG_STK = 16384) by reflexivity.
  assert (HPPS : Layout.PP_SIZE = 19744) by reflexivity.
  assert (HF8 : q_F (x_e cx) mod 8 = 0).
  { pose proof (Z.div_mod (q_F (x_e cx)) 32 ltac:(lia)). pose proof (Z.div_mod (q_F (x_e cx)) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (q_F (x_e cx)) 8 ltac:(lia)). lia. }
  assert (Hvb : 0 <= shadow_addr (q_pp (x_e cx) + 0x4000) < 2 ^ 64).
  { unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (q_pp (x_e cx) + 0x4000) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (q_pp (x_e cx) + 0x4000) 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
  split; [exact Hb|].
  split.
  { unfold w6_ctx. split; [exact HJ|]. split; [exact BR4|]. split; [exact BR2|]. split; [exact BR5|].
    split; [exact Hown|]. split; [exact EF2|]. exact HromD. }
  split; [| split; [exact HS | exact HV]].
  unfold w6b_in.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  split; [exact (AT (LReg 9) _ ltac:(eb_in))|].
  split; [exact (AT (LReg 18) _ ltac:(eb_in))|].
  split; [exact (AT (LReg 25) _ ltac:(eb_in))|].
  split; [exact (AT (LReg 14) _ ltac:(eb_in))|].
  split; [exact (AT (LReg 24) _ ltac:(eb_in))|].
  split; [exact (AT (LReg 15) _ ltac:(eb_in))|].
  split; [exact (AT (LReg 23) _ ltac:(eb_in))|].
  split; [exact (AT (LReg 27) _ ltac:(eb_in))|].
  split; [exact (AT (LReg 26) _ ltac:(eb_in))|].
  split.
  { intros H9. apply (AT (LReg 22)). unfold rs_L_D. apply in_or_app. right. apply in_or_app. right.
    apply Z.eqb_neq in H9. rewrite H9. right. left. reflexivity. }
  split; [apply eb_val_small; [lia | exact (AT (LCell XR 0x60) _ ltac:(eb_in))]|].
  split; [apply eb_val_small; [lia | exact (AT (LCell XR 0xb0) _ ltac:(eb_in))]|].
  split; [apply eb_val_small; [lia | exact (AT (LCell XR 0xc0) _ ltac:(eb_in))]|].
  split; [apply eb_val_small; [exact Hvb | exact (AT (LCell XR 0xe8) _ ltac:(eb_in))]|].
  split; [apply eb_val_small; [lia | exact (AT (LCell XR 0x108) _ ltac:(eb_in))]|].
  split; [exact (AT (LCell XR 0x118) _ ltac:(eb_in))|].
  split; [apply eb_val_small; [lia | exact (AT (LCell XR 0x138) _ ltac:(eb_in))]|].
  split; [exact Hvb|]. split; [exact Hkd|]. split; [exact Hpp1|].
  split; [unfold Layout.PP_SIZE in Hpp2; lia|].
  split; [exact HF1|]. split; [exact HF2|]. split; [exact HF32|]. split; [exact HFapp|].
  split.
  { (* e = 0^104 *)
    intros i Hi.
    destruct (HE0 (Z.to_nat i) ltac:(unfold rs_u8s, zeros; rewrite length_map, rtm_length_repeat; lia)) as [V _].
    rewrite Z2Nat.id in V by lia. specialize (V 0%nat ltac:(lia)). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
    rewrite V. f_equal. unfold rs_u8s. rewrite (rtm_nth_map (zeros 104) (Z.to_nat i)).
    unfold zeros. rewrite (rtm_nth_repeat _ _ 104 (Z.to_nat i)) by lia. reflexivity. }
  split.
  { (* e's shadow: its 13 granules are in scope *)
    pose proof HFSHD as HF'. rewrite eb_PJ in HF'.
    pose proof (rtm_A_ra_e rsegs (w_H W2) mem2 _ false false false false false false 0 104 HF' HF8 ltac:(lia) ltac:(lia))
      as X.
    unfold RTM_E in X. rewrite Z.add_0_r in X. exact X. }
  split.
  { (* e's shadow hull lies inside the frame's 56 shadow bytes *)
    intros s Hs.
    assert (Hin : shadow_addr (q_F (x_e cx)) <= s < shadow_addr (q_F (x_e cx)) + 56).
    { unfold shadow_addr in *.
      pose proof (Z.div_mod (q_F (x_e cx)) 8 ltac:(lia)) as D0.
      pose proof (Z.div_mod (q_F (x_e cx) + 0xf0) 8 ltac:(lia)) as D1.
      pose proof (Z.mod_pos_bound (q_F (x_e cx) + 0xf0) 8 ltac:(lia)) as M1.
      pose proof (Z.div_mod (q_F (x_e cx) + 0xf0 + 104 - 1) 8 ltac:(lia)) as D2.
      pose proof (Z.mod_pos_bound (q_F (x_e cx) + 0xf0 + 104 - 1) 8 ltac:(lia)) as M2.
      pose proof (Z.div_mod (SHADOW_OFF + (q_F (x_e cx) + 0xf0) / 8) 8 ltac:(lia)) as D3.
      pose proof (Z.mod_pos_bound (SHADOW_OFF + (q_F (x_e cx) + 0xf0) / 8) 8 ltac:(lia)) as M3.
      pose proof (Z.div_mod (SHADOW_OFF + (q_F (x_e cx) + 0xf0 + 104 - 1) / 8) 8 ltac:(lia)) as D4.
      pose proof (Z.mod_pos_bound (SHADOW_OFF + (q_F (x_e cx) + 0xf0 + 104 - 1) / 8) 8 ltac:(lia)) as M4.
      lia. }
    replace s with (shadow_addr (q_F (x_e cx)) + (s - shadow_addr (q_F (x_e cx)))) by lia.
    rewrite (HFSHD (s - shadow_addr (q_F (x_e cx))) ltac:(rewrite eb_PJ_len; lia)). discriminate. }
  split; [exact Hc1|]. split; [exact Hwin|]. split; [exact Hhull|]. exact Hdis.
Qed.

(* ============================== the join ============================== *)
Lemma eb_J_of : forall cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
  rs_start_M01 rsegs B cx rest ->
  rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly3 S3 W3 mem3 md3 (x_k cx) ->
  (forall rg : bv 5, bv_unsigned rg <> 0 -> ~ In rg w6b_clob -> getr regs3 rg = getr regs2 rg) ->
  frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 ->
  mo_le MT S2 S3 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ w6b_wr (q_R (x_e cx)) (q_F (x_e cx)) a ->
     aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  w6b_J_R (q_R (x_e cx)) (q_F (x_e cx)) (rs_cur rsegs cx rest r) (shadow_addr (q_pp (x_e cx) + 0x4000))
    (q_pp (x_e cx)) r rr W3 regs3 mem3 ->
  rs_cut_J rsegs B MT cx sh np ps cnt es rest rr (snd (ent_build rr)) (fst (ent_build rr)) ly3 S3 W3 regs3 mem3 md3.
Proof.
  intros cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HST HD HJ3 Hr3 Hf3 Hp3
    Hio3 Hmo3 Hm3 HR3.
  pose proof asan_consts as (Hceil & _).
  pose proof (eb_D_facts cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
    (HJ & R2 & R3 & R4 & HspR & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp
     & Hpp & Hpp1 & Hpp2 & Hppapp & Hsep & KI & KB & HFSHD & Hfsh0 & HromD).
  assert (HTS : T_SEG_STK = 16384) by reflexivity.
  destruct HD as (HPB & HAT & HFSH & HPP & HE0 & Hsrr & Hfu & Hkd & Hrr).
  destruct HPB as (HCORE & HIN' & Hsr & Hsrr' & Hwf & Hlen' & Hps & Htie & Hsh & Hnp & Hlp & Hnp3 & Hsh7 & Hps2 & Hcnt
    & Hesw & Hes32 & Hesc).
  destruct HCORE as (_ & Hspr & Hfr & Hperm & Hio & Hmo & Hkept).
  destruct HR3 as (R22 & R23 & R26 & R27 & R25 & R24 & E3).
  (* the registers outside w6b_clob that the cut lists *)
  assert (Hregs : forall n, In n [2; 3; 4; 8; 9; 18; 19; 20; 21] ->
    getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<- | Hn];
      [apply Hr3; [vm_compute; lia | intros Hin; apply (in_map (@bv_unsigned 5)) in Hin; vm_compute in Hin; lia] |]).
    destruct Hn. }
  pose proof (eb_pc_len sh ps es Hwf Hesw Hes32 Hps2) as Hlpp.
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
      rewrite HspR in Hs. unfold w6b_wr. intros [Hw | [Hw | Hw]]; [exact (Hs Hw) | |];
        apply HE1; unfold rs_E1; left; apply (proj2 (eb_inw _ _)); lia. }
    split; [exact HIN'|].
    split; [exact (eb_suffix_trans rest rr _ Hsrr' (ent_build_rest rr))|].
    repeat (split; [eassumption|]). exact Hesc.
  - (* the registers and cells *)
    unfold rs_at_cx, rs_at. apply Forall_forall. intros [l v] Hf.
    apply in_app_or in Hf as [Hf | Hf].
    + assert (A : rt_at rsegs (w_H W2) mem2 regs2 (x_e cx) l v).
      { apply (eb_at _ _ _ _ _ l v HAT). unfold rs_L_D. apply in_or_app. left. exact Hf. }
      apply (rtm_at_kept rsegs _ _ _ _ regs2 regs3 (x_e cx) l v A).
      cbn [rs_L_Dc rs_L_Dc0 rs_Rc0 rs_Kc rs_Hc rs_podc app In] in Hf.
      repeat (destruct Hf as [Hf | Hf];
        [injection Hf as <- <-; cbn [rtm_keeps rt_xv];
         first [ solve [apply Hregs; cbn [In]; lia]
               | solve [intros i Hi; apply Hm3; [lia | unfold w6b_wr; lia]]
               | solve [etransitivity; [exact R23 | symmetry; exact A]]
               | solve [etransitivity; [exact R27 | symmetry; exact A]] ] |]).
      destruct Hf.
    + cbn [In] in Hf. destruct Hf as [E | [E | [E | [E | []]]]]; injection E as <- <-; cbn [fst snd rt_at].
      * exact R22.
      * etransitivity; [exact R25|]. f_equal. unfold rs_cur. lia.
      * exact R24.
      * exact R26.
  - (* the frame's shadow *)
    unfold rs_fsh_at. apply (rtm_fsh_kept rsegs (w_H W2) mem2); [exact HFSH|].
    intros i Hi. rewrite eb_PJ_len in Hi.
    unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (q_F (x_e cx)) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (q_F (x_e cx)) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_mod (q_F (x_e cx)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q_F (x_e cx)) 8 ltac:(lia)).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
    apply Hm3; [lia | unfold w6b_wr; lia].
  - (* the first block *)
    unfold rs_pp_at. unfold rs_pp_at in HPP.
    apply (rtm_bytes_kept rsegs (w_H W2) mem2); [exact HPP|].
    intros x Hx. rewrite Hlpp in Hx. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
    apply Hm3; [lia | unfold w6b_wr; lia].
  - exact E3.
  - symmetry. apply surjective_pairing.
  - exact (ent_build_wf rr).
Qed.
End w.

Print Assumptions eb_D.
Print Assumptions eb_J_of.
