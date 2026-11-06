(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX; memnorm only as EXB's keep (exv_rm) and KIT_EXB_CALL's keep premise (old-pin kit
   4f18c75d4900 rebind, 2026-10-29), not an EXV_HYP field (EXV_HYP has neither since b29a52d6b76b / 379ec9e4a7d5). *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value: the PROOF of the shared call kit's KIT_EXB_CALL
   (lib/B/Prog/ExvB_Loop_kit.v, ExvLoop's statement): EXB re-established at the state after a program call made from a
   cut with sp = s1 in YCbqGcallW.v's window form, and the bytes [exv_s1 E, exv_sp E) unchanged. exv_kit_call; shared
   with the lanes ExvOpen / ExvDisp, which cite the name.
   Where each conjunct of EXB comes from at the post-call state (ly2, S2, Hp2, W2, regs2, mem2):
   - the journal from the entry: given (the composed k + k1 journal);
   - the caller window [exv_sp, exv_sp + e_d) outside exv_FP: the call's window keep (FP1 is inside exv_FP) and EXB's
     own clause; the bytes [exv_s1, exv_sp) (spills, saved registers, 176(s1)): the window keep, since exv_FP is the
     scratch (below alloc_ceiling) and the cursor cells (at or above the entry sp);
   - fregs_kept_x (e_fx E) fx2: composed (kp_fregs_trans); Hp / ablocks / ledger: the callee's Q; exv_rm: the room by
     exv_room_trans of EXB's (e_S E -> Sc) with the premise's (Sc -> S2), the memnorm keep by the premise; count_cid:
     the callee journal's frame clause (frames S2 = frames Sc); registers: aregs_preserved, and the frame and flag
     addresses are the same at ly2 (alx_layout, as ExvEntry's exve_flag_layout);
   - the flag pointer at frame + 120: the callee journal's frame clause (the frame is no block, so not the scratch;
     below alloc_ceiling, so not a cursor cell);
   - the text bytes: the block clause (blocks equal); its shadow and the scratch's: exv_sh_blk at the new state; the
     scratch writable by the block law's presence, not owned;
   - the cursor's 40 bytes: the real stack's zero shadow (alx_zshadow_byte, as ExvEntry's exve_stack_ra);
   - the tree: pj_nodeR by PRH_Reader.pj_nodeR_frame with the footprint kept (Lam blocks by the block clause, apart from
     exv_FP by EXV_PRE; the root by its home: Lam block / fake frame (frame clause) / real stack (window keep or the
     journal's >= alloc_ceiling clause)), writability carried off the image; the root's home at the new state; its
     shadow: exv_sh_lam / the frame's shadow bytes kept by the frame clause with eh_frame_hull / alx_zshadow_byte with
     eh_stk_hull.
   Rule 24: proves no function (kind: segment lemma). Numerals: 56 (LENGTH: tree node), 40 (LENGTH: struct ex), 120,
   128 (LENGTH: flag-pointer slot, class-1 frame), 176, 184, 288, 319 (LENGTH: ex_value's frame slots and realignment,
   via exv_s1_le / exv_saved_rng), 304, 16384, 16688 (LENGTH / DERIVED: ex_value's frame and stack need, ExvEntry's
   exve_stk_lo restated), 8, 32 (LENGTH: granule, frame alignment), 1 (WORD: frame class), 2 ^ 47, 2 ^ 64 (LENGTH:
   address-space bounds), 2, 3, 4, 8, 9, 18, 19, 24, 25, 26 (WORD: register numbers). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Open_sh ExvB_Open_kt.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Existing Instance prh_img_B.

Local Ltac kp_in := unfold exv_bregs; cbn [In]; repeat (first [left; reflexivity | right]).

(* ex_value's stack need at every nesting (ExvEntry's exve_stk_lo, cold/h-rw-pre-7-b-ex_value-entry 1bf53728a5a,
   restated: that file is not on this base) *)
Lemma kp_stk_lo : forall n : nat, 16688 <= STK_ex_value n.
Proof.
intros n. unfold STK_ex_value.
assert (Hf : @pi_frame prh_img_B F_ex_value = 304) by reflexivity.
assert (Hz : zmaxl [STK_RT_ECALL; STK_RT_STR; STK_RT_STRTOD; @STK_ex_string prh_img_B; @STK_ex_word prh_img_B;
  @STK_ex_ws prh_img_B] = 16384) by (vm_compute; reflexivity).
rewrite Hf, Hz. pose proof (Nat2Z.is_nonneg n) as Hn. rewrite Nat2Z.inj_succ. nia.
Qed.

(* the callee-saved float registers kept twice are kept *)
Lemma kp_fregs_trans : forall f1 f2 f3 : YK11.FPState,
  fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

(* the footprint of the entry is the scratch and the cursor's 40 bytes *)
Lemma kp_inFP_E : forall E a, inFP (exv_FP E) a ->
  (e_scr E <= a < e_scr E + exv_len E + 1) \/ (e_q E <= a < e_q E + 40).
Proof.
intros E a H. unfold exv_FP in H. rewrite !inFP_cons in H.
destruct H as [H|[H|[H|[H|H]]]]; [left; exact H | right; lia | right; lia | right; lia | destruct (inFP_nil a H)].
Qed.

(* a frame of at least a node's size is a whole number of granules (its class is not negative) *)
Lemma kp_fsb_mod : forall cid, 56 <= fs_frame_bytes cid -> fs_frame_bytes cid mod 8 = 0.
Proof.
intros cid H. unfold fs_frame_bytes in *.
destruct (Z_lt_le_dec cid 0) as [Hc|Hc].
- exfalso. replace cid with (- (- cid)) in H by lia. rewrite Z.shiftl_opp_r in H.
  rewrite Z.shiftr_div_pow2 in H by lia.
  assert (Hp : 2 ^ 1 <= 2 ^ (- cid)) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 1) with 2 in Hp.
  assert (Hq : 64 / 2 ^ (- cid) <= 32) by (apply Z.div_le_upper_bound; lia).
  lia.
- rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

(* ---- keep idioms across two worlds (ex_ws_x.v's exw_val_kept / exw_garr8_kept / exw_ra_kept with the hidden map of
   the second state its own: a program call grows the world) ---- *)
Section g. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.

Lemma kp_val_kept2 : forall H H' (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs H' m' x = aview segs H m x) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v HE Hv kk Hk. rewrite (mbyte_of_aview segs H H' m m' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.

Lemma kp_garr8_kept2 : forall H H' (m m' : word -> option byte) p L,
  (forall a, p <= a < p + Z.of_nat (length L) -> aview segs H' m' a = aview segs H m a) ->
  garr8 segs (mrestrict H m) p L -> garr8 segs (mrestrict H' m') p L.
Proof.
intros H H' m m' p L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. cbn in Hk.
rewrite (mbyte_of_aview segs H H' m m' (p + Z.of_nat j + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.

Lemma kp_ra_kept2 : forall H H' (m m' : word -> option byte) a n,
  (forall x, a <= x < a + n ->
     aview segs H' m' (shadow_of_addr SHADOW_OFF x) = aview segs H m (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable (aview segs H m) SHADOW_OFF a n -> range_addressable (aview segs H' m') SHADOW_OFF a n.
Proof. intros H H' m m' a n HE HR x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite (HE x Hx). auto. Qed.

(* off the image, a writable byte whose view is kept stays writable (YE7f.v's apresent_of_writable, over segs) *)
Lemma kp_wr_keep : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img segs a -> aview segs H' m' a = aview segs H m a ->
  writable_at segs (mrestrict H m) a -> writable_at segs (mrestrict H' m') a.
Proof.
intros H H' m m' a Ha Hn He Hw.
assert (Hp : apresent H m a).
{ unfold apresent. unfold writable_at, wview, mrestrict in Hw.
  rewrite (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YP03.unsigned_lit_small a Ha) in Hw.
  rewrite (find_segment_none segs a Hn) in Hw.
  destruct (H (Z_to_bv 64 a)) eqn:E; try rewrite E in Hw; [exfalso; apply Hw; reflexivity|].
  split; [reflexivity|]. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity|].
  try rewrite Eb in Hw. exfalso. apply Hw. reflexivity. }
exact (apresent_writable segs H' m' a (apresent_transfer segs H H' m m' a Ha Hn He Hp)).
Qed.
End g.

Section kp. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.

(* the layout a journal ends at names the same frames and flag bytes (ExvEntry's exve_flag_layout, restated) *)
Lemma kp_flag_layout : forall ly ly' (S : astate) Hp (W : world rsegs) mem md cid pos,
  ARx ly S Hp W mem md -> layout_le (length (st_secs S)) ly ly' ->
  frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos.
Proof.
intros ly ly' S Hp W mem md cid pos HAR Hle.
destruct (alx_layout rsegs B ARx (eh_laws B ARx SK HYP) ly S Hp W mem md ly' HAR Hle) as (_ & Hfr & _).
pose proof (Hfr cid pos) as Hf. split; [exact Hf|].
unfold frame_addr in Hf. unfold flag_addr. assert (HF : ly_F ly' = ly_F ly) by lia. rewrite HF. reflexivity.
Qed.

(* a range on the real stack is addressable at every allocator state (ExvEntry's exve_stack_ra, restated) *)
Lemma kp_stack_ra : forall ly S Hp (W : world rsegs) mem md (x n : Z),
  ARx ly S Hp W mem md -> ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S Hp W mem md x n HAR Hlo Hhi z Hz. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr.
apply (alx_zshadow_byte rsegs B ARx (eh_laws B ARx SK HYP) ly S Hp W mem md z HAR). lia.
Qed.

(* KIT_EXB_CALL *)
Lemma exv_kit_call : forall fx : YK11.FPState, KIT_EXB_CALL (fx := fx) B ARx SK.
Proof.
intros fx. unfold KIT_EXB_CALL.
intros E lyc Sc Hpc Wc regs memc mdc k pos fx2 FP1 STK1 ly2 S2 Hp2 W2 regs2 mem2 md2 k1
  HPRE HB HFP1 HJ2 HJ1 HWK HR HFK HFZ2 HRM2 HMN2 HHp2 HAB2 HLED2.
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as CH0.
pose proof (exv_s1_le E) as ((S1a & S1b) & S1m).
pose proof (kp_stk_lo (e_n E)) as HSTK.
assert (HLEN : exv_len E = Z.of_nat (length (e_x E))) by reflexivity.
assert (HLEN0 : 0 <= exv_len E) by lia.
unfold EXV_PRE in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFP & _ & _ & _ & _ & _ & _ & _ & Hspq & Hqd & Hwin & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsx & _
  & Hv0 & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _).
destruct Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop).
destruct Hwin as (Hd0 & Hd16 & Hdtop & _).
unfold EXB in HB |- *. cbv zeta in HB |- *.
destruct HB as (HJ & HWIN & HFR & HFZ & HHp & HAB & HRM & HLED & HCNT & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19
  & R3 & R4 & HSV & H176 & HFL & HSRC & HTB & HWD & HSB & HQR & HTREE).
pose proof (proj1 HJ) as HARc. cbv beta in HARc.
pose proof HJ as (_ & HlyC & _ & _ & _ & HfrsC & _).
destruct HlyC as (_ & _ & _ & _ & _ & _ & _ & _ & EtopC & EloC & EhiC & _).
destruct HJ1 as (HAR2 & Hly1 & _ & _ & _ & Hfrs1 & _ & _ & F1 & F2 & _ & F4 & _ & _ & _ & _ & _).
pose proof Hly1 as Hly1'.
destruct Hly1' as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & Elo2 & Ehi2 & _).
unfold exv_sp, exv_STK in *.
(* the registers, the frame, the layout *)
assert (SPc : spZ regs = exv_s1 E).
{ unfold spZ. rewrite R2. apply OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YP03.unsigned_lit_small.
  lia. }
assert (SP2 : spZ regs2 = spZ regs) by (unfold spZ; rewrite (HR 2%bv ltac:(kp_in)); reflexivity).
destruct (kp_flag_layout lyc ly2 Sc Hpc Wc memc mdc 1 pos HARc Hly1) as (FR2 & FL2).
assert (Hfrs : frames S2 = frames Sc) by (rewrite Hfrs1; reflexivity).
assert (Hin1 : In (1, pos) (frames Sc)) by (rewrite HfrsC; left; reflexivity).
(* the scratch: inside a live block, an application range, below alloc_ceiling *)
pose proof HSB as (bs & ms & Hins & Hs1 & Hs2 & _).
assert (Hreqs : ms <= req_size ms) by (unfold req_size; destruct (Z.eqb_spec ms 0); lia).
destruct (alx_blocks rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc bs ms HARc Hins) as (_ & _ & _ & Happ & _).
pose proof HWD as (Hscr0 & Hscr & _).
assert (INB2 : forall a n, prhex_inblk B lyc Sc Hpc a n -> prhex_inblk B ly2 S2 Hp2 a n).
{ intros a n H. unfold prhex_inblk in *. rewrite HAB2, HHp2. exact H. }
(* what the call writes lies in exv_FP: the scratch and the cursor's 40 bytes *)
assert (NF1 : forall a, ~ (e_scr E <= a < e_scr E + exv_len E + 1) -> ~ (e_q E <= a < e_q E + 40) -> ~ inFP FP1 a).
{ intros a Hs Hq Hf. destruct (kp_inFP_E E a (HFP1 a Hf)) as [H|H]; [exact (Hs H) | exact (Hq H)]. }
assert (SCRAPP : forall s, kLowShadowBeg < s < kHighMemBeg -> ~ (e_scr E <= s < e_scr E + exv_len E + 1)).
{ intros s Hs Hr. unfold in_app in Happ. lia. }
assert (SHAD : forall x, 0 <= x < alloc_ceiling ->
   kLowShadowBeg < shadow_of_addr SHADOW_OFF x < kHighMemBeg /\ shadow_of_addr SHADOW_OFF x < alloc_ceiling).
{ intros x Hx. unfold shadow_of_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. lia. }
(* the bytes of [exv_s1, exv_sp) are kept *)
assert (KEEPF : forall a, exv_s1 E <= a < spZ (e_regs E) ->
   aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a).
{ intros a Ha. apply HWK; [lia|]. apply NF1; lia. }
(* a byte of a block live at the cut, outside exv_FP, is kept *)
assert (BLK : forall a, (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + m) ->
   ~ (e_scr E <= a < e_scr E + exv_len E + 1) -> ~ (e_q E <= a < e_q E + 40) ->
   aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a).
{ intros a (b & m & Hin & Hab) Hs Hq.
  assert (Hreq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  replace a with (b + (a - b)) by lia.
  apply (F2 b m (a - b)); [exact Hin | rewrite HAB2; exact Hin | lia | ].
  apply NF1; replace (b + (a - b)) with a by lia; assumption. }
(* a byte of a frame live at the cut is kept (no frame byte is the scratch, a block's, or a cursor cell, above the
   frames) *)
assert (FRK : forall cid pos' a, In (cid, pos') (frames Sc) -> in_zr a (frame_rng lyc (cid, pos')) ->
   aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a).
{ intros cid pos' a Hin Hr.
  pose proof (frames_bounds_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos' HARc Hin) as (G1 & G2 & _).
  apply (F4 cid pos' a Hin (or_introl Hr)). apply NF1.
  - intros Hs. apply (frame_not_block_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc (cid, pos') bs ms a HARc Hin Hins Hr).
    lia.
  - unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. lia. }
split; [|exact KEEPF].
(* the journal, the caller window *)
split; [exact HJ2|].
split.
{ intros a Ha Hf. rewrite (HWK a ltac:(lia) (fun H => Hf (HFP1 a H))). exact (HWIN a Ha Hf). }
(* the float state (KIT_EXB_CALL's EXB premise elaborates at fx2: its implicit fx is resolved to the nearest FPState
   binder; exv_exb_fx below moves an EXB at the cut's fx there), Hp, the blocks, the room, the ledger, the frame
   count *)
split; [exact HFR|].
split; [exact HFZ2|].
split; [rewrite HHp2; exact HHp|].
split; [rewrite HAB2; exact HAB|].
split; [exact (conj (exv_room_trans _ _ _ (proj1 HRM) HRM2) HMN2)|].
split; [exact HLED2|].
split; [rewrite Hfrs; exact HCNT|].
(* the registers *)
split; [rewrite (HR 2%bv ltac:(kp_in)); exact R2|].
split; [rewrite (HR 8%bv ltac:(kp_in)); exact R8|].
split; [rewrite (HR 9%bv ltac:(kp_in)); exact R9|].
split; [rewrite FR2, (HR 18%bv ltac:(kp_in)); exact R18|].
split; [rewrite FR2, (HR 24%bv ltac:(kp_in)); exact R24|].
split; [rewrite (HR 25%bv ltac:(kp_in)); exact R25|].
split; [rewrite FR2, (HR 26%bv ltac:(kp_in)); exact R26|].
split; [rewrite (HR 19%bv ltac:(kp_in)); exact R19|].
split; [rewrite (HR 3%bv ltac:(kp_in)); exact R3|].
split; [rewrite (HR 4%bv ltac:(kp_in)); exact R4|].
(* the saved registers, 176(s1), the flag pointer *)
split.
{ intros o r Hin. pose proof (exv_saved_rng o r Hin) as Ho.
  eapply kp_val_kept2; [|exact (HSV o r Hin)].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KEEPF. lia. }
split.
{ rewrite FR2. eapply kp_val_kept2; [|exact H176].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KEEPF. lia. }
split.
{ rewrite FR2, FL2.
  rewrite (rdword_ext (aview rsegs (w_H Wc) memc) (aview rsegs (w_H W2) mem2) (frame_addr lyc 1 pos + 120));
    [exact HFL|].
  pose proof (frames_bounds_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc 1 pos HARc Hin1) as (Fb1 & Fb2 & _).
  change (fs_frame_bytes 1) with 128 in Fb2.
  intros kk Hk. apply (FRK 1 pos _ Hin1). unfold frame_rng, in_zr. cbn [fst snd].
  change (fs_frame_bytes 1) with 128. lia. }
(* the text *)
split.
{ destruct HSRC as (Hby & H4096 & Hce & Ham & Hra & Hhull).
  assert (TXK : forall a, e_x0 E <= a < e_x0 E + exv_len E ->
     aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a).
  { intros a Ha. destruct (HTB ltac:(lia)) as (bt & mt & Hint & Ht1 & Ht2 & _).
    apply BLK; [exists bt, mt; split; [exact Hint | lia] | lia | lia]. }
  split; [|split; [exact H4096|split; [exact Hce|split; [exact Ham|split]]]].
  - eapply kp_garr8_kept2; [|exact Hby]. intros a Ha. apply TXK. lia.
  - destruct (Z_lt_le_dec 0 (exv_len E)) as [Hl|Hl].
    + destruct (exv_sh_blk B ARx SK HYP ly2 S2 Hp2 W2 mem2 md2 (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
        (e_x0 E) (exv_len E) HAR2 HLED2 (INB2 _ _ (HTB Hl)) Hl) as (RA & _).
      rewrite <- HLEN. exact RA.
    + intros z Hz. exfalso. lia.
  - intros Hl. rewrite <- HLEN in Hl |- *.
    destruct (exv_sh_blk B ARx SK HYP ly2 S2 Hp2 W2 mem2 md2 (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
      (e_x0 E) (exv_len E) HAR2 HLED2 (INB2 _ _ (HTB Hl)) Hl) as (_ & HV).
    exact HV. }
split; [intros Hl; exact (INB2 _ _ (HTB Hl))|].
(* the scratch *)
split.
{ destruct HWD as (D1 & D2 & D3 & D4 & D5 & D6).
  destruct (alx_blocks rsegs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 bs ms HAR2 ltac:(rewrite HAB2; exact Hins))
    as (_ & _ & _ & _ & Hpr & _).
  split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split.
  - intros a Ha. destruct (Hpr a ltac:(lia)) as (Hp & Hno).
    split; [exact (apresent_writable rsegs _ _ _ Hp)|]. split; [exact Hno|]. lia.
  - destruct (exv_sh_blk B ARx SK HYP ly2 S2 Hp2 W2 mem2 md2 (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
      (e_scr E) (exv_len E + 1) HAR2 HLED2 (INB2 _ _ HSB) ltac:(lia)) as (RA & HV).
    split; [exact RA | intros _; exact HV]. }
split; [exact (INB2 _ _ HSB)|].
(* the cursor's shadow *)
split; [apply (kp_stack_ra ly2 S2 Hp2 W2 mem2 md2 (e_q E) 40 HAR2); lia|].
(* the tree *)
destruct Hv0 as [Hv0 | (_ & _ & HDJ)]; [left; exact Hv0|].
destruct HTREE as [Hv | (Hnd & Hhome & Hra & Hhull)]; [left; exact Hv|]. right.
assert (Hhi : ly_stk_hi lyc <= 2 ^ 47) by lia.
pose proof (exv_foot_rng B ARx SK HYP lyc Sc Hpc Wc memc mdc (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E) regs
  (e_v E) (e_t E) (e_D E) HARc HLED Hnd Hhome Hhi) as FOOT.
assert (LAMK : forall b0 k0 x, In (b0, k0) (e_Lam E) -> b0 <= x < b0 + k0 ->
   ~ (e_scr E <= x < e_scr E + exv_len E + 1) -> ~ (e_q E <= x < e_q E + 40) ->
   aview rsegs (w_H W2) mem2 x = aview rsegs (w_H Wc) memc x /\ ~ in_img rsegs x).
{ intros b0 k0 x Hin Hx Hs Hq. pose proof HLED as (_ & _ & HBL & _). rewrite Forall_forall in HBL.
  destruct (HBL (b0, k0) Hin) as (Hk0 & Hblk & _). cbn [fst snd] in Hk0, Hblk.
  assert (Hrq : k0 + cf_head <= req_size (k0 + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
  split.
  - apply BLK; [|exact Hs|exact Hq]. exists (b0 - cf_head), (k0 + cf_head). split; [exact Hblk | lia].
  - apply (blk_img_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc (b0 - cf_head) (k0 + cf_head) x HARc Hblk). lia. }
assert (FOOTK : forall x, PRH_Reader.pj_footR (e_v E) (e_D E) x ->
   aview rsegs (w_H W2) mem2 x = aview rsegs (w_H Wc) memc x /\ ~ in_img rsegs x).
{ intros x Hx. pose proof (FOOT x Hx) as Hxb. destruct (HDJ x Hx) as (Hxs & Hxq & Hxw & _).
  destruct Hx as [Hx | (b & Hb & Hx)].
  - destruct Hhome as [(b0 & k0 & Hin & H1 & H2) | [(cid & pos' & Hin & H1 & H2) | (H1 & H2)]].
    + apply (LAMK b0 k0 x Hin); [lia | exact Hxs | exact Hxq].
    + split.
      * apply (FRK cid pos' x Hin). unfold frame_rng, in_zr. cbn [fst snd]. lia.
      * apply (frm_img_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos' x HARc Hin). lia.
    + split.
      * destruct (Z_lt_le_dec x (spZ (e_regs E) + e_d E)) as [Hlt | Hge].
        -- apply HWK; [lia | apply NF1; [exact Hxs | exact Hxq]].
        -- apply F1; lia.
      * intros Hi. pose proof (B_prog_segs_low x Hi) as Hlow. unfold kLowMemEnd in Hlow. lia.
  - pose proof (exv_node_D (e_t E) _ _ (e_v E) (e_D E) Hnd b Hb) as Hl. destruct b as [b0 k0].
    unfold prh_lin in Hl. cbn [fst snd] in Hl. unfold PRH_Reader.pj_holdsR in Hx. cbn [fst snd] in Hx.
    apply (LAMK b0 k0 x Hl); [lia | exact Hxs | exact Hxq]. }
split.
{ apply (PRH_Reader.pj_nodeR_frame rsegs (e_t E) (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2)
    (prh_lin (e_Lam E)) (e_v E) (e_D E) Hnd).
  intros x Hx. pose proof (FOOT x Hx) as Hxb. destruct (FOOTK x Hx) as (Ha & Hni). split.
  - apply (mbyte_of_aview rsegs). exact Ha.
  - intros Hw. apply (kp_wr_keep rsegs (w_H Wc) (w_H W2) memc mem2 x); [lia | exact Hni | exact Ha | exact Hw]. }
unfold prhex_home in Hhome |- *.
split.
{ destruct Hhome as [Hl | [(cid & pos' & Hin & H1 & H2) | (H1 & H2)]].
  - left. exact Hl.
  - right. left. exists cid, pos'. rewrite Hfrs.
    destruct (kp_flag_layout lyc ly2 Sc Hpc Wc memc mdc cid pos' HARc Hly1) as (Ef & _). rewrite Ef.
    split; [exact Hin | split; [exact H1 | exact H2]].
  - right. right. rewrite SP2, Ehi2. split; [exact H1 | exact H2]. }
destruct Hhome as [(b0 & k0 & Hin & H1 & H2) | [(cid & pos' & Hin & H1 & H2) | (H1 & H2)]].
- exact (exv_sh_lam B ARx SK HYP ly2 S2 Hp2 W2 mem2 md2 (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
    b0 k0 (e_v E) 56 HAR2 HLED2 Hin H1 H2 ltac:(lia)).
- destruct (kp_flag_layout lyc ly2 Sc Hpc Wc memc mdc cid pos' HARc Hly1) as (Ef & _).
  assert (Hin2 : In (cid, pos') (frames S2)) by (rewrite Hfrs; exact Hin).
  destruct (alx_frames rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos' HARc Hin) as (Fm & _).
  pose proof (frames_bounds_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos' HARc Hin) as (Fb1 & Fb2 & _).
  assert (Hbm : fs_frame_bytes cid mod 8 = 0) by (apply kp_fsb_mod; lia).
  split.
  + apply (kp_ra_kept2 rsegs (w_H Wc) (w_H W2) memc mem2 (e_v E) 56); [|exact Hra].
    intros x Hx. destruct (SHAD x ltac:(lia)) as (Hs1' & Hs2').
    apply (F4 cid pos' (shadow_of_addr SHADOW_OFF x) Hin).
    * right. unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd]. lia.
    * apply NF1; [apply SCRAPP; exact Hs1' | lia].
  + apply (eh_frame_hull B ARx SK HYP ly2 S2 Hp2 W2 mem2 md2 cid pos' (e_v E) 56 HAR2 Hin2); try rewrite Ef; lia.
- split.
  + apply (kp_stack_ra ly2 S2 Hp2 W2 mem2 md2 (e_v E) 56 HAR2); lia.
  + apply (eh_stk_hull B ARx SK HYP ly2 S2 Hp2 W2 mem2 md2 (e_v E) 56 HAR2); lia.
Qed.

(* EXB moves to a float state that keeps the callee-saved f registers and has rounding mode 0 (for a caller whose EXB
   is at the cut's fx and whose callee ends at fx2: KIT_EXB_CALL's premise is at fx2) *)
Lemma exv_exb_fx : forall (fx fx2 : YK11.FPState) E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos,
  EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> fregs_kept_x fx fx2 -> frm_zero (@YK11.fp_csr fx2) ->
  EXB (fx := fx2) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos.
Proof.
intros fx fx2 E lyc Sc Hpc Wc regs memc mdc k pos HB HK HZ.
unfold EXB in HB |- *. cbv zeta in HB |- *.
destruct HB as (H1 & H2 & H3 & H4 & REST).
split; [exact H1|]. split; [exact H2|]. split; [exact (kp_fregs_trans _ _ _ H3 HK)|]. split; [exact HZ | exact REST].
Qed.
End kp.

Print Assumptions exv_kit_call.
