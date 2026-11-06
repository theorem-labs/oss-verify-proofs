(* fuzz_preset, slice S5b, lane PI-key (the S3 walk, a Theorem Labs lane): the ONE transport of parse_items' loop positions across a
   store into the FREE SLOT n of one of the node's two array blocks (a Theorem Labs lane's ruling, 2026-10-29: the S3 walk writes it
   once; PI-key's key store, IelemD / ISlot / IelemE's grow arms cite it).
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). No callee, no walk: a memory-frame lemma over VrdIElem.v's
   boundary predicates.
   THE SLOT. blk is one of the node's array blocks, of w-byte slots: (blk, w * cap) is in
   kids_blkR kids cap ++ keys_blkR ty keys cap (vrd_inode's own split of D). The store writes [blk + w * n, + w), with
   n = ip_n P < cap = ip_cap P. Nothing here names which array: the kids store is w = 56, the key store w = 8, and
   the membership premise fixes w (vss_blk).
   WHAT IT GIVES.
   - vk_slot_rw: the slot is writable at the position's view rdW (ip_W P) (ip_mem P). Its sources: prh_lin
     (ip_Lam P) blk (w * cap) (vrd_inode's fifth conjunct), the block's allocator block (prh_hblock, from vrd_icur's
     prh_ledger by prh_ledger_hblock), its bytes present (AR_laws_x's block law at the position's ARx, which is
     vrd_ijrn's journal's first conjunct).
   - vk_slot_store_keep: a new machine state (regs, mem', md', k') whose memory agrees with P's outside the slot (at
     the w_H-restricted level), whose journal the store's run supplies, and whose sp is P's: the position
     vk_move P regs mem' md' k' (ip_p P) keeps vrd_iframe, vrd_inode .. Dx (any Dx), vrd_icur (pj_in_okR, src_rd and
     prh_ledger among its conjuncts) and vrd_ijrn. Every conclusion is at the NEW view
     rdW (ip_W P) mem' = mrestrict (w_H (ip_W P)) mem' (aview SEGS (w_H (ip_W P)) mem' for the shadow and image
     clauses).
   WHY IT HOLDS. Every byte the predicates read is apart from the slot:
   - the frame, the cursor q and the caller window are on the stack, above alloc_ceiling (vrd_ient_ok's astk_ok);
     the slot is in an allocator block, below it (the block law);
   - the node v: vrd_inode_apart (VrdIFd.v), since the slot block is in D;
   - the member / item trees: the used part [blk, blk + w * n) is below the slot; the OTHER array and every Di block
     are other allocator blocks (sep_blocks_x; D has no duplicate, from the ledger's NoDup through the position's
     rd_ledger_move, a premise);
   - the text: its home at the ENTRY (rd_pre's prhReader_home): an entry harness or allocator block, which no D
     block is (rd_blocks_move), or image bytes, which no block is (AR_laws_x's client_img law);
   - the statics (PST_IMG: image) and the harness heads (another block, or blk's own head, below blk: HW);
   - every shadow byte: the slot is in application memory (the block law's in_app), every shadow byte of an address
     below 2 ^ 47 is in [SHADOW_OFF, kHighMemBeg).
   The chain conjunct of vrd_ijrn is IelemE's vrd_chain_keep_w (VrdIElem.v Section W): every byte it may read is at or
   above sp0 - 144, above the slot.
   The slot itself stays writable at mem': the block law at the journal's ARx at mem' (vrd_inode's rd_rw clause covers
   the slot when blk is the kids block).
   TWO SECTION VARIABLES, both image / instance facts, as VrdCurStore.v takes them: PST_IMG (alloc.c's statics are
   image bytes; discharged at prh_img_A by S1ImgA.v pst_in_img_A) and HW (`8 <= cf_head`; a Theorem Labs lane's
   preset_head_wide, lib/A/CfParamsPreset.v:95).
   SET: a working branch on a working branch 7cc876957dd (record texts 265bfe65918). A-only: B sites not
   measured.
   Numerals: 144 (LENGTH, parse_items' frame, as VrdIElem.v states it), 56 / 24 / 8 (LENGTH: node, cursor, head word),
   2 ^ 44 / 2 ^ 47 / 2 ^ 64 (LENGTH: bounds). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse VrdFrame VrdIElem
VrdCurStore VrdIFd.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
(* the re-hiding move's wle' (YA0nH) and preset's zone (YGcfRehidePost.RZ_cf): vrd_ijrn's journal is at wle' *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section SS.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
#[local] Notation PAI := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PAI).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Variable HW : 8 <= cf_head.
Variable PST_IMG : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a.

(* ---- byte-level pieces ---- *)

(* a present byte is writable *)
Lemma vss_rw_present : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> writable_at SEGS (mrestrict H m) a.
Proof. intros H m a (Hh & b & Hb). unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate. Qed.

(* rd_rw across a store: kept outside the window, the window writable at the new memory *)
Lemma vss_rw_keep : forall (H : word -> bool) (m m' : word -> option byte) lo hi a n,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict H m' x = mrestrict H m x) ->
  (forall x, lo <= x < hi -> writable_at SEGS (mrestrict H m') x) ->
  (forall x, a <= x < a + n -> 0 <= x < 2 ^ 64) ->
  rd_rw SEGS (mrestrict H m) a n -> rd_rw SEGS (mrestrict H m') a n.
Proof.
  intros H m m' lo hi a n HK HWw Hr HR x Hx.
  destruct (Z_lt_le_dec x lo) as [Hl | Hl]; [|destruct (Z_lt_le_dec x hi) as [Hh | Hh]].
  - pose proof (Hr x Hx). pose proof (HR x Hx) as Hw. unfold writable_at, wview in *.
    rewrite (HK (Z_to_bv 64 x)) by (rewrite unsigned_lit_small by lia; lia). exact Hw.
  - exact (HWw x (conj Hl Hh)).
  - pose proof (Hr x Hx). pose proof (HR x Hx) as Hw. unfold writable_at, wview in *.
    rewrite (HK (Z_to_bv 64 x)) by (rewrite unsigned_lit_small by lia; lia). exact Hw.
Qed.

(* the shadow bytes of an address below 2 ^ 47 are in [SHADOW_OFF, kHighMemBeg): apart from application memory *)
Lemma vss_keep_ra : forall (H : word -> bool) (m m' : word -> option byte) lo hi a n,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict H m' x = mrestrict H m x) ->
  (hi <= kLowShadowBeg \/ kHighMemBeg <= lo) -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable (aview SEGS H m) SHADOW_OFF a n -> range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof.
  intros H m m' lo hi a n HK Hz Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok).
  exists s. split; [|exact Hok]. unfold shadow_of_addr in *.
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (vk_keep_av H m m' lo hi _ HK) by (unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia). exact Hs.
Qed.

Lemma vss_keep_hull : forall (H : word -> bool) (m m' : word -> option byte) lo hi a n,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict H m' x = mrestrict H m x) ->
  (hi <= kLowShadowBeg \/ kHighMemBeg <= lo) -> 0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis (aview SEGS H m) a n -> shadow_hull_vis (aview SEGS H m') a n.
Proof.
  intros H m m' lo hi a n HK Hz Ha Han Hn HV s Hs. unfold shadow_addr in Hs.
  assert (0 <= a / 8) by (apply Z.div_pos; lia).
  assert ((a + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as M2.
  rewrite (vk_keep_av H m m' lo hi s HK) by (unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia).
  apply HV. unfold shadow_addr. exact Hs.
Qed.

Lemma vss_nodup_app : forall (A : Type) (l1 l2 : list A) x y,
  List.NoDup (l1 ++ l2) -> In x l1 -> In y l2 -> x <> y.
Proof.
  intros A l1 l2 x y H Hx Hy Heq. subst y. induction l1 as [|a l1 IH]; [destruct Hx|].
  cbn [app] in H. inversion H as [|a' l' Hn Hd]; subst.
  destruct Hx as [-> | Hx].
  - apply Hn. apply in_or_app. right. exact Hy.
  - exact (IH Hd Hx).
Qed.

(* ---- the slot block ---- *)
Lemma vss_blk : forall E P Dx blk w,
  vrd_inode E P Dx -> ip_n P < ip_cap P ->
  In (blk, w * ip_cap P)
    (kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)) ->
  ((blk = ip_kids P /\ w = 56) \/ (ie_o E = true /\ blk = ip_keys P /\ w = 8)) /\
  prh_lin (ip_Lam P) blk (w * ip_cap P) /\ In (blk, w * ip_cap P) (ip_D P).
Proof.
  intros E P Dx blk w HND Hn Hin.
  pose proof HND as (_ & Hnc & _ & _ & Hlin & _ & (Di & HPerm & _) & _).
  assert (HD : In (blk, w * ip_cap P) (ip_D P)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right.
    rewrite app_assoc. apply in_or_app. left. exact Hin. }
  apply in_app_or in Hin as [Hk | Hy].
  - unfold kids_blkR in Hk. destruct (Z.eqb_spec (ip_cap P) 0) as [Hc | Hc]; [lia|].
    destruct Hk as [Heq | []]. injection Heq as Eb Ew.
    assert (w = 56) by (apply (Z.mul_cancel_r w 56 (ip_cap P)); [lia | nia]).
    subst w. split; [left; split; [lia | reflexivity]|]. split; [|exact HD].
    rewrite <- Eb. exact (proj1 (Hlin ltac:(lia))).
  - unfold keys_blkR in Hy. destruct (ie_o E) eqn:Ho; destruct (Z.eqb_spec (ip_cap P) 0) as [Hc | Hc]; cbn in Hy;
      try lia; try contradiction.
    destruct Hy as [Heq | []]. injection Heq as Eb Ew.
    assert (w = 8) by (apply (Z.mul_cancel_r w 8 (ip_cap P)); [lia | nia]).
    subst w. split; [right; split; [reflexivity | split; [lia | reflexivity]]|]. split; [|exact HD].
    rewrite <- Eb. exact (proj2 (Hlin ltac:(lia)) eq_refl).
Qed.

(* ==== the slot is writable at the position's view ==== *)
Lemma vk_slot_rw_core : forall E P Dx blk w,
  vrd_inode E P Dx ->
  prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P)
    (ie_most E) (ie_own E) ->
  vrd_ijrn B ARx SK E P ->
  In (blk, w * ip_cap P)
    (kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)) ->
  ip_n P < ip_cap P ->
  rd_rw SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (blk + w * ip_n P) w.
Proof.
  intros E P Dx blk w HND Hled HJN Hin Hn.
  destruct (vss_blk E P Dx blk w HND Hn Hin) as (Hwk & Hlin & _).
  pose proof HJN as ((HAR & _) & _).
  pose proof HND as (_ & Hnc & _).
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ blk (w * ip_cap P) _ _ Hled Hlin) as (Hk & Hab & _).
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & _ & _ & _ & Hpres & _).
  pose proof (@cf_head_nonneg cp) as Hch.
  destruct (req_size_pos (w * ip_cap P + cf_head)) as [_ Hrq]; [lia|].
  assert (Hw0 : 0 < w) by (destruct Hwk as [(_ & ->) | (_ & _ & ->)]; lia).
  assert (Hwn : w * ip_n P + w <= w * ip_cap P) by nia.
  intros x Hx. apply vss_rw_present. exact (proj1 (Hpres x ltac:(lia))).
Qed.

Lemma vk_slot_rw : forall E P Dx blk w,
  vrd_inode E P Dx -> vrd_icur B E P -> vrd_ijrn B ARx SK E P ->
  In (blk, w * ip_cap P)
    (kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)) ->
  ip_n P < ip_cap P ->
  rd_rw SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (blk + w * ip_n P) w.
Proof.
  intros E P Dx blk w HND HCU HJN Hin Hn. pose proof HCU as (_ & _ & _ & _ & Hled & _).
  exact (vk_slot_rw_core E P Dx blk w HND Hled HJN Hin Hn).
Qed.

Ltac vk_proj := unfold vk_move; cbn [ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids ip_keys
  ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].

(* ==== THE TRANSPORT, core form: the memory facts of vrd_icur as separate premises (so a position whose model has
   refused, without vrd_icur's count bound, can use it), and two keeps the stretch after the store needs: the text
   (src_rd) and every OTHER D block's bytes ==== *)
Lemma vk_slot_store_keep_core : forall CTX CTX0 CW E P Dx regs mem' md' k' blk w,
  pi_frame F_parse_items = 144 -> pi_s0cur F_parse_items = Some 0 ->
  vrd_ient_ok B ARx CTX CTX0 CW E ->
  vrd_iframe E P -> vrd_inode E P Dx -> vrd_ijrn B ARx SK E P ->
  pj_in_okR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (ie_q E) (ie_text E) (ie_len E) (ip_p P)
    (Z.of_nat (ie_d E) + 1) (ie_tb E) ->
  range_addressable (aview SEGS (w_H (ip_W P)) (ip_mem P)) SHADOW_OFF (ie_q E) 24 ->
  prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P)
    (ie_most E) (ie_own E) ->
  (* the position's ledger move (vrd_imodel's third conjunct): D has no duplicate *)
  rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ip_ok P)
    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P)
    (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) ->
  (* the slot block and the slot *)
  In (blk, w * ip_cap P)
    (kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)) ->
  ip_n P < ip_cap P ->
  (* the store: memory changes only in the slot *)
  (forall x : word, ~ (blk + w * ip_n P <= bv_unsigned x < blk + w * ip_n P + w) ->
     mrestrict (w_H (ip_W P)) mem' x = mrestrict (w_H (ip_W P)) (ip_mem P) x) ->
  spZ regs = spZ (ip_regs P) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  vrd_iframe E (vk_move P regs mem' md' k' (ip_p P)) /\ vrd_inode E (vk_move P regs mem' md' k' (ip_p P)) Dx /\
  vrd_ijrn B ARx SK E (vk_move P regs mem' md' k' (ip_p P)) /\
  pj_in_okR SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) (ie_text E) (ie_len E) (ip_p P)
    (Z.of_nat (ie_d E) + 1) (ie_tb E) /\
  range_addressable (aview SEGS (w_H (ip_W P)) mem') SHADOW_OFF (ie_q E) 24 /\
  prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P)
    (ie_most E) (ie_own E) /\
  (src_rd (ip_W P) (ip_mem P) (ie_text E) (ie_tb E) -> src_rd (ip_W P) mem' (ie_text E) (ie_tb E)) /\
  rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
    (fun z => exists b, In b (ip_D P) /\ b <> (blk, w * ip_cap P) /\ pj_holdsR b z).
Proof.
  intros CTX CTX0 CW E P Dx regs mem' md' k' blk w Himg Hs0c HEN HFR HND HJN Hpin Hraq Hled HLM Hin Hn HK Hsp HJ'.
  pose proof asan_consts as (C1 & _).
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  assert (Bv56 : ie_v E + 56 <= alloc_ceiling) by (eapply vrd_node_low; eassumption).
  (* the frame is above alloc_ceiling *)
  assert (Bfr : alloc_ceiling <= spZ (ie_regs E) - 144).
  { pose proof HEN as ((HAFN & _) & _).
    pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
    pose proof Hstk as (_ & _ & Hceil & Hslo & _).
    assert (HSTK : 144 <= STK_parse_items (ie_d E)).
    { unfold STK_parse_items. rewrite Himg. pose proof (pi_frame_nonneg F_parse_value).
      assert (0 <= LEAF_pv_pi) by (unfold LEAF_pv_pi, zmaxl; cbn [fold_right]; lia).
      assert (0 <= Z.of_nat (PjGrammar.MAXD - ie_d E) * (pi_frame F_parse_value + 144))
        by (apply Z.mul_nonneg_nonneg; lia).
      lia. }
    lia. }
  pose proof HJN as ((HAR & _) & _).
  pose proof HJN as (_ & _ & _ & _ & _ & HBM & _).
  pose proof HBM as (HnotE & HPab & _).
  pose proof HJ' as (HAR' & _).
  pose proof HEN as (_ & _ & _ & _ & HRD & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HhomeE & _ & _ & _ & _ & _ & HLE & _).
  pose proof (@cf_head_nonneg cp) as Hch.
  destruct (vss_blk E P Dx blk w HND Hn Hin) as (Hwk & Hlin & HbD).
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ blk (w * ip_cap P) _ _ Hled Hlin) as (Hk & Hab & _).
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & Hb4 & Hbc & Happ & _ & _).
  destruct (req_size_pos (w * ip_cap P + cf_head)) as [_ Hrq]; [lia|].
  pose proof HND as (Hhdr & Hnc & Hcap & Hc0 & Hlin0 & Hlen & (Di & HPerm & HTree) & Hrw & Hrav & Hrak & Hrakeys & Hkz).
  assert (Hw0 : 0 < w) by (destruct Hwk as [(_ & ->) | (_ & _ & ->)]; lia).
  assert (Hwn : w * ip_n P + w <= w * ip_cap P) by nia.
  assert (Hwn0 : 0 <= w * ip_n P) by nia.
  (* THE WINDOW: in blk's allocator block, below alloc_ceiling, in application memory, not image *)
  assert (HWb : forall x, blk + w * ip_n P <= x < blk + w * ip_n P + w ->
             blk - cf_head <= x < blk - cf_head + req_size (w * ip_cap P + cf_head) /\ blk <= x < blk + w * ip_cap P)
    by (intros x Hx; lia).
  assert (HWhi : blk + w * ip_n P + w <= alloc_ceiling) by lia.
  assert (HWzone : blk + w * ip_n P + w <= kLowShadowBeg \/ kHighMemBeg <= blk + w * ip_n P).
  { unfold in_app in Happ. lia. }
  assert (HWimg : forall x, blk + w * ip_n P <= x < blk + w * ip_n P + w -> ~ in_img SEGS x).
  { intros x Hx. refine (proj2 (alx_client_img SEGS B ARx LAWS _ _ _ _ _ _ x HAR _)).
    left. exists (blk - cf_head), (w * ip_cap P + cf_head). split; [exact Hab | lia]. }
  (* apart from every other allocator block *)
  assert (HWsep : forall p m0, In (p, m0) (ablocks B (ip_ly P) (ip_S P)) ->
             (blk - cf_head, w * ip_cap P + cf_head) <> (p, m0) ->
             forall x, blk + w * ip_n P <= x < blk + w * ip_n P + w -> ~ (p <= x < p + req_size m0)).
  { intros p m0 HpP Hne x Hx Hpx.
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab HpP Hne) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia. }
  (* apart from every entry block: no D block is one *)
  assert (HWentry : forall p m0, In (p, m0) (ablocks B (ie_ly E) (ie_S E)) ->
             forall x, blk + w * ip_n P <= x < blk + w * ip_n P + w -> ~ (p <= x < p + req_size m0)).
  { intros p m0 HpE x Hx.
    assert (HpP : In (p, m0) (ablocks B (ip_ly P) (ip_S P)))
      by (apply (Permutation_in _ (Permutation_sym HPab)); apply in_or_app; right; exact HpE).
    assert (Hne : (blk - cf_head, w * ip_cap P + cf_head) <> (p, m0))
      by (intros Heq; apply (HnotE blk (w * ip_cap P) HbD); rewrite Heq; exact HpE).
    exact (HWsep p m0 HpP Hne x Hx). }
  (* apart from every other D block *)
  assert (HWD : forall b, In b (ip_D P) -> b <> (blk, w * ip_cap P) ->
             forall x, blk + w * ip_n P <= x < blk + w * ip_n P + w -> ~ pj_holdsR b x).
  { intros [a k] HbIn Hne x Hx Hhx. unfold pj_holdsR in Hhx. cbn [fst snd] in Hhx.
    assert (HabP : In (a - cf_head, k + cf_head) (ablocks B (ip_ly P) (ip_S P))).
    { apply (Permutation_in _ (Permutation_sym HPab)). apply in_or_app. left. unfold prhReader_ab.
      exact (in_map (fun ak => (fst ak - cf_head, snd ak + cf_head)) _ (a, k) HbIn). }
    assert (Hne' : (blk - cf_head, w * ip_cap P + cf_head) <> (a - cf_head, k + cf_head)).
    { intros Heq. injection Heq as E1 E2. apply Hne. f_equal; lia. }
    destruct (req_size_pos (k + cf_head)) as [_ Hr]; [lia|].
    exact (HWsep _ _ HabP Hne' x Hx ltac:(lia)). }
  (* the harness heads *)
  assert (HWlam : forall a k i, In (a, k) (ip_Lam P) -> 0 <= i < 8 ->
             forall x, blk + w * ip_n P <= x < blk + w * ip_n P + w -> x <> a - cf_head + i).
  { intros a k i HaL Hi x Hx Hxe.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ Hled HaL) as (Hk0 & HabL & _).
    destruct (Z.eq_dec a blk) as [-> | Hneq]; [lia|].
    assert (Hne : (blk - cf_head, w * ip_cap P + cf_head) <> (a - cf_head, k + cf_head))
      by (intros Heq; injection Heq as E1 E2; lia).
    destruct (req_size_pos (k + cf_head)) as [_ Hr]; [lia|].
    exact (HWsep _ _ HabL Hne x Hx ltac:(lia)). }
  (* the node *)
  assert (Hap : pj_apartR (ip_D P) (ie_v E)) by (eapply vrd_inode_apart; eassumption).
  assert (HWnode : forall x, blk + w * ip_n P <= x < blk + w * ip_n P + w -> ~ (ie_v E <= x < ie_v E + 56)).
  { intros x Hx Hv. exact (Hap (blk, w * ip_cap P) x HbD ltac:(unfold pj_holdsR; cbn [fst snd]; lia) Hv). }
  (* the text: its home at the entry *)
  pose proof Hpin as (_ & _ & _ & _ & _ & Ht0 & Htl & Htp & Htlen & _).
  assert (HWtext : forall x, blk + w * ip_n P <= x < blk + w * ip_n P + w ->
             ~ (ie_text E <= x < ie_text E + ie_len E)).
  { intros x Hx Ht.
    destruct HhomeE as [[(b & m0 & HbL & Hb1 & Hb2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] |
                        (b & m0 & HbA & _ & Hb1 & Hb2)].
    - pose proof HLE as (_ & _ & HHB & _). rewrite Forall_forall in HHB.
      destruct (HHB _ HbL) as (Hk0 & HabE & _). cbn [fst snd] in Hk0, HabE.
      destruct (req_size_pos (m0 + cf_head)) as [_ Hr]; [lia|].
      exact (HWentry _ _ HabE x Hx ltac:(lia)).
    - destruct (Hro x ltac:(lia)) as (Hr & _). apply (HWimg x Hx).
      destruct Hr as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (@pa_relro_img _ _ PAI x Hr)].
    - destruct (Hro x ltac:(lia)) as (Hr & _). apply (HWimg x Hx).
      destruct Hr as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (@pa_relro_img _ _ PAI x Hr)].
    - destruct (req_size_pos m0) as [_ Hr]; [lia|].
      exact (HWentry _ _ HbA x Hx ltac:(lia)). }
  (* D has no duplicate; the Di blocks are not the slot block *)
  assert (HNd : List.NoDup (ip_D P)).
  { pose proof HLM as (_ & _ & _ & HPL & _). pose proof Hled as (_ & HNL & _).
    assert (HNL' : List.NoDup (map fst (ip_Lam P))) by (first [exact HNL | apply NoDup_ListNoDup; exact HNL]).
    apply (Permutation_map fst) in HPL. pose proof (Permutation_NoDup HPL HNL') as H. rewrite map_app in H.
    apply NoDup_app_remove_r in H. exact (NoDup_map_inv _ _ H). }
  assert (HDi : forall b, In b Di -> b <> (blk, w * ip_cap P)).
  { intros b Hb Heq. subst b.
    pose proof (Permutation_NoDup HPerm HNd) as HN2. apply NoDup_app_remove_l in HN2.
    rewrite app_assoc in HN2. exact (vss_nodup_app _ _ _ _ _ HN2 Hin Hb eq_refl). }
  assert (HDlow : forall b x, In b (ip_D P) -> pj_holdsR b x -> 4096 <= x < alloc_ceiling)
    by (intros b x Hb Hx; eapply vk_D_low; eassumption).
  assert (HDsub : forall b, In b (Dx ++ kids_blkR (ip_kids P) (ip_cap P) ++
                    keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Di) -> In b (ip_D P))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPerm) Hb)).
  assert (Hkids : 0 < ip_cap P -> In (ip_kids P, 56 * ip_cap P) (ip_D P)).
  { intros Hc. apply HDsub. apply in_or_app. right. apply in_or_app. left. unfold kids_blkR.
    destruct (Z.eqb_spec (ip_cap P) 0); [lia | left; reflexivity]. }
  assert (Hkeys : ie_o E = true -> 0 < ip_cap P -> In (ip_keys P, 8 * ip_cap P) (ip_D P)).
  { intros Ho Hc. apply HDsub. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    unfold keys_blkR. rewrite Ho. destruct (Z.eqb_spec (ip_cap P) 0); [lia | left; reflexivity]. }
  assert (Hkr : forall z, ip_kids P <= z < ip_kids P + 56 * ip_cap P -> 4096 <= z < alloc_ceiling)
    by (intros z Hz; exact (HDlow _ z (Hkids ltac:(lia)) Hz)).
  assert (Hyr : forall z, ie_o E = true -> ip_keys P <= z < ip_keys P + 8 * ip_cap P -> 4096 <= z < alloc_ceiling)
    by (intros z Ho Hz; exact (HDlow _ z (Hkeys Ho ltac:(lia)) Hz)).
  (* a byte of the kids / keys used part, or of a Di block, is not in the slot *)
  assert (HKidsU : forall z, ip_kids P <= z < ip_kids P + 56 * ip_n P ->
             0 <= z < 2 ^ 64 /\ ~ (blk + w * ip_n P <= z < blk + w * ip_n P + w)).
  { intros z Hz. pose proof (Hkr z ltac:(lia)). split; [lia|]. intros Hw.
    destruct Hwk as [(-> & ->) | (Ho & -> & ->)]; [lia|].
    refine (HWD _ (Hkids ltac:(lia)) _ z Hw ltac:(unfold pj_holdsR; cbn [fst snd]; lia)).
    intros Heq. injection Heq as E1 E2. lia. }
  assert (HKeysU : forall z, ie_o E = true -> ip_keys P <= z < ip_keys P + 8 * ip_n P ->
             0 <= z < 2 ^ 64 /\ ~ (blk + w * ip_n P <= z < blk + w * ip_n P + w)).
  { intros z Ho Hz. pose proof (Hyr z Ho ltac:(lia)). split; [lia|]. intros Hw.
    destruct Hwk as [(-> & ->) | (_ & -> & ->)]; [|lia].
    refine (HWD _ (Hkeys Ho ltac:(lia)) _ z Hw ltac:(unfold pj_holdsR; cbn [fst snd]; lia)).
    intros Heq. injection Heq as E1 E2. lia. }
  assert (HDiU : forall z, rd_blk Di z -> 0 <= z < 2 ^ 64 /\ ~ (blk + w * ip_n P <= z < blk + w * ip_n P + w)).
  { intros z Hz. unfold rd_blk in Hz. apply Exists_exists in Hz as (b & Hb & Hzb).
    assert (HbD' : In b (ip_D P)).
    { apply HDsub. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
    pose proof (HDlow b z HbD' Hzb). split; [lia|]. intros Hw. exact (HWD b HbD' (HDi b Hb) z Hw Hzb). }
  (* the keeps *)
  assert (HKav : forall Pz, (forall z, Pz z -> 0 <= z < 2 ^ 64 /\ ~ (blk + w * ip_n P <= z < blk + w * ip_n P + w)) ->
     rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem') Pz)
    by (intros Pz HP; exact (vk_keep_rd _ (ip_mem P) mem' _ _ Pz HK HP)).
  assert (HWw' : forall x, blk + w * ip_n P <= x < blk + w * ip_n P + w ->
             writable_at SEGS (mrestrict (w_H (ip_W P)) mem') x).
  { intros x Hx. destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR' Hab) as (_ & _ & _ & _ & Hpres' & _).
    apply vss_rw_present. exact (proj1 (Hpres' x ltac:(lia))). }
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - (* the frame: above alloc_ceiling *)
    pose proof HFR as (Hf0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 &
      F17 & Fpres).
    assert (HKfr : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
                     (fun x => spZ (ie_regs E) - 144 <= x < spZ (ie_regs E)))
      by (apply HKav; intros z Hz; split; lia).
    unfold vrd_iframe. cbv zeta. vk_proj.
    split; [rewrite Hsp; exact Hf0|].
    repeat match goal with
    | |- val_mem _ _ _ _ _ /\ _ => split; [eapply VrdFrame.val_mem_keep; [eassumption|];
                                     eapply VrdFrame.rd_keep_mono; [exact HKfr | cbn; intros; lia]|]
    end.
    intros a Ha.
    apply (vk_apresent_keep _ (ip_mem P) mem' (blk + w * ip_n P) w a HK); [lia | lia | exact (Fpres a Ha)].
  - (* the node and the trees *)
    unfold vrd_inode. cbv zeta. vk_proj.
    split; [eapply pj_hdrR_keep; [exact Hhdr | apply HKav; intros z Hz; split; [lia | intros Hw; exact (HWnode z Hw Hz)]]|].
    split; [exact Hnc|]. split; [exact Hcap|]. split; [exact Hc0|]. split; [exact Hlin0|]. split; [exact Hlen|].
    split.
    { exists Di. split; [exact HPerm|].
      destruct (ie_o E) eqn:Ho; rewrite ?Ho in HTree.
      - eapply pj_memsR_keep; [exact HTree | intros; assumption | apply HKav].
        rewrite length_rev, Hlen. intros z [Hz | [Hz | Hz]].
        + exact (HKidsU z Hz).
        + exact (HKeysU z eq_refl Hz).
        + exact (HDiU z Hz).
      - eapply pj_itemsR_keep; [exact HTree | intros; assumption | apply HKav].
        rewrite length_map, length_rev, Hlen. intros z [Hz | Hz].
        + exact (HKidsU z Hz).
        + exact (HDiU z Hz). }
    split.
    { apply (vss_rw_keep _ (ip_mem P) mem' _ _ _ _ HK HWw'); [|exact Hrw].
      intros z Hz. pose proof (Hkr z ltac:(lia)). lia. }
    split; [apply (vss_keep_ra _ (ip_mem P) mem' _ _ (ie_v E) 56 HK HWzone); [lia | lia | exact Hrav]|].
    split.
    { intros Hc. pose proof (Hkr (ip_kids P) ltac:(lia)). pose proof (Hkr (ip_kids P + 56 * ip_cap P - 1) ltac:(lia)).
      apply (vss_keep_ra _ (ip_mem P) mem' _ _ _ _ HK HWzone); [lia | lia | exact (Hrak Hc)]. }
    split; [|exact Hkz].
    intros Ho Hc. pose proof (Hyr (ip_keys P) Ho ltac:(lia)).
    pose proof (Hyr (ip_keys P + 8 * ip_cap P - 1) Ho ltac:(lia)).
    apply (vss_keep_ra _ (ip_mem P) mem' _ _ _ _ HK HWzone); [lia | lia | exact (Hrakeys Ho Hc)].
  - (* the journal, the caller window, the read-only view and the chain: all above the slot, or image *)
    pose proof HJN as (HJ & Hwin & Hfz & Hfk & Haro & Hbm & Hch2).
    unfold vrd_ijrn. vk_proj.
    split; [exact HJ'|].
    split.
    { intros a Ha Hnf. rewrite <- (Hwin a Ha Hnf). apply (vk_keep_av _ (ip_mem P) mem' _ _ a HK); lia. }
    split; [exact Hfz|]. split; [exact Hfk|].
    split.
    { intros a Hro Hno Herr.
      assert (Hi : in_img SEGS a).
      { destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (@pa_relro_img _ _ PAI a Hr)]. }
      pose proof (@pa_segs_low _ _ PAI a Hi) as Hl. unfold kLowMemEnd in Hl.
      rewrite (vk_keep_av _ (ip_mem P) mem' _ _ a HK); [exact (Haro a Hro Hno Herr) | lia | intros Hw; exact (HWimg a Hw Hi)]. }
    split; [exact Hbm|].
    eapply vrd_chain_keep_w; try eassumption; try reflexivity.
    intros a Ha Hnf. apply (vk_keep_av _ (ip_mem P) mem' _ _ a HK); lia.
  - (* the cursor *)
    eapply pj_in_okR_keep; [exact Hpin|]. apply HKav. intros z [Hz | Hz]; split; try lia.
      all: intros Hw; first [lia | exact (HWtext z Hw Hz)].
  - (* the cursor's shadow *)
    apply (vss_keep_ra _ (ip_mem P) mem' _ _ (ie_q E) 24 HK HWzone); [lia | lia | exact Hraq].
  - (* the ledger *)
    eapply prh_ledger_kept_aview; [exact Hled | | | |].
      + intros a Ha. pose proof (PST_IMG a Ha) as HI. pose proof (@pa_segs_low _ _ PAI a HI) as Hl.
        unfold kLowMemEnd in Hl.
        apply (vk_keep_av _ (ip_mem P) mem' _ _ a HK); [lia | intros Hw; exact (HWimg a Hw HI)].
      + intros a k i HaL Hi.
        destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ Hled HaL) as (Hk0 & HabL & _).
        destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR HabL) as (_ & H4 & Hc & _).
        destruct (req_size_pos (k + cf_head)) as [_ Hrq']; [lia|].
        apply (vk_keep_av _ (ip_mem P) mem' _ _ _ HK); [lia | intros Hw; exact (HWlam a k i HaL Hi _ Hw eq_refl)].
      + intros a k _ Hab0. exact Hab0.
      + apply Permutation_refl.
  - (* the text *)
    intros Hsrc.
    destruct Hsrc as (Hby & Ht4 & Htl' & Ham & Hra & Hhull).
      split; [|split; [exact Ht4 | split; [exact Htl' | split; [exact Ham | split]]]].
      + unfold PRH_Base.bytes_at in *. eapply garr8_keep; [exact Hby | apply HKav].
        intros z Hz. split; [lia|]. intros Hw. apply (HWtext z Hw). lia.
      + apply (vss_keep_ra _ (ip_mem P) mem' _ _ _ _ HK HWzone); [lia | lia | exact Hra].
      + intros Hl. apply (vss_keep_hull _ (ip_mem P) mem' _ _ _ _ HK HWzone); [lia | lia | lia | exact (Hhull Hl)].
  - (* every other D block *)
    apply HKav. intros z (b & Hb & Hne & Hz). pose proof (HDlow b z Hb Hz). split; [lia|].
    intros Hw. exact (HWD b Hb Hne z Hw Hz).
Qed.

(* ==== THE TRANSPORT ==== *)
Lemma vk_slot_store_keep : forall CTX CTX0 CW E P Dx regs mem' md' k' blk w,
  pi_frame F_parse_items = 144 -> pi_s0cur F_parse_items = Some 0 ->
  vrd_ient_ok B ARx CTX CTX0 CW E ->
  vrd_iframe E P -> vrd_inode E P Dx -> vrd_icur B E P -> vrd_ijrn B ARx SK E P ->
  (* the position's ledger move (vrd_imodel's third conjunct): D has no duplicate *)
  rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ip_ok P)
    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P)
    (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) ->
  (* the slot block and the slot *)
  In (blk, w * ip_cap P)
    (kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)) ->
  ip_n P < ip_cap P ->
  (* the store: memory changes only in the slot *)
  (forall x : word, ~ (blk + w * ip_n P <= bv_unsigned x < blk + w * ip_n P + w) ->
     mrestrict (w_H (ip_W P)) mem' x = mrestrict (w_H (ip_W P)) (ip_mem P) x) ->
  spZ regs = spZ (ip_regs P) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  vrd_iframe E (vk_move P regs mem' md' k' (ip_p P)) /\ vrd_inode E (vk_move P regs mem' md' k' (ip_p P)) Dx /\
  vrd_icur B E (vk_move P regs mem' md' k' (ip_p P)) /\ vrd_ijrn B ARx SK E (vk_move P regs mem' md' k' (ip_p P)).
Proof.
  intros CTX CTX0 CW E P Dx regs mem' md' k' blk w Himg Hs0c HEN HFR HND HCU HJN HLM Hin Hn HK Hsp HJ'.
  pose proof HCU as (Hpin & Hraq & Hsrc & Hhome & Hled & Hfrm & Hcnt).
  destruct (vk_slot_store_keep_core CTX CTX0 CW E P Dx regs mem' md' k' blk w Himg Hs0c HEN HFR HND HJN Hpin Hraq Hled
              HLM Hin Hn HK Hsp HJ') as (F' & N' & J' & Pin' & Raq' & Led' & Src' & _).
  split; [exact F'|]. split; [exact N'|]. split; [|exact J'].
  unfold vrd_icur. cbv zeta. vk_proj.
  split; [exact Pin'|]. split; [exact Raq'|]. split; [exact (Src' Hsrc)|]. split; [exact Hhome|].
  split; [exact Led'|]. split; [exact Hfrm|]. exact Hcnt.
Qed.


(* ==== where the slot is, for the run that stores it: in application memory (no shadow byte), apart from the node,
   below parse_items' frame, and addressable (vrd_inode's own range_addressable of the array) ==== *)
Lemma vk_slot_place : forall CTX CTX0 CW E P Dx blk w,
  pi_frame F_parse_items = 144 ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_inode E P Dx ->
  prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P)
    (ie_most E) (ie_own E) -> vrd_ijrn B ARx SK E P ->
  In (blk, w * ip_cap P)
    (kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)) ->
  ip_n P < ip_cap P ->
  4096 <= blk + w * ip_n P /\ blk + w * ip_n P + w <= spZ (ie_regs E) - 144 /\
  (blk + w * ip_n P + w <= kLowShadowBeg \/ kHighMemBeg <= blk + w * ip_n P) /\
  (forall x, blk + w * ip_n P <= x < blk + w * ip_n P + w -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44)) /\
  (forall x, blk + w * ip_n P <= x < blk + w * ip_n P + w -> ~ (ie_v E <= x < ie_v E + 56)) /\
  range_addressable (aview SEGS (w_H (ip_W P)) (ip_mem P)) SHADOW_OFF (blk + w * ip_n P) w.
Proof.
  intros CTX CTX0 CW E P Dx blk w Himg HEN HND Hled HJN Hin Hn.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Bfr : alloc_ceiling <= spZ (ie_regs E) - 144).
  { pose proof HEN as ((HAFN & _) & _).
    pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
    pose proof Hstk as (_ & _ & Hceil & Hslo & _).
    assert (HSTK : 144 <= STK_parse_items (ie_d E)).
    { unfold STK_parse_items. rewrite Himg. pose proof (pi_frame_nonneg F_parse_value).
      assert (0 <= LEAF_pv_pi) by (unfold LEAF_pv_pi, zmaxl; cbn [fold_right]; lia).
      assert (0 <= Z.of_nat (PjGrammar.MAXD - ie_d E) * (pi_frame F_parse_value + 144))
        by (apply Z.mul_nonneg_nonneg; lia).
      lia. }
    lia. }
  pose proof HJN as ((HAR & _) & _).
  pose proof (@cf_head_nonneg cp) as Hch.
  destruct (vss_blk E P Dx blk w HND Hn Hin) as (Hwk & Hlin & HbD).
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ blk (w * ip_cap P) _ _ Hled Hlin) as (Hk & Hab & _).
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & Hb4 & Hbc & Happ & _ & _).
  destruct (req_size_pos (w * ip_cap P + cf_head)) as [_ Hrq]; [lia|].
  pose proof HND as (_ & Hnc & _ & _ & _ & _ & _ & _ & _ & Hrak & Hrakeys & _).
  assert (Hw0 : 0 < w) by (destruct Hwk as [(_ & ->) | (_ & _ & ->)]; lia).
  assert (Hwn : w * ip_n P + w <= w * ip_cap P) by nia.
  assert (Hwn0 : 0 <= w * ip_n P) by nia.
  assert (Hap : pj_apartR (ip_D P) (ie_v E)) by (eapply vrd_inode_apart; eassumption).
  split; [lia|]. split; [lia|]. split; [unfold in_app in Happ; lia|]. split.
  { intros x Hx. unfold in_app in Happ. unfold SHADOW_OFF, kLowShadowBeg in *. lia. }
  split.
  { intros x Hx Hv. exact (Hap (blk, w * ip_cap P) x HbD ltac:(unfold pj_holdsR; cbn [fst snd]; lia) Hv). }
  intros x Hx.
  destruct Hwk as [(-> & ->) | (Ho & -> & ->)].
  - apply (Hrak ltac:(lia)). lia.
  - apply (Hrakeys Ho ltac:(lia)). lia.
Qed.

End SS.

Print Assumptions vk_slot_store_keep.
