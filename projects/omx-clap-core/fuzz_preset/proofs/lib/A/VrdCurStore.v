(* fuzz_preset, slice S5b, lane PI-key (the S3 walk, a Theorem Labs lane): the ONE transport of parse_items' loop positions across a
   store confined to a window [a0, a0 + n) at or above alloc_ceiling (a Theorem Labs lane's ruling, 2026-10-29: the S3 walk writes it
   once; PI-key's white-space loops store q->p, the Ival walk's post-value loop does too; IelemE / the Ival walk / IproD import).
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). No callee, no walk: a memory-frame lemma over VrdIElem.v's
   boundary predicates.
   WHAT IT GIVES (vk_cur_store_keep). A position P and a new machine state (regs, mem', md', k') and cursor p' whose
   memory agrees with P's outside the window (at the w_H-restricted level), whose journal the store's run supplies,
   and whose sp is P's: vk_move P regs mem' md' k' p' keeps vrd_iframe, vrd_inode .. Dx (any Dx), vrd_icur and
   vrd_ijrn. The p-dependent clauses stay with the caller, as premises: pj_in_okR at the new memory and p', and
   `length (rest p') <= length (rest p)` (for the cnt bound).
   WHY IT HOLDS. Every byte those predicates read is below alloc_ceiling (the node, by rd_pre's prhPv_node and
   vrd_node_low; the array and member blocks, by rd_blocks_move and AR_laws_x's block law; the harness heads, by the
   ledger's harness blocks and the head width HW; the text, by src_rd; the statics, by the image fact PST_IMG; every
   shadow byte, being below 2 ^ 46) or in parse_items' own frame [sp0 - 144, sp0) (premise: the window avoids it).
   The chain conjunct of vrd_ijrn is IelemE's vrd_chain_keep_w (VrdIElem.v Section W, a working branch
   2e1d73b494d): the window lies in rd_fp q v.
   TWO SECTION HYPOTHESES, both image / instance facts: PST_IMG (alloc.c's statics are image bytes; discharged at
   prh_img_A by S1ImgA.v pst_in_img_A) and HW (the text of the kit's prh_head_wide, `8 <= cf_head`; discharged by
   a Theorem Labs lane's preset_head_wide, lib/A/CfParamsPreset.v:95; the S5b record texts this file sits on do not yet carry
   the kit's name).
   SET: a working branch on a working branch 2e1d73b494d (vrd_chain_keep_w). A-only: B sites not measured.
   Numerals: 144 (LENGTH, parse_items' frame, as VrdIElem.v states it), 56 / 24 / 8 (LENGTH: node, cursor, word),
   2 ^ 46 / 2 ^ 48 / 2 ^ 64 (LENGTH: bounds). No ADDRESS literal. *)
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
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse VrdFrame VrdIElem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
(* the re-hiding move's wle' (YA0nH) and preset's zone (YGcfRehidePost.RZ_cf): vrd_ijrn's journal is at wle' *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
#[local] Notation PAI := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PAI).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

(* a position moved to a new machine state; every other field is P's *)
Definition vk_move (P : vrd_ipos) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k p : Z) : vrd_ipos :=
  MkIPos (ip_fx P) (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) regs mem md k
    (ip_n P) (ip_cap P) (ip_kids P) (ip_keys P) p (ip_acc P) (ip_f P) (ip_cont P)
    (ip_ok P) (ip_tr P) (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P).

(* ---- the byte-level keep outside a window ---- *)
Lemma vk_keep_rd : forall (H : word -> bool) (m m' : word -> option byte) lo hi (Pz : Z -> Prop),
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict H m' x = mrestrict H m x) ->
  (forall a, Pz a -> 0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi)) ->
  rd_keep SEGS (mrestrict H m) (mrestrict H m') Pz.
Proof.
  intros H m m' lo hi Pz HK HP. split.
  - intros a Ha. destruct (HP a Ha) as [Hr Hn]. unfold mbyte.
    rewrite (HK (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; exact Hn). reflexivity.
  - intros a Ha Hw. destruct (HP a Ha) as [Hr Hn]. unfold writable_at, wview in *.
    rewrite (HK (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; exact Hn). exact Hw.
Qed.

Lemma vk_keep_av : forall (H : word -> bool) (m m' : word -> option byte) lo hi a,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict H m' x = mrestrict H m x) ->
  0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros H m m' lo hi a HK Hr Hn. unfold aview, mbyte.
  rewrite (HK (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; exact Hn). reflexivity.
Qed.

Lemma vk_keep_ra : forall (H : word -> bool) (m m' : word -> option byte) lo hi a n,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict H m' x = mrestrict H m x) ->
  2 ^ 46 <= lo -> 0 <= a -> a + n <= 2 ^ 48 ->
  range_addressable (aview SEGS H m) SHADOW_OFF a n -> range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof.
  intros H m m' lo hi a n HK Hlo Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok).
  exists s. split; [|exact Hok]. unfold shadow_of_addr in *.
  assert (0 <= x / 8 < 2 ^ 45) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (vk_keep_av H m m' lo hi _ HK) by (unfold SHADOW_OFF; lia). exact Hs.
Qed.

Lemma vk_keep_hull : forall (H : word -> bool) (m m' : word -> option byte) lo hi a n,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict H m' x = mrestrict H m x) ->
  2 ^ 46 <= lo -> 0 <= a -> a + n <= 2 ^ 48 -> 0 < n ->
  shadow_hull_vis (aview SEGS H m) a n -> shadow_hull_vis (aview SEGS H m') a n.
Proof.
  intros H m m' lo hi a n HK Hlo Ha Han Hn HV s Hs. unfold shadow_addr in Hs.
  assert (0 <= (a + n - 1) / 8 < 2 ^ 45) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (0 <= a / 8) by (apply Z.div_pos; lia).
  assert (Hs2 : 0 <= s < 2 ^ 46).
  { split.
    - assert (0 <= (SHADOW_OFF + a / 8) / 8 * 8) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; unfold SHADOW_OFF; lia). lia.
    - assert ((SHADOW_OFF + (a + n - 1) / 8) / 8 * 8 <= SHADOW_OFF + (a + n - 1) / 8) by
        (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
      unfold SHADOW_OFF in *. lia. }
  rewrite (vk_keep_av H m m' lo hi _ HK) by lia. apply HV. exact Hs.
Qed.

(* ---- the harness blocks lie below the allocator ceiling ---- *)
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.

Lemma vk_lam_low : forall ly S Hp W mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ 4096 <= a /\ a + k <= alloc_ceiling.
Proof.
  intros ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL0 Hin.
  destruct (prh_ledger_hblock (L := A_prog_listing) (PA := PAI) B ly S Hp W mem Lam peak cnt fail ran a k most own
              HL0 Hin)
    as (Hk & Hab & _).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4 & Hc & _).
  pose proof (req_size_pos (k + cf_head)) as Hrq. pose proof (@cf_head_nonneg cp) as Hch.
  destruct Hrq as [_ Hrq]; [lia|]. lia.
Qed.

(* ---- the bytes below the allocator ceiling are kept ---- *)
Lemma vk_keep_low : forall (H : word -> bool) (m m' : word -> option byte) a0 n (Pz : Z -> Prop),
  (forall x : word, ~ (a0 <= bv_unsigned x < a0 + n) -> mrestrict H m' x = mrestrict H m x) ->
  alloc_ceiling <= a0 -> (forall a, Pz a -> 0 <= a < alloc_ceiling) ->
  rd_keep SEGS (mrestrict H m) (mrestrict H m') Pz.
Proof.
  intros H m m' a0 n Pz HK Ha0 HP. apply (vk_keep_rd H m m' a0 (a0 + n) Pz HK).
  intros a Ha. pose proof asan_consts as (C1 & _). destruct (HP a Ha). split; lia.
Qed.

Lemma vk_apresent_keep : forall (H : word -> bool) (m m' : word -> option byte) a0 n a,
  (forall x : word, ~ (a0 <= bv_unsigned x < a0 + n) -> mrestrict H m' x = mrestrict H m x) ->
  0 <= a < 2 ^ 64 -> ~ (a0 <= a < a0 + n) -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a0 n a HK Hr Hn [Hh (b & Hb)]. split; [exact Hh|]. exists b.
  pose proof (HK (Z_to_bv 64 a)) as E. rewrite unsigned_lit_small in E by lia. specialize (E Hn).
  unfold mrestrict in E. rewrite Hh in E. rewrite E. exact Hb.
Qed.

(* the harness blocks a position holds (its D) lie below the ceiling *)
Lemma vk_D_low : forall ly S Hp W mem md ly0 S0 D tr rest d b x,
  ARx ly S Hp W mem md -> rd_blocks_move B ly0 S0 ly S D tr rest d -> In b D -> pj_holdsR b x ->
  4096 <= x < alloc_ceiling.
Proof.
  intros ly S Hp W mem md ly0 S0 D tr rest d [a k] x HAR (_ & HPm & _) Hin Hx.
  unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
  assert (Hab : In (a - cf_head, k + cf_head) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. left. unfold prhReader_ab.
    exact (in_map (fun ak => (fst ak - cf_head, snd ak + cf_head)) D (a, k) Hin). }
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4 & Hc & _).
  pose proof (@cf_head_nonneg cp) as Hch.
  destruct (req_size_pos (k + cf_head)) as [_ Hrq]; [lia|]. lia.
Qed.

(* the stack bounds every position needs *)
Lemma vk_sp_bounds : forall CTX CTX0 CW E, vrd_ient_ok B ARx CTX CTX0 CW E ->
  alloc_ceiling <= spZ (ie_regs E) /\ 0 <= ie_e E /\ spZ (ie_regs E) + ie_e E <= 2 ^ 47 /\
  spZ (ie_regs E) <= ie_q E /\ ie_q E + 24 <= spZ (ie_regs E) + ie_e E /\ 4096 <= ie_v E.
Proof.
  intros CTX CTX0 CW E HEN.
  destruct HEN as ((HAF & _) & _ & _ & _ & HRD & _).
  destruct HAF as (_ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & HS0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
  destruct HRD as (_ & _ & _ & _ & _ & (He0 & _ & Hetop & _) & Hq0 & Hq24 & _ & _ & _ & _ & (Hv4 & _) & _).
  repeat split; lia.
Qed.

Variable HW : 8 <= cf_head.
Variable PST_IMG : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a.

Ltac vk_proj := unfold vk_move; cbn [ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids ip_keys
  ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].

(* ==== THE TRANSPORT ==== *)
Lemma vk_cur_store_keep : forall CTX CTX0 CW E P Dx regs mem' md' k' p' a0 n,
  pi_frame F_parse_items = 144 -> pi_s0cur F_parse_items = Some 0 ->
  vrd_ient_ok B ARx CTX CTX0 CW E ->
  vrd_iframe E P -> vrd_inode E P Dx -> vrd_icur B E P -> vrd_ijrn B ARx SK E P ->
  alloc_ceiling <= a0 -> 0 <= n -> a0 + n <= 2 ^ 64 ->
  (forall a, a0 <= a < a0 + n -> inFP (rd_fp (ie_q E) (ie_v E)) a) ->
  (forall a, a0 <= a < a0 + n -> ~ (spZ (ie_regs E) - 144 <= a < spZ (ie_regs E))) ->
  (forall x : word, ~ (a0 <= bv_unsigned x < a0 + n) ->
     mrestrict (w_H (ip_W P)) mem' x = mrestrict (w_H (ip_W P)) (ip_mem P) x) ->
  spZ regs = spZ (ip_regs P) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  pj_in_okR SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) (ie_text E) (ie_len E) p' (Z.of_nat (ie_d E) + 1)
    (ie_tb E) ->
  (length (rest_atR (ie_tb E) (ie_text E) p') <= length (rest_atR (ie_tb E) (ie_text E) (ip_p P)))%nat ->
  vrd_iframe E (vk_move P regs mem' md' k' p') /\ vrd_inode E (vk_move P regs mem' md' k' p') Dx /\
  vrd_icur B E (vk_move P regs mem' md' k' p') /\ vrd_ijrn B ARx SK E (vk_move P regs mem' md' k' p').
Proof.
  intros CTX CTX0 CW E P Dx regs mem' md' k' p' a0 n Himg Hs0c HEN HFR HND HCU HJN Ha0 Hn Han Hwfp Hwfr HK Hsp
    HJ' Hpin' Hrest.
  pose proof asan_consts as (C1 & _).
  destruct (vk_sp_bounds CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  assert (Bv56 : ie_v E + 56 <= alloc_ceiling) by (eapply vrd_node_low; eassumption).
  pose proof HJN as ((HAR & _) & _).
  pose proof HJN as (_ & _ & _ & _ & _ & HBM & _).
  assert (Bsp0 : 0 <= spZ (ie_regs E) - 144).
  { pose proof HFR as (Hf0 & _). rewrite <- Hf0. unfold spZ.
    pose proof (bv_unsigned_in_range 64 (getr (ip_regs P) 2%bv)) as Hr. lia. }
  assert (HKfr : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
                   (fun x => spZ (ie_regs E) - 144 <= x < spZ (ie_regs E))).
  { apply (vk_keep_rd _ (ip_mem P) mem' a0 (a0 + n) _ HK). intros a Ha. split; [lia|]. intros Hw. exact (Hwfr a Hw Ha). }
  assert (HDlow : forall b x, In b (ip_D P) -> pj_holdsR b x -> 4096 <= x < alloc_ceiling)
    by (intros b x Hb Hx; exact (vk_D_low _ _ _ _ _ _ _ _ _ _ _ _ b x HAR HBM Hb Hx)).
  split; [|split; [|split]].
  - (* the frame *)
    pose proof HFR as (Hf0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 &
      F17 & Fpres).
    unfold vrd_iframe. cbv zeta. vk_proj.
    split; [rewrite Hsp; exact Hf0|].
    repeat match goal with
    | |- val_mem _ _ _ _ _ /\ _ => split; [eapply VrdFrame.val_mem_keep; [eassumption|];
                                     eapply VrdFrame.rd_keep_mono; [exact HKfr | cbn; intros; lia]|]
    end.
    intros a Ha.
    apply (vk_apresent_keep _ (ip_mem P) mem' a0 n a HK); [lia | intros Hw; exact (Hwfr a Hw Ha) | exact (Fpres a Ha)].
  - (* the node and the trees *)
    pose proof HND as (Hhdr & Hnc & Hcap & Hc0 & Hlin & Hlen & (Di & HPerm & HTree) & Hrw & Hrav & Hrak & Hrakeys & Hkz).
    assert (HDsub : forall b, In b (Dx ++ kids_blkR (ip_kids P) (ip_cap P) ++
                      keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Di) -> In b (ip_D P))
      by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPerm) Hb)).
    assert (Hkids : 0 < ip_cap P -> In (ip_kids P, 56 * ip_cap P) (ip_D P)).
    { intros Hc. apply HDsub. apply in_or_app. right. apply in_or_app. left. unfold kids_blkR.
      destruct (Z.eqb_spec (ip_cap P) 0); [lia | left; reflexivity]. }
    assert (Hkeys : ie_o E = true -> 0 < ip_cap P -> In (ip_keys P, 8 * ip_cap P) (ip_D P)).
    { intros Ho Hc. apply HDsub. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      unfold keys_blkR. rewrite Ho. destruct (Z.eqb_spec (ip_cap P) 0); [lia | left; reflexivity]. }
    assert (HDi : forall z, rd_blk Di z -> 4096 <= z < alloc_ceiling).
    { intros z Hz. unfold rd_blk in Hz. apply Exists_exists in Hz as (b & Hb & Hz).
      apply (HDlow b z); [|exact Hz]. apply HDsub. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. exact Hb. }
    assert (HKlow : forall Pz, (forall a, Pz a -> 0 <= a < alloc_ceiling) ->
       rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem') Pz)
      by (intros Pz HP; exact (vk_keep_low _ (ip_mem P) mem' a0 n Pz HK Ha0 HP)).
    assert (Hkr : forall z, 0 < ip_cap P -> ip_kids P <= z < ip_kids P + 56 * ip_cap P -> 4096 <= z < alloc_ceiling)
      by (intros z Hc Hz; exact (HDlow _ z (Hkids Hc) Hz)).
    assert (Hyr : forall z, ie_o E = true -> 0 < ip_cap P -> ip_keys P <= z < ip_keys P + 8 * ip_cap P ->
                    4096 <= z < alloc_ceiling)
      by (intros z Ho Hc Hz; exact (HDlow _ z (Hkeys Ho Hc) Hz)).
    unfold vrd_inode. cbv zeta. vk_proj.
    split; [eapply pj_hdrR_keep; [exact Hhdr | apply HKlow; intros; lia]|].
    split; [exact Hnc|]. split; [exact Hcap|]. split; [exact Hc0|]. split; [exact Hlin|]. split; [exact Hlen|].
    split.
    { exists Di. split; [exact HPerm|].
      destruct (ie_o E) eqn:Ho; rewrite ?Ho in HTree.
      - eapply pj_memsR_keep; [exact HTree | intros; assumption | apply HKlow].
        rewrite length_rev, Hlen. intros z [Hz | [Hz | Hz]].
        + assert (0 < ip_cap P) by lia. pose proof (Hkr z ltac:(lia) ltac:(lia)). lia.
        + assert (0 < ip_cap P) by lia. pose proof (Hyr z eq_refl ltac:(lia) ltac:(lia)). lia.
        + pose proof (HDi z Hz). lia.
      - eapply pj_itemsR_keep; [exact HTree | intros; assumption | apply HKlow].
        rewrite length_map, length_rev, Hlen. intros z [Hz | Hz].
        + assert (0 < ip_cap P) by lia. pose proof (Hkr z ltac:(lia) ltac:(lia)). lia.
        + pose proof (HDi z Hz). lia. }
    split.
    { eapply rd_rw_keep; [exact Hrw | apply HKlow]. intros z Hz.
      destruct (Z.eq_dec (ip_cap P) 0) as [Hc | Hc]; [lia|].
      pose proof (Hkr z ltac:(lia) ltac:(lia)). lia. }
    split; [apply (vk_keep_ra _ (ip_mem P) mem' a0 (a0 + n) (ie_v E) 56 HK); [lia | lia | lia | exact Hrav]|].
    split.
    { intros Hc. pose proof (Hkr (ip_kids P) Hc ltac:(lia)). pose proof (Hkr (ip_kids P + 56 * ip_cap P - 1) Hc ltac:(lia)).
      apply (vk_keep_ra _ (ip_mem P) mem' a0 (a0 + n) _ _ HK); [lia | lia | lia | exact (Hrak Hc)]. }
    split; [|exact Hkz].
    intros Ho Hc. pose proof (Hyr (ip_keys P) Ho Hc ltac:(lia)).
    pose proof (Hyr (ip_keys P + 8 * ip_cap P - 1) Ho Hc ltac:(lia)).
    apply (vk_keep_ra _ (ip_mem P) mem' a0 (a0 + n) _ _ HK); [lia | lia | lia | exact (Hrakeys Ho Hc)].
  - (* the cursor, the text and the ledger *)
    pose proof HCU as (Hpin & Hraq & Hsrc & Hhome & Hled & Hfrm & Hcnt).
    unfold vrd_icur. cbv zeta. vk_proj.
    split; [exact Hpin'|].
    split; [apply (vk_keep_ra _ (ip_mem P) mem' a0 (a0 + n) (ie_q E) 24 HK); [lia | lia | lia | exact Hraq]|].
    split.
    { destruct Hsrc as (Hby & Ht4 & Htl & Ham & Hra & Hhull).
      split; [|split; [exact Ht4 | split; [exact Htl | split; [exact Ham | split]]]].
      - unfold PRH_Base.bytes_at in *. eapply garr8_keep; [exact Hby | apply (vk_keep_low _ (ip_mem P) mem' a0 n _ HK Ha0)].
        intros; lia.
      - apply (vk_keep_ra _ (ip_mem P) mem' a0 (a0 + n) _ _ HK); [lia | lia | lia | exact Hra].
      - intros Hl. apply (vk_keep_hull _ (ip_mem P) mem' a0 (a0 + n) _ _ HK); [lia | lia | lia | lia | exact (Hhull Hl)]. }
    split; [exact Hhome|].
    split.
    { eapply prh_ledger_kept_aview; [exact Hled | | | |].
      - intros a Ha. pose proof (@pa_segs_low _ _ PAI a (PST_IMG a Ha)) as Hl. unfold kLowMemEnd in Hl.
        apply (vk_keep_av _ (ip_mem P) mem' a0 (a0 + n) a HK); lia.
      - intros a k i Hin Hi.
        destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ Hled Hin) as (Hk0 & Hab & _).
        destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4 & Hc & _).
        destruct (req_size_pos (k + cf_head)) as [_ Hrq]; [lia|].
        apply (vk_keep_av _ (ip_mem P) mem' a0 (a0 + n) _ HK); lia.
      - intros a k _ Hab. exact Hab.
      - apply Permutation_refl. }
    split; [exact Hfrm|]. lia.
  - (* the journal, the caller window, the read-only view and the chain *)
    pose proof HJN as (HJ & Hwin & Hfz & Hfk & Haro & Hbm & Hch).
    unfold vrd_ijrn. vk_proj.
    split; [exact HJ'|].
    split.
    { intros a Ha Hnf. rewrite <- (Hwin a Ha Hnf).
      apply (vk_keep_av _ (ip_mem P) mem' a0 (a0 + n) a HK); [lia | intros Hw; exact (Hnf (Hwfp a Hw))]. }
    split; [exact Hfz|]. split; [exact Hfk|].
    split.
    { intros a Hro Hno Herr.
      assert (Hi : in_img SEGS a).
      { destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (@pa_relro_img _ _ PAI a Hr)]. }
      pose proof (@pa_segs_low _ _ PAI a Hi) as Hl. unfold kLowMemEnd in Hl.
      rewrite (vk_keep_av _ (ip_mem P) mem' a0 (a0 + n) a HK) by lia. exact (Haro a Hro Hno Herr). }
    split; [exact Hbm|].
    eapply vrd_chain_keep_w; try eassumption; try reflexivity.
    intros a Ha Hnf. apply (vk_keep_av _ (ip_mem P) mem' a0 (a0 + n) a HK); [lia | intros Hw; exact (Hnf (Hwfp a Hw))].
Qed.

End C.

Print Assumptions vk_cur_store_keep.
