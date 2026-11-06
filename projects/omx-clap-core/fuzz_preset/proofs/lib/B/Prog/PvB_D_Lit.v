(* fuzz_preset image B (asan-ubsan), parse_value 0x8637c, segment D (the DISPATCH): the PACKAGING of
   literal's post (the tliteral_specX, lib/A/PRH_FnReader.v:326-355) into parse_value's post part pv_Qm
   (PvB_Defs.v:167-198) for the three literal arms ('t' -> "true" type 2, 'f' -> "false" type 1, 'n' -> "null" type 0)
   (pvD_Qm_lit), and the end-of-text arm (skip leaves nothing: no call, code -1, the reader state as is; pvD_Qm_none).
   State-free: no machine code is walked; the callee's post and the cut's reader state are hypotheses.
   The model: jr_value at the dispatch byte c is `lit cw t (c :: y)` (PvB_Model.pvm_unfold), and the cursor p1 reads
   c :: y (PvB_Model.pvm_skip_rest). The node: v's 56 bytes were zero at entry (prhPv_node's pj_zeroR), pv_reader0
   carries them to the call, the call keeps [v + 4, v + 56) and either writes the type word (hit) or keeps it too
   (miss). The node's bytes are writable after the call because they lie off the image (the allocator's
   client-image law for a block or a fake frame, and the stack's floor alloc_ceiling above the image for the
   caller's window), so a visible byte there is a present one.
   Numerals: the node layout (LENGTH: 56 node bytes, 4 type bytes, 8 / 16 / .. / 48 field offsets), the literal
   types 0 / 1 / 2 and the dispatch bytes 116 / 102 / 110 (WORD, PjGrammar's w_true / w_false / w_null heads). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjTree PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_Frees.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Instance PIB : PrhImg := prh_img_B.
Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the kit rule: the allocator's laws over ARx (YCbqG.v AR_laws_x), as PvB_A.v / PvB_X.v take it *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

(* a byte off the image that the memory shows is a byte the memory holds, so it is writable *)
Lemma pvl_wr : forall (m : word -> option byte) x b, 0 <= x < 2 ^ 64 -> ~ in_img SEGS x ->
  mbyte SEGS m x = Some b -> writable_at SEGS m x.
Proof.
intros m x b Hx Hn Hb. unfold writable_at, wview. unfold mbyte in Hb. revert Hb.
destruct (m (Z_to_bv 64 x)) as [b'|]; intros Hb; [discriminate|].
rewrite (seg_rom_none SEGS x Hx Hn) in Hb. discriminate Hb.
Qed.

(* the zero byte, from the view to the memory *)
Lemma pvl_byte0 : forall H (m : word -> option byte) x, aview SEGS H m x = Some 0 ->
  mbyte SEGS (mrestrict H m) x = Some (Z_to_bv 8 0).
Proof.
intros H m x E. unfold aview in E. revert E.
destruct (mbyte SEGS (mrestrict H m) x) as [b|]; intros E; [|discriminate E].
cbn [option_map] in E. injection E as E. f_equal. apply bv_eq. rewrite E. reflexivity.
Qed.

(* a zeroed node reads 0 at each of its bytes *)
Lemma pvl_zero_at : forall H (m : word -> option byte) v x, pj_zeroR SEGS (mrestrict H m) v -> v <= x < v + 56 ->
  aview SEGS H m x = Some 0.
Proof.
intros H m v x Hz Hx. unfold pj_zeroR, garr8 in Hz.
destruct (Hz (Z.to_nat (x - v))) as [Hv _]; [rewrite repeat_length; lia|].
specialize (Hv 0%nat ltac:(lia)). rewrite nth_repeat in Hv.
replace (v + Z.of_nat (Z.to_nat (x - v)) + Z.of_nat 0) with x in Hv by lia.
unfold aview. rewrite Hv. reflexivity.
Qed.

Lemma pvl_le0 : forall (n k : nat), le_byte 0 n k = 0.
Proof.
intros n k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l. reflexivity.
Qed.

(* n zero bytes are the value 0 *)
Lemma pvl_val0 : forall (m : word -> option byte) a (n : nat),
  (forall x, a <= x < a + Z.of_nat n -> mbyte SEGS m x = Some (Z_to_bv 8 0)) -> val_mem SEGS m a n 0.
Proof.
intros m a n H k Hk. rewrite H by lia. do 2 f_equal. symmetry. exact (pvl_le0 n k).
Qed.

(* the header of a node off the image: the type word ty, every other field 0 *)
Lemma pvl_hdr : forall (m : word -> option byte) v ty, v mod 8 = 0 -> 0 <= v -> v + 56 < 2 ^ 64 ->
  (forall x, v <= x < v + 56 -> ~ in_img SEGS x) ->
  0 <= ty < 2 ^ 32 -> val_mem SEGS m v 4 ty ->
  (forall x, v + 4 <= x < v + 56 -> mbyte SEGS m x = Some (Z_to_bv 8 0)) ->
  pj_hdrR SEGS m v ty 0 0 0 0 0 0.
Proof.
intros m v ty Hal H0 H64 NI Hty Hv Hz.
assert (U : forall a, v + 8 <= a -> a + 8 <= v + 56 -> rd_u64 SEGS m a 0).
{ intros a H1 H2. split; [lia|]. apply pvl_val0. intros x Hx. apply Hz. lia. }
split; [split; [exact Hal|]|].
{ intros x Hx. destruct (Z_lt_le_dec x (v + 4)) as [Hlt|Hge].
  - pose proof (Hv (Z.to_nat (x - v)) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
    replace (v + (x - v)) with x in Hb by lia.
    exact (pvl_wr m x _ ltac:(lia) (NI x Hx) Hb).
  - exact (pvl_wr m x _ ltac:(lia) (NI x Hx) (Hz x ltac:(lia))). }
split; [split; [exact Hty | exact Hv]|].
split; [apply U; lia|]. split; [apply U; lia|]. split; [apply U; lia|].
split; [apply U; lia|]. split; [apply U; lia|]. apply U; lia.
Qed.

(* one conjunct of a hypothesis, found by its type wherever it sits (the cut's conjunct order may move) *)
Local Ltac pvl_pick H := clear - H; repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end; assumption.

(* the entry node, from the entry premises: aligned, in range, off the image, zero; and the text's cursor bounds *)
Lemma pvl_entry_node : forall en, pv_pre B ARx en ->
  pe_v en mod 8 = 0 /\ 0 <= pe_v en /\ pe_v en + 56 < 2 ^ 64 /\
  (forall x, pe_v en <= x < pe_v en + 56 -> ~ in_img SEGS x) /\
  pj_zeroR SEGS (mrestrict (w_H (pe_W en)) (pe_mem en)) (pe_v en) /\
  pe_text en <= pe_p en <= pe_text en + pe_len en /\ Z.of_nat (length (pe_tb en)) = pe_len en.
Proof.
intros en HPRE. unfold pv_pre in HPRE.
assert (Hfpre : fpre B ARx (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en) (pe_mem en)
  (pe_md en) (pe_ch en)) by pvl_pick HPRE.
assert (Hrd : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by pvl_pick HPRE.
clear HPRE. unfold fpre, afn_pre_x in Hfpre. unfold rd_pre in Hrd.
assert (HAR : ARx (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en)) by pvl_pick Hfpre.
assert (Hstk : astk_ok (pe_STK en) (pe_ly en) (spZ (pe_regs en))) by pvl_pick Hfpre.
assert (Hin0 : pj_in_okR SEGS (mrestrict (w_H (pe_W en)) (pe_mem en)) (pe_q en) (pe_text en) (pe_len en) (pe_p en)
  (Z.of_nat (pe_d en)) (pe_tb en)) by pvl_pick Hrd.
assert (Hnode : prhPv_node B (pe_STK en) (pe_e en) (pe_ly en) (pe_S en) (pe_W en) (pe_regs en) (pe_mem en)
  (pe_Lam en) (pe_v en)) by pvl_pick Hrd.
assert (Hled0 : prh_ledger B (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_Lam en) (pe_peak en)
  (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en)) by pvl_pick Hrd.
clear Hfpre Hrd.
destruct Hstk as (_ & HSTK0 & Hceil & Hslo & _).
destruct Hnode as (Hv4 & Hv8 & _ & Hz0 & Hat & Hamr & _ & _).
destruct Hin0 as (_ & _ & _ & _ & _ & _ & _ & Hp0 & Hlen0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range in Hamr.
split; [exact Hv8|]. split; [lia|]. split; [lia|].
split; [|split; [exact Hz0 | split; [exact Hp0 | exact Hlen0]]].
intros x Hx.
destruct Hat as [(a0 & k & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & pos' & Hin & H1 & H2) | (H1 & H2)]]].
- destruct Hled0 as (_ & _ & HF & _). rewrite Forall_forall in HF.
  destruct (HF (a0, k) Hin) as (Hk0 & Hab0 & _). cbn [fst snd] in Hk0, Hab0.
  pose proof (@cf_head_nonneg cp) as Hcf.
  apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ (a0 - cf_head) (k + cf_head) x HAR Hab0).
  unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0); lia.
- apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ b m x HAR Hin).
  unfold req_size. destruct (Z.eqb_spec m 0); lia.
- apply (frm_img_x SEGS B ARx LAWS _ _ _ _ _ _ cid pos' x HAR Hin). lia.
- intros Hi. pose proof (@pa_segs_low _ B_prog_listing PA x Hi) as Hlo. lia.
Qed.

(* the reader state at the dispatch, the parts the arms read *)
Lemma pvl_reader0 : forall en pos p1 lyc Sc Wc memc, pv_reader0 B en pos p1 lyc Sc Wc memc ->
  frames Sc = (0, pos) :: frames (pe_S en) /\ ablocks B lyc Sc = ablocks B (pe_ly en) (pe_S en) /\
  blocks_bytes Sc = blocks_bytes (pe_S en) /\ room_live_cf Sc /\
  pj_in_okR SEGS (mrestrict (w_H Wc) memc) (pe_q en) (pe_text en) (pe_len en) p1 (Z.of_nat (pe_d en)) (pe_tb en) /\
  (forall a, pe_v en <= a < pe_v en + 56 -> aview SEGS (w_H Wc) memc a = aview SEGS (w_H (pe_W en)) (pe_mem en) a) /\
  prh_ledger B lyc Sc (pe_Hp en) Wc memc (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en)
    (pe_own en).
Proof.
intros en pos p1 lyc Sc Wc memc H. unfold pv_reader0, rd_room in H.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); pvl_pick H.
Qed.

(* the ledger move of a stretch with no allocator call (the batch kit's rd_ledger_move: g_most, the grant-all trace gt, the
   refused peak over no call is 0) *)
Lemma pvl_move0 : forall Lam peak cnt fail ran most gt, 0 <= Ledger.lsum Lam <= peak -> 0 <= cnt < 2 ^ 64 ->
  rd_ledger_move Lam peak cnt fail ran most [] gt [] [] Lam peak cnt fail ran.
Proof.
intros Lam peak cnt fail ran most gt Hpk Hcnt.
split; [|split; [|split; [|split; [|split; [|split]]]]].
- unfold prh_oks. cbn [PjGrammar.calls].
  split; [intros i Hi; exfalso; lia|]. split; [left; reflexivity|]. intros i Hi; exfalso; lia.
- cbn [PjGrammar.calls Z.of_nat]. rewrite Z.add_0_r. symmetry. apply Z.mod_small. lia.
- unfold fail_afterR. cbn [PjGrammar.calls Z.of_nat]. split; intros Hf; [lia | reflexivity].
- apply Permutation_refl.
- cbn. apply perm_nil.
- reflexivity.
- unfold prh_refused_peak. cbn [hpeakR PjGrammar.calls List.seq map fold_right]. lia.
Qed.

(* a node whose header is all zero is a refused tree with no blocks, at any depth *)
Lemma pvl_fd0 : forall (m : word -> option byte) lblk n v, pj_hdrR SEGS m v 0 0 0 0 0 0 0 ->
  pj_fdR SEGS m lblk n v [].
Proof.
intros m lblk n v HH.
destruct n; cbn [pj_fdR]; unfold pj_fshapeR;
  (split; [constructor|]); (split; [intros b x Hb; destruct Hb|]);
  exists 0, 0, 0, 0, 0, 0, 0, false, [], [], [], [];
  (split; [exact HH|]); (split; [left; split; reflexivity|]);
  (split; [left; repeat split|]); (split; [left; repeat split|]);
  (split; [cbn [app]; apply perm_nil|]); [split; reflexivity | reflexivity].
Qed.

(* THE PACKAGING of a literal arm: no model event on the path (literal makes no allocator call), so the room post is
   PvB_Room.v rp_nil over the keep from entry to the call's post state *)
Lemma pvD_Qm_lit : forall (en : PvEnt) (pos p1 : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
    (memc : word -> option byte) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world SEGS)
    (mem' : word -> option byte) (c ty code : Z) (y cw : list Z) (t : PjTree.jv),
  pv_pre B ARx en ->
  p1 = pe_text en + pe_len en - Z.of_nat (length (PjGrammar.skip (pe_rest en))) ->
  PjGrammar.skip (pe_rest en) = c :: y ->
  pv_reader0 B en pos p1 lyc Sc Wc memc ->
  (cw = PjGrammar.w_true /\ ty = 2 /\ t = PjTree.JTrue /\ c = 116) \/
  (cw = PjGrammar.w_false /\ ty = 1 /\ t = PjTree.JFalse /\ c = 102) \/
  (cw = PjGrammar.w_null /\ ty = 0 /\ t = PjTree.JNull /\ c = 110) ->
  (room_live_cf Sc -> room_live_cf S') -> Hp' = pe_Hp en -> ablocks B ly' S' = ablocks B lyc Sc ->
  frames S' = frames Sc -> blocks_bytes S' = blocks_bytes Sc ->
  prh_ledger B ly' S' Hp' W' mem' (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en)
    (pe_own en) ->
  (* the room at S', unmoved since entry: literal makes no allocator call (the live list equal, the run position
     kept); and the hull meters kept *)
  rp_keep (pe_S en) S' -> YGcfSecsStep.secs_same (pe_S en) S' ->
  (if PjGrammar.prefixb cw (rest_atR (pe_tb en) (pe_text en) p1)
   then code = 0 /\
     pj_in_okR SEGS (mrestrict (w_H W') mem') (pe_q en) (pe_text en) (pe_len en) (p1 + Z.of_nat (length cw))
       (Z.of_nat (pe_d en)) (pe_tb en) /\
     val_mem SEGS (mrestrict (w_H W') mem') (pe_v en) 4 ty
   else code = -1 /\
     pj_in_okR SEGS (mrestrict (w_H W') mem') (pe_q en) (pe_text en) (pe_len en) p1 (Z.of_nat (pe_d en)) (pe_tb en) /\
     (forall a, pe_v en <= a < pe_v en + 4 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H Wc) memc a)) ->
  (forall a, pe_v en + 4 <= a < pe_v en + 56 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H Wc) memc a) ->
  pv_Qm B en (fun S2 => Permutation (frames S2) ((0, pos) :: frames (pe_S en))) code ly' S' Hp' W' mem'.
Proof.
intros en pos p1 lyc Sc Wc memc ly' S' Hp' W' mem' c ty code y cw t
  HPRE Hp1 Hsk HR0 Harm Hroom HHp Hab Hfr Hbb Hled HPOS HSEC Hpost Hkeep.
destruct (pvl_entry_node en HPRE) as (Hv8 & Hv0 & Hv64 & NIMG & Hz0 & Hp0 & Hlen0).
destruct (pvl_reader0 en pos p1 lyc Sc Wc memc HR0) as (Rfr & Rab & Rbb & Rlive & _ & Rv & _).
pose proof Hled as ((_ & _ & _ & _ & _ & _ & _ & Hlive & _ & Hcnt & _) & _).
(* the bytes [v + 4, v + 56) are still zero *)
assert (Z0' : forall x, pe_v en + 4 <= x < pe_v en + 56 ->
  mbyte SEGS (mrestrict (w_H W') mem') x = Some (Z_to_bv 8 0)).
{ intros x Hx. apply pvl_byte0. rewrite (Hkeep x Hx), (Rv x ltac:(lia)).
  exact (pvl_zero_at _ _ _ x Hz0 ltac:(lia)). }
(* the cursor reads the dispatch byte *)
assert (Hrs : rest_atR (pe_tb en) (pe_text en) p1 = c :: y).
{ rewrite Hp1, <- Hsk. exact (proj1 (pvm_skip_rest (pe_tb en) (pe_text en) (pe_len en) (pe_p en) Hlen0 Hp0)). }
rewrite Hsk in Hp1.
(* the model: the literal arm *)
assert (HM : PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) [] = PjGrammar.lit cw t (c :: y) []).
{ rewrite pvm_unfold, Hsk.
  destruct Harm as [(-> & -> & -> & ->) | [(-> & -> & -> & ->) | (-> & -> & -> & ->)]]; reflexivity. }
assert (TAG : PjTree.tag t = ty /\ 0 <= ty < 2 ^ 32 /\
  (t = PjTree.JTrue \/ t = PjTree.JFalse \/ t = PjTree.JNull)).
{ destruct Harm as [(_ & -> & -> & _) | [(_ & -> & -> & _) | (_ & -> & -> & _)]];
    (split; [reflexivity | split; [lia | auto]]). }
(* the dispatch byte is no opener: the value's frees are the leaf's (PvB_Frees.pvf_frees_leaf) *)
assert (Hc12 : c <> 123 /\ c <> 91).
{ destruct Harm as [(_ & _ & _ & ->) | [(_ & _ & _ & ->) | (_ & _ & _ & ->)]]; split; discriminate. }
(* the parts both arms share *)
assert (HROOM : room_live_cf S') by exact (Hroom Rlive).
assert (HBB : blocks_bytes S' <= blocks_bytes (pe_S en) + prh_held []).
{ rewrite Hbb, Rbb. unfold prh_held. cbn [PjGrammar.held PjGrammar.calls Z.of_nat]. lia. }
assert (HMOVE : rd_ledger_move (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) []
  (pe_gt en) [] [] (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en))
  by (apply pvl_move0; clear - Hlive Hcnt; lia).
assert (HAB : Permutation (ablocks B ly' S') (prhReader_ab [] ++ ablocks B (pe_ly en) (pe_S en))).
{ rewrite Hab, Rab. cbn [prhReader_ab map app]. apply Permutation_refl. }
assert (HFR : Permutation (frames S') ((0, pos) :: frames (pe_S en))).
{ rewrite Hfr, Rfr. apply Permutation_refl. }
unfold PjGrammar.lit in HM. rewrite Hrs in Hpost.
(* the literal makes no allocator call: no hull use, and no call for an injected failure to reach *)
assert (HHULL : PresetHullBudget.hull_used (pe_S en) S' (PresetReqAt.rd_hevs (pe_gt en)))
  by exact (PresetHullBudget.hull_used_same (pe_S en) S' _ HSEC).
unfold pv_Qm.
revert HM Hpost. destruct (PjGrammar.prefixb cw (c :: y)) eqn:Epre; intros HM Hpost.
- (* HIT: the type word written, the cursor past the word *)
  destruct Hpost as (-> & Hin' & Hty).
  pose proof (PjGrammar.prefixb_app cw (c :: y) Epre) as Hpl.
  destruct TAG as (Etag & Hty32 & Ht). rewrite <- Etag in Hty.
  assert (HH : pj_hdrR SEGS (mrestrict (w_H W') mem') (pe_v en) (PjTree.tag t) 0 0 0 0 0 0).
  { apply pvl_hdr; [exact Hv8 | lia | lia | exact NIMG | rewrite Etag; exact Hty32 | exact Hty | exact Z0']. }
  exists [], (Some (t, skipn (length cw) (c :: y))), [], [], [],
    (pe_Lam en), (pe_peak en), (pe_cnt en), (pe_fail en), (pe_ran en).
  split; [exact HM|]. split; [exact Hled|]. split; [exact HROOM|]. split; [exact HHULL|].
  split; [exact (rp_nil [] (pe_S en) S' eq_refl HPOS)|].
  split; [apply pv_outc_nil;
    [unfold pe_gt, prhPv_gtrace; rewrite HM; reflexivity | rewrite HM; reflexivity | exact HPOS]|].
  split; [intros sm x os i H0 hist _ _ _ F; exfalso; unfold pe_gt, prhPv_gtrace in F; rewrite HM in F; cbn in F;
    lia|].
  split; [exact HMOVE|].
  split; [intros a k Hk; destruct Hk|]. split; [exact HAB|]. split; [cbv beta; exact HFR|].
  split; [cbn [hpeakR]; lia|]. split; [exact HBB|]. split; [reflexivity|].
  split; [reflexivity|].
  (* the free order: no block; the model frees nothing (lf of an empty trace) *)
  split; [intros _ n _; exists []; split;
    [exact (PvB_Frees.pvf_zero_foR SEGS _ _ n (pe_v en) _ HH)
    |rewrite (PvB_Frees.pvf_frees_leaf _ _ _ c y Hsk (proj1 Hc12) (proj2 Hc12)), HM; reflexivity]|].
  split; [|split; [|split]].
  + replace (pe_text en + pe_len en - Z.of_nat (length (skipn (length cw) (c :: y))))
      with (p1 + Z.of_nat (length cw)) by lia.
    exact Hin'.
  + destruct Ht as [-> | [-> | ->]]; cbn [pj_nodeR];
      (split; [constructor|]); (split; [intros b x Hb; destruct Hb|]);
      exists 0, 0, 0, 0, 0, 0; (split; [exact HH|]); repeat split.
  + destruct Ht as [-> | [-> | ->]]; apply PvB_Frees.pvf_ncap_leaf; intros ? E; discriminate E.
  + cbn [Ledger.lsum]. pose proof (PjGrammar.skip_len (pe_rest en)) as Hsl. rewrite Hsk in Hsl. lia.
- (* MISS: nothing stored, the node still the entry's zeroed one *)
  destruct Hpost as (-> & Hin' & Hv4').
  assert (HH : pj_hdrR SEGS (mrestrict (w_H W') mem') (pe_v en) 0 0 0 0 0 0 0).
  { apply pvl_hdr; [exact Hv8 | lia | lia | exact NIMG | lia | | exact Z0'].
    apply pvl_val0. intros x Hx. apply pvl_byte0.
    rewrite (Hv4' x ltac:(lia)), (Rv x ltac:(lia)). exact (pvl_zero_at _ _ _ x Hz0 ltac:(lia)). }
  exists [], None, [], [], [], (pe_Lam en), (pe_peak en), (pe_cnt en), (pe_fail en), (pe_ran en).
  split; [exact HM|]. split; [exact Hled|]. split; [exact HROOM|]. split; [exact HHULL|].
  split; [exact (rp_nil [] (pe_S en) S' eq_refl HPOS)|].
  split; [apply pv_outc_nil;
    [unfold pe_gt, prhPv_gtrace; rewrite HM; reflexivity | rewrite HM; reflexivity | exact HPOS]|].
  split; [intros sm x os i H0 hist _ _ _ F; exfalso; unfold pe_gt, prhPv_gtrace in F; rewrite HM in F; cbn in F;
    lia|].
  split; [exact HMOVE|].
  split; [intros a k Hk; destruct Hk|]. split; [exact HAB|]. split; [cbv beta; exact HFR|].
  split; [cbn [hpeakR]; lia|]. split; [exact HBB|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [intros _ n _; exists []; split;
    [exact (PvB_Frees.pvf_zero_foR SEGS _ _ n (pe_v en) _ HH)
    |rewrite (PvB_Frees.pvf_frees_leaf _ _ _ c y Hsk (proj1 Hc12) (proj2 Hc12)), HM; reflexivity]|].
  split.
  + destruct Hin' as (V1 & V2 & V3 & Hrw & _ & _ & _ & Hp & _ & _ & _ & Hdd).
    exists p1, (Z.of_nat (pe_d en)).
    split; [exact Hp|]. split; [lia|]. split; [exact V1|]. split; [exact V2|]. split; [exact V3|]. exact Hrw.
  + exact (pvl_fd0 _ _ _ _ HH).
Qed.

(* THE PACKAGING of the end-of-text arm (p >= end): skip leaves nothing, jr_value refuses, the reader state at the
   dispatch is the post as it stands (no call, no allocation, no write), the node still the entry's zeroed one *)
Lemma pvD_Qm_none : forall (en : PvEnt) (pos p1 : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
    (memc : word -> option byte),
  pv_pre B ARx en ->
  p1 = pe_text en + pe_len en - Z.of_nat (length (PjGrammar.skip (pe_rest en))) ->
  PjGrammar.skip (pe_rest en) = [] ->
  pv_reader0 B en pos p1 lyc Sc Wc memc ->
  pv_Qm B en (fun S2 => Permutation (frames S2) ((0, pos) :: frames (pe_S en))) (-1) lyc Sc (pe_Hp en) Wc memc.
Proof.
intros en pos p1 lyc Sc Wc memc HPRE Hp1 Hsk HR0.
destruct (pvl_entry_node en HPRE) as (Hv8 & Hv0 & Hv64 & NIMG & Hz0 & _ & _).
destruct (pvl_reader0 en pos p1 lyc Sc Wc memc HR0) as (Rfr & Rab & Rbb & Rlive & Hin1 & Rv & Hled).
pose proof Hled as ((_ & _ & _ & _ & _ & _ & _ & Hlive & _ & Hcnt & _) & _).
(* the room at the dispatch: pv_reader0's keep from entry (no allocator step since entry), and its hull meters kept *)
assert (HRP : rp_keep (pe_S en) Sc) by (unfold pv_reader0 in HR0; pvl_pick HR0).
assert (HSEC : YGcfSecsStep.secs_same (pe_S en) Sc) by (unfold pv_reader0 in HR0; pvl_pick HR0).
assert (Z0 : forall x, pe_v en <= x < pe_v en + 56 ->
  mbyte SEGS (mrestrict (w_H Wc) memc) x = Some (Z_to_bv 8 0)).
{ intros x Hx. apply pvl_byte0. rewrite (Rv x Hx). exact (pvl_zero_at _ _ _ x Hz0 Hx). }
assert (HH : pj_hdrR SEGS (mrestrict (w_H Wc) memc) (pe_v en) 0 0 0 0 0 0 0).
{ apply pvl_hdr; [exact Hv8 | lia | lia | exact NIMG | lia | | intros x Hx; apply Z0; lia].
  apply pvl_val0. intros x Hx. apply Z0. cbn in Hx. lia. }
assert (HM : PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) [] = (None, [], []))
  by (rewrite pvm_unfold, Hsk; reflexivity).
unfold pv_Qm.
exists [], None, [], [], [], (pe_Lam en), (pe_peak en), (pe_cnt en), (pe_fail en), (pe_ran en).
split; [exact HM|].
split; [exact Hled|]. split; [exact Rlive|].
split; [exact (PresetHullBudget.hull_used_same (pe_S en) Sc _ HSEC)|].
split; [exact (rp_nil [] (pe_S en) Sc eq_refl HRP)|].
split; [apply pv_outc_nil;
  [unfold pe_gt, prhPv_gtrace; rewrite HM; reflexivity | rewrite HM; reflexivity | exact HRP]|].
split; [intros sm x os i H0 hist _ _ _ F; exfalso; unfold pe_gt, prhPv_gtrace in F; rewrite HM in F; cbn in F; lia|].
split; [apply pvl_move0; clear - Hlive Hcnt; lia|].
split; [intros a k Hk; destruct Hk|].
split; [rewrite Rab; cbn [prhReader_ab map app]; apply Permutation_refl|].
split; [cbv beta; rewrite Rfr; apply Permutation_refl|].
split; [cbn [hpeakR]; lia|].
split; [rewrite Rbb; unfold prh_held; cbn [PjGrammar.held PjGrammar.calls Z.of_nat]; lia|].
split; [reflexivity|].
split; [reflexivity|].
split; [intros _ n _; exists []; split;
  [exact (PvB_Frees.pvf_zero_foR SEGS _ _ n (pe_v en) _ HH)
  |rewrite (PvB_Frees.pvf_frees_nil _ _ _ Hsk); reflexivity]|].
split.
- destruct Hin1 as (V1 & V2 & V3 & Hrw & _ & _ & _ & Hp & _ & _ & _ & Hdd).
  exists p1, (Z.of_nat (pe_d en)).
  split; [exact Hp|]. split; [lia|]. split; [exact V1|]. split; [exact V2|]. split; [exact V3|]. exact Hrw.
- exact (pvl_fd0 _ _ _ _ HH).
Qed.

(* ---- TRANSPORT across a POINTWISE-equal memory (the walk's runs change no byte but give only pointwise equal
   restricted memories; no functional extensionality). Each predicate below reads the memory only through its
   argument function (mbyte, wview) or through aview at the same hidden set. ---- *)
Lemma pvl_mbyte_ext : forall (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, mbyte SEGS m' a = mbyte SEGS m a.
Proof. intros m m' E a. unfold mbyte. rewrite E. reflexivity. Qed.

Lemma pvl_val_mem_ext : forall (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a n v, val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' E a n v H k Hk. rewrite (pvl_mbyte_ext m m' E). exact (H k Hk). Qed.

Lemma pvl_garr8_ext : forall (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a l, garr8 SEGS m a l -> garr8 SEGS m' a l.
Proof.
intros m m' E a l H j Hj. destruct (H j Hj) as [Hv Hr].
split; [exact (pvl_val_mem_ext m m' E _ _ _ Hv) | exact Hr].
Qed.

Lemma pvl_writable_ext : forall (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, writable_at SEGS m a -> writable_at SEGS m' a.
Proof. intros m m' E a H. unfold writable_at, wview in *. rewrite E. exact H. Qed.

Lemma pvl_rd_rw_ext : forall (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a n, rd_rw SEGS m a n -> rd_rw SEGS m' a n.
Proof. intros m m' E a n H x Hx. exact (pvl_writable_ext m m' E x (H x Hx)). Qed.

Lemma pvl_pj_in_okR_ext : forall (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall q text len p d tb, pj_in_okR SEGS m q text len p d tb -> pj_in_okR SEGS m' q text len p d tb.
Proof.
intros m m' E q text len p d tb (V1 & V2 & V3 & Hrw & Hal & Ht0 & Htl & Hp & Hlen & GT & Hsep & Hd).
split; [exact (pvl_val_mem_ext m m' E _ _ _ V1)|]. split; [exact (pvl_val_mem_ext m m' E _ _ _ V2)|].
split; [exact (pvl_val_mem_ext m m' E _ _ _ V3)|]. split; [exact (pvl_rd_rw_ext m m' E _ _ Hrw)|].
split; [exact Hal|]. split; [exact Ht0|]. split; [exact Htl|]. split; [exact Hp|]. split; [exact Hlen|].
split; [exact (pvl_garr8_ext m m' E _ _ GT)|]. split; [exact Hsep | exact Hd].
Qed.

Lemma pvl_aview_ext : forall (H : word -> bool) (m m' : word -> option byte),
  (forall x, mrestrict H m' x = mrestrict H m x) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' E a. unfold aview. rewrite (pvl_mbyte_ext _ _ E). reflexivity. Qed.

Lemma pvl_range_addressable_ext : forall (rd rd' : reader), (forall a, rd' a = rd a) ->
  forall b a n, range_addressable rd b a n -> range_addressable rd' b a n.
Proof. intros rd rd' E b a n H x Hx. destruct (H x Hx) as (s & Hs & Ho). exists s. rewrite E. split; assumption. Qed.

Lemma pvl_shadow_hull_vis_ext : forall (rd rd' : reader), (forall a, rd' a = rd a) ->
  forall x n, shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof. intros rd rd' E x n H s Hs. rewrite E. exact (H s Hs). Qed.

Lemma pvl_src_rd_ext : forall (W : world SEGS) (m m' : word -> option byte),
  (forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
  forall p l, src_rd W m p l -> src_rd W m' p l.
Proof.
intros W m m' E p l (Hb & H1 & H2 & H3 & Hra & Hhv).
pose proof (pvl_aview_ext _ m m' E) as EA.
split; [exact (pvl_garr8_ext _ _ E _ _ Hb)|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [exact (pvl_range_addressable_ext _ _ EA _ _ _ Hra)|].
intros Hl. exact (pvl_shadow_hull_vis_ext _ _ EA _ _ (Hhv Hl)).
Qed.

Lemma pvl_prh_ledger_ext : forall ly S Hp (W : world SEGS) (m m' : word -> option byte),
  (forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
  forall Lam peak cnt fail ran most own, prh_ledger B ly S Hp W m Lam peak cnt fail ran most own ->
  prh_ledger B ly S Hp W m' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W m m' E Lam peak cnt fail ran most own
  ((G1 & G2 & G3 & G4 & G5 & (Gm & Gmb) & (Go & Gob) & Gr) & Hnd & HF & HP).
split; [|split; [exact Hnd | split; [|exact HP]]].
- split; [exact (pvl_val_mem_ext _ _ E _ _ _ G1)|]. split; [exact (pvl_val_mem_ext _ _ E _ _ _ G2)|].
  split; [exact (pvl_val_mem_ext _ _ E _ _ _ G3)|]. split; [exact (pvl_val_mem_ext _ _ E _ _ _ G4)|].
  split; [exact (pvl_val_mem_ext _ _ E _ _ _ G5)|].
  split; [split; [exact (pvl_val_mem_ext _ _ E _ _ _ Gm) | exact Gmb]|].
  split; [split; [exact (pvl_val_mem_ext _ _ E _ _ _ Go) | exact Gob] | exact Gr].
- rewrite Forall_forall in HF |- *. intros ak Hak. destruct (HF ak Hak) as (K1 & K2 & K3 & K4 & K5).
  split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|].
  exact (pvl_val_mem_ext _ _ E _ _ _ K5).
Qed.

(* the reader state at the dispatch, carried to a pointwise-equal memory (prhReader_home, the allocator-state
   conjuncts and the room keep read no memory) *)
Lemma pv_reader0_ext : forall (en : PvEnt) (pos p1 : Z) (lyc : alayout) (Sc : astate) (W : world SEGS)
    (m m' : word -> option byte),
  (forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
  pv_reader0 B en pos p1 lyc Sc W m -> pv_reader0 B en pos p1 lyc Sc W m'.
Proof.
intros en pos p1 lyc Sc W m m' E (R1 & R2 & R3 & R4 & Rin & Rsrc & Rhome & Rv & Rra & Rled & Rrp & Rsec).
pose proof (pvl_aview_ext _ m m' E) as EA.
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
split; [exact (pvl_pj_in_okR_ext _ _ E _ _ _ _ _ _ Rin)|].
split; [exact (pvl_src_rd_ext _ _ _ E _ _ Rsrc)|]. split; [exact Rhome|].
split; [intros a Ha; rewrite EA; exact (Rv a Ha)|].
split; [exact (pvl_range_addressable_ext _ _ EA _ _ _ Rra)|].
split; [exact (pvl_prh_ledger_ext _ _ _ _ _ _ E _ _ _ _ _ _ _ Rled)|].
split; [exact Rrp | exact Rsec].
Qed.

End c.
