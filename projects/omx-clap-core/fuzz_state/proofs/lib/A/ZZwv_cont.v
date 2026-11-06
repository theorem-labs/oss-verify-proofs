(* write_value's CONTAINER arms (fs.asan image A, write_value 0x83d84): the item loop's induction and the two arms
   wv_arr / wv_obj, composed from the call-site steps (ZZwv_cput / ZZwv_cind / ZZwv_cps / ZZwv_cwv), the entry and
   open steps (ZZwv_cent) and the two tail jumps (ZZwv_ctail).
   The statements of wv_arr / wv_obj are the ones a Theorem Labs lane takes as hypotheses in write_value's closing theorem
   (FSW_write_value.v, Section W), agreed 2026-10-29 and unchanged since.
   Rule 24: proves write_value's two container arms (the lane's lookup for write_value, proof-index v5, CHECKER
   CONFIRM a Theorem Labs lane; record in (internal path)). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat
FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model FSW_writer_kit
FSH_Fn_reader FSW_rd FSupoisonStack FSW_pj ZZwv_defs ZZwv_inv ZZwv_kit ZZwv_comp ZZwv_tree ZZwv_call ZZwv_step FSW_write_value.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the model: where one item's pieces sit in the arm's piece list ================= *)
(* the pieces of items 0 .. i - 1, then this item's comma / indent / value, then the rest *)
Lemma wv_items_at : forall p d l i x,
  nth_error l i = Some x ->
  wv_items p d 0%nat l =
  wv_items p d 0%nat (firstn i l)
  ++ (WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ WriterValue.wvpieces x p (d + 1))
  ++ wv_items p d (S i) (skipn (S i) l).
Proof.
intros p d l i x Hi.
assert (El : l = firstn i l ++ skipn i l) by (symmetry; apply firstn_skipn).
assert (Eln : length (firstn i l) = i).
{ rewrite length_firstn. apply Nat.min_l. apply Nat.lt_le_incl. apply nth_error_Some. rewrite Hi. discriminate. }
assert (Esk : skipn i l = x :: skipn (S i) l).
{ rewrite <- (firstn_skipn i l) in Hi. rewrite nth_error_app2 in Hi by lia.
  rewrite Eln, Nat.sub_diag in Hi.
  destruct (skipn i l) as [|y r] eqn:Es; [discriminate|].
  cbn [nth_error] in Hi. injection Hi as <-.
  replace (S i) with (1 + i)%nat by lia. rewrite <- skipn_skipn, Es. reflexivity. }
rewrite El at 1. rewrite wv_items_app, Eln, Esk, wv_items_cons, Nat.add_0_l.
rewrite <- app_assoc, <- app_assoc. reflexivity.
Qed.

Lemma wv_mems_at : forall p d l i nm x,
  nth_error l i = Some (nm, x) ->
  wv_mems p d 0%nat l =
  wv_mems p d 0%nat (firstn i l)
  ++ (WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ WriterSpec.spieces nm ++ [WriterValue.wsep p]
      ++ WriterValue.wvpieces x p (d + 1))
  ++ wv_mems p d (S i) (skipn (S i) l).
Proof.
intros p d l i nm x Hi.
assert (El : l = firstn i l ++ skipn i l) by (symmetry; apply firstn_skipn).
assert (Eln : length (firstn i l) = i).
{ rewrite length_firstn. apply Nat.min_l. apply Nat.lt_le_incl. apply nth_error_Some. rewrite Hi. discriminate. }
assert (Esk : skipn i l = (nm, x) :: skipn (S i) l).
{ rewrite <- (firstn_skipn i l) in Hi. rewrite nth_error_app2 in Hi by lia.
  rewrite Eln, Nat.sub_diag in Hi.
  destruct (skipn i l) as [|y r] eqn:Es; [discriminate|].
  cbn [nth_error] in Hi. injection Hi as <-.
  replace (S i) with (1 + i)%nat by lia. rewrite <- skipn_skipn, Es. reflexivity. }
rewrite El at 1. rewrite wv_mems_app, Eln, Esk, wv_mems_cons, Nat.add_0_l.
rewrite !app_assoc. reflexivity.
Qed.

(* the last item: nothing follows it in the loop *)
Lemma wv_items_last : forall p d l i, length l = S i -> wv_items p d (S i) (skipn (S i) l) = [].
Proof. intros p d l i Hl. rewrite skipn_all2 by lia. reflexivity. Qed.

Lemma wv_mems_last : forall p d l i, length l = S i -> wv_mems p d (S i) (skipn (S i) l) = [].
Proof. intros p d l i Hl. rewrite skipn_all2 by lia. reflexivity. Qed.

(* the comma piece: empty before the first item, one byte after it *)
Lemma wv_comma_0 : WriterValue.wcomma 0%nat = [].
Proof. reflexivity. Qed.

Lemma wv_comma_S : forall i, WriterValue.wcomma (S i) = [[44]].
Proof. reflexivity. Qed.

Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ================= the word the arm's chain clause names, read off the present frame bytes ================= *)
(* every byte of a present stack range is visible in the unpoisoned view (no stack byte is user-poisoned:
   ZZwv_kit.zwk_p_stack_not_ush), so the word at o - 8 exists and the arm can name it *)
Lemma wvc_rdword_present : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md ->
  (forall x, a <= x < a + 8 -> apresent (w_H W) mem x) ->
  alloc_ceiling <= a -> a + 8 <= 2 ^ 64 ->
  exists v, rdword (aview tfibsegs (w_H W) (unpoison U mem)) a = Some v.
Proof.
intros ly S U W mem md a HARU HP Hlo Hhi.
assert (AV : forall x, a <= x < a + 8 -> exists b, aview tfibsegs (w_H W) (unpoison U mem) x = Some b).
{ intros x Hx.
  rewrite (aview_unpoison_out tfibsegs _ U mem x
    (zwk_p_stack_not_ush B ly S U W mem md x HARU ltac:(lia))).
  destruct (HP x Hx) as (Hh & b & Hb).
  exists (bv_unsigned b). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity. }
unfold rdword.
destruct (AV a ltac:(lia)) as (b0 & E0). rewrite E0.
destruct (AV (a + 1) ltac:(lia)) as (b1 & E1). rewrite E1.
destruct (AV (a + 2) ltac:(lia)) as (b2 & E2). rewrite E2.
destruct (AV (a + 3) ltac:(lia)) as (b3 & E3). rewrite E3.
destruct (AV (a + 4) ltac:(lia)) as (b4 & E4). rewrite E4.
destruct (AV (a + 5) ltac:(lia)) as (b5 & E5). rewrite E5.
destruct (AV (a + 6) ltac:(lia)) as (b6 & E6). rewrite E6.
destruct (AV (a + 7) ltac:(lia)) as (b7 & E7). rewrite E7.
eexists. reflexivity.
Qed.

(* ================= one arm covers both containers ================= *)
(* wv_spec_on is contravariant in the class of trees: a proof for a wider class gives each narrower one *)
Lemma wvc_spec_on_mono : forall (P P' : PjTree.jv -> Prop) k,
  (forall t, P t -> P' t) -> wv_spec_on B P' k -> wv_spec_on B P k.
Proof.
intros P P' k Hsub H ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail Ht.
exact (H ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail (Hsub t Ht)).
Qed.


(* ================= the arm's fixed data, and the entry facts the steps assume ================= *)
(* F as the arm builds it from write_value's entry: the node's header fields, the out-object, the model state and
   the level; wf_sp F is the entry sp, wf_m F the level 2 - k, wf_ra8 F the word at o - 8. *)
Definition wvc_F (k : nat) (regs : bvmap 5 word) (ot o v pretty d : Z) (t : PjTree.jv)
    (str kids keys n : Z) (buf cap failed : Z) (text : list Z) (live peak cnt fail : Z)
    (UL D : list (Z * Z)) (ra8 : Z) : wvc_fix :=
  mkWF (PjTree.tag t) pretty d ot o v str kids keys n buf cap failed text live peak cnt fail UL D t ra8
    (spZ regs) (2 - k).

(* every entry hypothesis of ZZwv_step's Section A, in its declaration order, for wvc_F *)
Lemma wvc_arm_facts : forall k ly S U (W : world tfibsegs) regs mem md ch ot o v pretty d t D UL buf cap failed
    text live peak cnt fail num str kids keys n cap0 ra8,
  fpreU tfibsegs B (STK_write_value (2 - k)) ly S U W regs mem md ch ->
  ARU tfibsegs B ly S U W mem md ->
  PjStruct.pj_hdr tfibsegs (rdW W mem) v (PjTree.tag t) num str kids keys n cap0 ->
  ((exists items, t = PjTree.JArr items /\ n = Z.of_nat (length items) /\ keys = 0 /\ n <= cap0 /\
      (cap0 = 0 /\ kids = 0 \/ 0 < cap0 /\ In (kids, 56 * cap0) UL)) \/
   (exists members, t = PjTree.JObj members /\ n = Z.of_nat (length members) /\ n <= cap0 /\
      (cap0 = 0 /\ kids = 0 /\ keys = 0 \/ 0 < cap0 /\ In (kids, 56 * cap0) UL /\ In (keys, 8 * cap0) UL))) ->
  ublocks_ok B tfibsegs ly S W mem UL ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  0 <= pretty < alloc_ceiling -> 0 <= d < 2 ^ 31 -> d + Z.of_nat (PjTree.depth t) <= 2 ^ 31 - 1 ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  cap <= live -> jv_plain t -> Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  Z.of_nat (length text) + Z.of_nat (length (concat (WriterValue.wvpieces t (negb (pretty =? 0)) d))) + 1 <= WMAX ->
  wbudget_pre S cap cnt live
    (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterValue.wvpieces t (negb (pretty =? 0)) d)) ->
  (forall x, o <= x < ot -> ~ PjStruct.pj_foot v D x) ->
  let F := wvc_F k regs ot o v pretty d t str kids keys n buf cap failed text live peak cnt fail UL D ra8 in
  wf_sp F mod 16 = 0 /\ wf_ot F mod 16 = 0 /\ wf_o F + 32 <= wf_ot F /\ wf_o F mod 8 = 0 /\
  wf_ot F <= ly_top ly /\ ly_top ly <= 2 ^ 47 /\
  alloc_ceiling + STK_write_value (wf_m F) <= wf_sp F /\
  YK11.getr regs 3%bv = w64 (as_gp B) /\ YK11.getr regs 4%bv = w64 (as_tp B) /\
  0 <= wf_cap0 F /\ wf_cap0 F <= wf_live F /\ 0 <= wf_cnt0 F /\
  0 <= wf_p F < alloc_ceiling /\ 0 <= wf_d F /\
  wf_d F + Z.of_nat (PjTree.depth (wf_t F)) <= 2 ^ 31 - 1 /\
  Z.of_nat (length (wf_text0 F)) + Z.of_nat (length (concat (wvc_WP F))) + 1 <= WMAX /\
  wbudget_pre S (wf_cap0 F) (wf_cnt0 F) (wf_live F) (WriterApp.putN (wvc_st0 F) (wvc_WP F)) /\
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE /\
  (forall x, wf_o F <= x < wf_ot F -> ~ PjStruct.pj_foot (wf_v F) (wf_D F) x) /\
  jv_plain (wf_t F) /\
  ((wf_ty F = 5 /\ exists items, wf_t F = PjTree.JArr items /\ wf_n F = Z.of_nat (length items) /\ wf_keys F = 0) \/
   (wf_ty F = 6 /\ exists members, wf_t F = PjTree.JObj members /\ wf_n F = Z.of_nat (length members))) /\
  (exists num' capn, PjStruct.pj_hdr tfibsegs (rdW W mem) (wf_v F) (wf_ty F) num'
     (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn) /\
  0 <= wf_n F < 2 ^ 54 /\
  (0 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
   0 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling).
Proof.
intros k ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail num str kids keys n
  cap0 ra8 HPRE HARU HH HT HUL HOUT HGL Hp Hd Hdd Hspo Hoot Hot16 Hottop Hcapl Hplain Hfrl Hroom Hbud Hfoot F.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HPRE as (HPREU & _).
destruct HPREU as (HFN & _ & _).
destruct HFN as (HAR & Hret & Hra & Hgp & Htp & HSTK & Hpres & Hch & Hqt).
destruct HSTK as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HOUT as (Ho8 & Ho0 & Hotop & _ & Hbufr & Hcapr & _).
pose proof HGL as (_ & _ & _ & _ & Hlp & Hpk & Hcnt & _).
(* the kids / keys blocks of a non-empty container are live, so their bytes lie below alloc_ceiling *)
assert (HBLK : forall a m, In (a, m) UL -> 0 < m -> 4096 <= a /\ a + m <= alloc_ceiling).
{ intros a m Hin Hm. destruct (HUL a m Hin) as (Hab & Hal & Hpos & _).
  destruct (fsw_ablock_low B ly S W (unpoison U mem) md (a - HEAD) (m + HEAD) HAR Hab) as (A1 & A2 & A3).
  pose proof (req_size_pos (m + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ).
  unfold HEAD in *. lia. }
assert (HKK : 0 <= kids /\ kids + 56 * n <= alloc_ceiling /\ 0 <= keys /\ keys + 8 * n <= alloc_ceiling /\
              0 <= n < 2 ^ 54).
{ destruct HT as [(items & Et & En & Ek & Hnc & Hcase) | (members & Et & En & Hnc & Hcase)].
  - destruct Hcase as [(E0 & Ek0) | (Hc0 & Hin)].
    + subst cap0 kids keys. assert (n = 0) by lia. subst n. repeat split; lia.
    + destruct (HBLK kids (56 * cap0) Hin ltac:(lia)) as (K1 & K2).
      subst keys. repeat split; lia.
  - destruct Hcase as [(E0 & Ek0 & Ey0) | (Hc0 & Hink & Hiny)].
    + subst cap0 kids keys. assert (n = 0) by lia. subst n. repeat split; lia.
    + destruct (HBLK kids (56 * cap0) Hink ltac:(lia)) as (K1 & K2).
      destruct (HBLK keys (8 * cap0) Hiny ltac:(lia)) as (Y1 & Y2).
      repeat split; lia. }
unfold F, wvc_F. cbn [wf_sp wf_ot wf_o wf_ty wf_p wf_d wf_v wf_str wf_kids wf_keys wf_n wf_buf0 wf_cap0 wf_failed0
  wf_text0 wf_live wf_peak0 wf_cnt0 wf_fail0 wf_UL wf_D wf_t wf_ra8 wf_m].
unfold wvc_WP, wvc_st0. cbn [wf_t wf_p wf_d wf_failed0 wf_text0 wf_cap0 wf_cnt0 wf_fail0].
split; [exact Hal16|]. split; [exact Hot16|]. split; [exact Hoot|]. split; [exact Ho8|].
split; [exact Hottop|]. split; [lia|]. split; [lia|].
split; [exact Hgp|]. split; [exact Htp|].
split; [lia|]. split; [exact Hcapl|]. split; [lia|].
split; [exact Hp|]. split; [lia|]. split; [exact Hdd|].
split; [exact Hroom|]. split; [exact Hbud|]. split; [exact Hfrl|].
split; [exact Hfoot|]. split; [exact Hplain|].
split.
{ destruct HT as [(items & Et & En & Ek & _) | (members & Et & En & _)].
  - left. subst t. cbn [PjTree.tag]. split; [reflexivity|]. exists items. split; [reflexivity|]. split; [exact En | exact Ek].
  - right. subst t. cbn [PjTree.tag]. split; [reflexivity|]. exists members. split; [reflexivity | exact En]. }
split; [exists num, cap0; exact HH|].
split; [lia|]. lia.
Qed.


(* ================= the arm's piece list, split at item i ================= *)
(* the pieces already written when the arm stands at WVC_R_IND for item i: the opening bracket, the items before
   i, this item's comma and its indent *)
Definition wvc_done (F : wvc_fix) (i : nat) : list (list Z) :=
  let p := negb (wf_p F =? 0) in
  let d := wf_d F in
  match wf_t F with
  | PjTree.JArr items =>
      [[91]] ++ wv_items p d 0%nat (firstn i items) ++ WriterValue.wcomma i ++ WriterValue.wind p (d + 1)
  | PjTree.JObj members =>
      [[123]] ++ wv_mems p d 0%nat (firstn i members) ++ WriterValue.wcomma i ++ WriterValue.wind p (d + 1)
  | _ => []
  end.

(* the pieces still to write after item i's value: the later items, the closing indent and the closing bracket *)
Definition wvc_rest (F : wvc_fix) (i : nat) : list (list Z) :=
  let p := negb (wf_p F =? 0) in
  let d := wf_d F in
  match wf_t F with
  | PjTree.JArr items => wv_items p d (S i) (skipn (S i) items) ++ WriterValue.wind p d ++ [[93]]
  | PjTree.JObj members => wv_mems p d (S i) (skipn (S i) members) ++ WriterValue.wind p d ++ [[125]]
  | _ => []
  end.

(* item i's own pieces: the value for an array, the key, the separator and the value for an object *)
Definition wvc_itemP (F : wvc_fix) (nm : list Z) (u : PjTree.jv) : list (list Z) :=
  let p := negb (wf_p F =? 0) in
  let d := wf_d F in
  if wf_ty F =? 6
  then WriterSpec.spieces nm ++ [WriterValue.wsep p] ++ WriterValue.wvpieces u p (d + 1)
  else WriterValue.wvpieces u p (d + 1).

Lemma wvc_split_arr : forall F items i u,
  wf_t F = PjTree.JArr items -> wf_ty F = 5 -> nth_error items i = Some u ->
  wvc_WP F = wvc_done F i ++ wvc_itemP F [] u ++ wvc_rest F i.
Proof.
intros F items i u Et Ety Hi.
unfold wvc_WP, wvc_done, wvc_rest, wvc_itemP. rewrite Et, Ety, Z.eqb_refl || rewrite Et, Ety.
rewrite wv_pieces_arr.
assert (Hne : items <> []) by (intros ->; destruct i; cbn in Hi; discriminate).
destruct items as [|y ys]; [exfalso; exact (Hne eq_refl)|].
rewrite (wv_items_at (negb (wf_p F =? 0)) (wf_d F) (y :: ys) i u Hi).
cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvc_split_obj : forall F members i nm u,
  wf_t F = PjTree.JObj members -> wf_ty F = 6 -> nth_error members i = Some (nm, u) ->
  wvc_WP F = wvc_done F i ++ wvc_itemP F nm u ++ wvc_rest F i.
Proof.
intros F members i nm u Et Ety Hi.
unfold wvc_WP, wvc_done, wvc_rest, wvc_itemP. rewrite Et, Ety, Z.eqb_refl || rewrite Et, Ety.
rewrite wv_pieces_obj.
assert (Hne : members <> []) by (intros ->; destruct i; cbn in Hi; discriminate).
destruct members as [|y ys]; [exfalso; exact (Hne eq_refl)|].
rewrite (wv_mems_at (negb (wf_p F =? 0)) (wf_d F) (y :: ys) i nm u Hi).
cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

(* at the last item the rest is just the closing indent and bracket *)
Lemma wvc_rest_last_arr : forall F items i,
  wf_t F = PjTree.JArr items -> length items = S i ->
  wvc_rest F i = WriterValue.wind (negb (wf_p F =? 0)) (wf_d F) ++ [[93]].
Proof.
intros F items i Et Hl. unfold wvc_rest. rewrite Et.
rewrite (wv_items_last (negb (wf_p F =? 0)) (wf_d F) items i Hl). reflexivity.
Qed.

Lemma wvc_rest_last_obj : forall F members i,
  wf_t F = PjTree.JObj members -> length members = S i ->
  wvc_rest F i = WriterValue.wind (negb (wf_p F =? 0)) (wf_d F) ++ [[125]].
Proof.
intros F members i Et Hl. unfold wvc_rest. rewrite Et.
rewrite (wv_mems_last (negb (wf_p F =? 0)) (wf_d F) members i Hl). reflexivity.
Qed.

(* one step of the cursor: after item i's value, the comma and the indent of item i + 1 head the rest *)
Lemma wvc_skipn_cons : forall {X : Type} (l : list X) i x,
  nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
intros X l. induction l as [|y r IH]; intros i x Hi; [destruct i; discriminate|].
destruct i as [|i]; cbn [nth_error skipn] in *; [injection Hi as <-; reflexivity | exact (IH i x Hi)].
Qed.

Lemma wvc_rest_step_arr : forall F items i u,
  wf_t F = PjTree.JArr items -> wf_ty F = 5 -> nth_error items (S i) = Some u ->
  wvc_rest F i = WriterValue.wcomma (S i) ++ WriterValue.wind (negb (wf_p F =? 0)) (wf_d F + 1)
                 ++ wvc_itemP F [] u ++ wvc_rest F (S i).
Proof.
intros F items i u Et Ety Hi. unfold wvc_rest, wvc_itemP. rewrite Et, Ety, Z.eqb_refl || rewrite Et, Ety.
rewrite (wvc_skipn_cons items (S i) u Hi). cbn [wv_items].
rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvc_rest_step_obj : forall F members i nm u,
  wf_t F = PjTree.JObj members -> wf_ty F = 6 -> nth_error members (S i) = Some (nm, u) ->
  wvc_rest F i = WriterValue.wcomma (S i) ++ WriterValue.wind (negb (wf_p F =? 0)) (wf_d F + 1)
                 ++ wvc_itemP F nm u ++ wvc_rest F (S i).
Proof.
intros F members i nm u Et Ety Hi. unfold wvc_rest, wvc_itemP. rewrite Et, Ety, Z.eqb_refl || rewrite Et, Ety.
rewrite (wvc_skipn_cons members (S i) (nm, u) Hi). cbn [wv_mems].
rewrite <- !app_assoc. reflexivity.
Qed.


(* firstn one step: the prefix of length i + 1 is the prefix of length i with item i appended *)
Lemma wvc_firstn_S : forall {X : Type} (l : list X) i x,
  nth_error l i = Some x -> firstn (S i) l = firstn i l ++ [x].
Proof.
intros X l. induction l as [|y r IH]; intros i x Hi; [destruct i; discriminate|].
destruct i as [|i]; cbn [nth_error firstn] in *.
- injection Hi as <-. reflexivity.
- rewrite (IH i x Hi). reflexivity.
Qed.

(* the cursor's own step on the written prefix: item i's pieces, then the comma and the next indent *)
Lemma wvc_done_step_arr : forall F items i u,
  wf_t F = PjTree.JArr items -> wf_ty F = 5 -> nth_error items i = Some u ->
  wvc_done F (S i) =
    wvc_done F i ++ wvc_itemP F [] u ++ [[44]] ++ WriterValue.wind (negb (wf_p F =? 0)) (wf_d F + 1).
Proof.
intros F items i u Et Ety Hi. unfold wvc_done, wvc_itemP. rewrite Et, Ety, Z.eqb_refl || rewrite Et, Ety.
rewrite (wvc_firstn_S items i u Hi), wv_items_app.
assert (Elen : length (firstn i items) = i).
{ rewrite length_firstn. apply Nat.min_l. apply Nat.lt_le_incl. apply nth_error_Some. rewrite Hi. discriminate. }
rewrite Elen, Nat.add_0_l. cbn [wv_items app].
rewrite wv_comma_S, ?app_nil_r. cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvc_done_step_obj : forall F members i nm u,
  wf_t F = PjTree.JObj members -> wf_ty F = 6 -> nth_error members i = Some (nm, u) ->
  wvc_done F (S i) =
    wvc_done F i ++ wvc_itemP F nm u ++ [[44]] ++ WriterValue.wind (negb (wf_p F =? 0)) (wf_d F + 1).
Proof.
intros F members i nm u Et Ety Hi. unfold wvc_done, wvc_itemP. rewrite Et, Ety, Z.eqb_refl || rewrite Et, Ety.
rewrite (wvc_firstn_S members i (nm, u) Hi), wv_mems_app.
assert (Elen : length (firstn i members) = i).
{ rewrite length_firstn. apply Nat.min_l. apply Nat.lt_le_incl. apply nth_error_Some. rewrite Hi. discriminate. }
rewrite Elen, Nat.add_0_l. cbn [wv_mems app].
rewrite wv_comma_S, ?app_nil_r. cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

(* the first item: nothing is written but the opening bracket and the first indent *)
Lemma wvc_done_0_arr : forall F items,
  wf_t F = PjTree.JArr items -> wf_ty F = 5 ->
  wvc_done F 0 = [[91]] ++ WriterValue.wind (negb (wf_p F =? 0)) (wf_d F + 1).
Proof. intros F items Et Ety. unfold wvc_done. rewrite Et. cbn [firstn wv_items app]. reflexivity. Qed.

Lemma wvc_done_0_obj : forall F members,
  wf_t F = PjTree.JObj members -> wf_ty F = 6 ->
  wvc_done F 0 = [[123]] ++ WriterValue.wind (negb (wf_p F =? 0)) (wf_d F + 1).
Proof. intros F members Et Ety. unfold wvc_done. rewrite Et. cbn [firstn wv_mems app]. reflexivity. Qed.

End C.
