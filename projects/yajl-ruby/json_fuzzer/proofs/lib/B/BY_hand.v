(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Cells Mem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib RYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma agree_below : forall W m m' lo, munch W m m' -> wmono bsegs m m' -> Forall (fun iv => lo <= fst iv) W ->
  agree_on bsegs (fun a => a < lo) m m'.
Proof. aceil.
  intros W m m' lo MU WM FW a Ha Hlo. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia.
  clear -CEILB FW Hlo. induction W as [|[u v] W IH]; cbn; [exact I|]. inversion FW; subst. cbn in *. split; [lia| apply IH; assumption].
Qed.

Lemma bs_rep_agree : forall P m m' SB h,
  agree_on bsegs P m m' -> abs_rep m SB h -> (forall a, SB <= a < SB + h_stack_size h -> P a) ->
  0 <= h_used h <= h_stack_size h -> abs_rep m' SB h.
Proof. aceil.
  intros P m m' SB h HP BR HF HU. unfold RYajlRep.bs_rep in *. destruct (h_stack_blk h); [| exact BR].
  destruct BR as (NZ & junk & SC). split; [exact NZ|]. exists junk.
  eapply rw_cells_agree; [exact HP| exact SC|]. intros a Ha. apply HF. revert Ha. cbn [cells_size csize Nat.add]. lia.
Qed.

Lemma hand_struct_agree : forall P m m' h mh,
  agree_on bsegs P m m' -> ahand_struct m h mh -> (forall a, mh_addr mh <= a < mh_addr mh + 104 -> P a) -> ahand_struct m' h mh.
Proof. aceil.
  intros P m m' h mh HP ((pew & pad & HC & PW) & R) HF. split; [| exact R]. exists pew, pad. split; [| exact PW].
  eapply rw_cells_agree; [exact HP| exact HC|]. rewrite hand_cells_size. exact HF.
Qed.

(* [comment removed for export] *)
Definition yfoot (mh : mhand) (h : yhandle) (a : Z) : Prop :=
  exists b, In b (abl (yblocks mh h)) /\ ab_addr b <= a < ab_addr b + ab_size b.

Lemma yfoot_intro : forall mh h id A n a, In (id, A, n) (yblocks mh h) -> A <= a < A + n -> yfoot mh h a.
Proof. aceil.
  intros mh h id A n a Hin Ha. exists (mkABlock A n). split; [| cbn; lia].
  unfold abl. apply in_map_iff. exists (id, A, n). split; [reflexivity| exact Hin].
Qed.

(* [comment removed for export] *)
Lemma abl_in : forall id A n l, In (id, A, n) l -> In (mkABlock A n) (abl l).
Proof. aceil. intros id A n l H. unfold abl. apply in_map_iff. exists (id, A, n). split; [reflexivity| exact H]. Qed.
Lemma yb_in_hand : forall mh h, In (mkABlock (mh_addr mh) SIZEOF_HANDLE) (abl (yblocks mh h)).
Proof. aceil. intros. eapply abl_in. left. reflexivity. Qed.
Lemma yb_in_lexer : forall mh h, In (mkABlock (mh_lexer mh) SIZEOF_LEXER) (abl (yblocks mh h)).
Proof. aceil. intros. eapply abl_in. right. left. reflexivity. Qed.
Lemma yb_in_lexbuf : forall mh h, In (mkABlock (mb_addr (mh_lexbuf mh)) SIZEOF_BUF) (abl (yblocks mh h)).
Proof. aceil. intros. eapply abl_in. right. right. left. reflexivity. Qed.
Lemma yb_in_lexdata : forall mh h, yb_data (lx_buf (h_lexer h)) <> None ->
  In (mkABlock (mb_data (mh_lexbuf mh)) (yb_len (lx_buf (h_lexer h)))) (abl (yblocks mh h)).
Proof. aceil.
  intros mh h HD. eapply abl_in with (id := mb_did (mh_lexbuf mh)). unfold yblocks, lexer_blocks, buf_blocks.
  destruct (yb_data (lx_buf (h_lexer h))); [| exfalso; apply HD; reflexivity]. right. right. right. left. reflexivity.
Qed.
Lemma yb_in_decbuf : forall mh h, In (mkABlock (mb_addr (mh_decbuf mh)) SIZEOF_BUF) (abl (yblocks mh h)).
Proof. aceil. intros. eapply abl_in with (id := mb_id (mh_decbuf mh)). unfold yblocks, lexer_blocks. right. apply in_or_app. right. apply in_or_app. left. left. reflexivity. Qed.
Lemma yb_in_decdata : forall mh h, yb_data (h_decbuf h) <> None ->
  In (mkABlock (mb_data (mh_decbuf mh)) (yb_len (h_decbuf h))) (abl (yblocks mh h)).
Proof. aceil.
  intros mh h HD. eapply abl_in with (id := mb_did (mh_decbuf mh)). unfold yblocks, lexer_blocks. right. apply in_or_app. right. apply in_or_app. left.
  unfold buf_blocks. destruct (yb_data (h_decbuf h)); [| exfalso; apply HD; reflexivity]. right. left. reflexivity.
Qed.
Lemma yb_in_stack : forall mh h, h_stack_blk h <> None -> In (mkABlock (mh_stack mh) (h_stack_size h)) (abl (yblocks mh h)).
Proof. aceil.
  intros mh h HS. eapply abl_in with (id := mh_sid mh). unfold yblocks, lexer_blocks. right. apply in_or_app. right. apply in_or_app. right.
  unfold bs_blocks. destruct (h_stack_blk h); [| exfalso; apply HS; reflexivity]. left. reflexivity.
Qed.

Lemma hand_rep_agree : forall P m m' h mh,
  agree_on bsegs P m m' -> ahand_rep m h mh -> (forall a, yfoot mh h a -> P a) -> ahand_rep m' h mh.
Proof. aceil.
  intros P m m' h mh HP (HS & LR & BR & BSR) HF.
  assert (IN0 : In (mh_id mh, mh_addr mh, SIZEOF_HANDLE) (yblocks mh h)) by (left; reflexivity).
  assert (IN1 : In (mh_lid mh, mh_lexer mh, SIZEOF_LEXER) (yblocks mh h)) by (right; left; reflexivity).
  assert (IN2 : In (mb_id (mh_lexbuf mh), mb_addr (mh_lexbuf mh), SIZEOF_BUF) (yblocks mh h)) by (right; right; left; reflexivity).
  assert (IN3 : forall d, yb_data (lx_buf (h_lexer h)) = Some d -> In (mb_did (mh_lexbuf mh), mb_data (mh_lexbuf mh), yb_len (lx_buf (h_lexer h))) (yblocks mh h)).
  { intros d Hd. unfold yblocks, lexer_blocks, buf_blocks. rewrite Hd. right. right. right. left. reflexivity. }
  assert (IN4 : In (mb_id (mh_decbuf mh), mb_addr (mh_decbuf mh), SIZEOF_BUF) (yblocks mh h)).
  { unfold yblocks, lexer_blocks. right. apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
  assert (IN5 : forall d, yb_data (h_decbuf h) = Some d -> In (mb_did (mh_decbuf mh), mb_data (mh_decbuf mh), yb_len (h_decbuf h)) (yblocks mh h)).
  { intros d Hd. unfold yblocks, lexer_blocks. right. apply in_or_app. right. apply in_or_app. left. unfold buf_blocks. rewrite Hd. right. left. reflexivity. }
  assert (IN6 : forall k, h_stack_blk h = Some k -> In (mh_sid mh, mh_stack mh, h_stack_size h) (yblocks mh h)).
  { intros k Hk. unfold yblocks, lexer_blocks. right. apply in_or_app. right. apply in_or_app. right. unfold bs_blocks. rewrite Hk. left. reflexivity. }
  split; [| split; [| split]].
  - eapply hand_struct_agree; [exact HP| exact HS|]. intros a Ha. apply HF. eapply yfoot_intro; [exact IN0| unfold SIZEOF_HANDLE; lia].
  - eapply lexer_rep_agree; [exact HP| exact LR| | |].
    + intros a Ha. apply HF. eapply yfoot_intro; [exact IN1| lia].
    + intros a Ha. apply HF. eapply yfoot_intro; [exact IN2| lia].
    + intros HD a Ha. apply HF. destruct (yb_data (lx_buf (h_lexer h))) as [d|] eqn:E; [| exfalso; apply HD; reflexivity].
      eapply yfoot_intro; [exact (IN3 d eq_refl)| lia].
  - eapply buf_rep_agree; [exact HP| exact BR| |].
    + intros a Ha. apply HF. eapply yfoot_intro; [exact IN4| lia].
    + intros HD a Ha. apply HF. destruct (yb_data (h_decbuf h)) as [d|] eqn:E; [| exfalso; apply HD; reflexivity].
      eapply yfoot_intro; [exact (IN5 d eq_refl)| lia].
  - destruct HS as (_ & _ & _ & HU & HSB).
    destruct (h_stack_blk h) as [k|] eqn:E.
    + eapply bs_rep_agree; [exact HP| exact BSR| | exact HU]. intros a Ha. apply HF. eapply yfoot_intro; [exact (IN6 k eq_refl)| lia].
    + unfold RYajlRep.bs_rep in *. rewrite E in *. exact BSR.
Qed.

(* [comment removed for export] *)
Lemma hand_rep_below : forall W m m' lo h mh,
  ahand_rep m h mh -> munch W m m' -> wmono bsegs m m' -> Forall (fun iv => lo <= fst iv) W ->
  (forall b, In b (abl (yblocks mh h)) -> ab_addr b + ab_size b <= lo) -> ahand_rep m' h mh.
Proof. aceil.
  intros W m m' lo h mh HR MU WM FW HB. eapply hand_rep_agree; [eapply agree_below; [exact MU| exact WM| exact FW]| exact HR|].
  intros a (b & Hb & Ha). cbv beta. pose proof (HB b Hb). lia.
Qed.

Lemma ctx_rep_below : forall W m m' lo CX cx,
  actx_rep m CX cx -> munch W m m' -> wmono bsegs m m' -> Forall (fun iv => lo <= fst iv) W -> CX + 8 <= lo -> actx_rep m' CX cx.
Proof. aceil.
  intros W m m' lo CX cx HR MU WM FW HB. eapply ctx_rep_agree; [eapply agree_below; [exact MU| exact WM| exact FW]| exact HR|].
  intros a Ha. cbv beta. lia.
Qed.

Lemma text_at_below : forall W m m' lo T txt,
  atext_at m T txt -> munch W m m' -> wmono bsegs m m' -> Forall (fun iv => lo <= fst iv) W ->
  (zlength txt = 0 \/ T + zlength txt <= lo) -> atext_at m' T txt.
Proof. aceil.
  intros W m m' lo T txt HR MU WM FW HB. eapply text_at_agree; [eapply agree_below; [exact MU| exact WM| exact FW]| exact HR|].
  intros a Ha. cbv beta. lia.
Qed.

Lemma oshadow_munch : forall W m m' A n,
  oshadow m A n -> munch W m m' -> wmono bsegs m m' -> disjoint_from W (oshw_lo A) ((n + 7) / 8) -> oshadow m' A n.
Proof. aceil.
  intros W m m' A n (H8 & Hn & HU) MU WM HD. split; [exact H8|]. split; [exact Hn|].
  eapply (u8arr_transport bsegs); [exact HU| exact MU| exact WM|].
  pose proof (blk_shadow_length n ltac:(lia)) as L. rewrite L. unfold oshw_lo in HD. exact HD.
Qed.

(* [comment removed for export] *)
Lemma oshadow_below : forall W m m' lo A n,
  oshadow m A n -> munch W m m' -> wmono bsegs m m' -> Forall (fun iv => lo <= fst iv) W ->
  0 <= A -> A + n <= 2^47 -> 0x100080000000 <= lo -> oshadow m' A n.
Proof. aceil.
  intros W m m' lo A n HS MU WM FW A0 An Hlo. eapply oshadow_munch; [exact HS| exact MU| exact WM|].
  destruct HS as (H8 & Hn & _). unfold oshw_lo, A_SB.
  clear MU WM. induction W as [|[u v] W IH]; cbn; [exact I|]. inversion FW; subst. cbn in *.
  split; [left; Z.div_mod_to_equations; lia| apply IH; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition absep (b1 b2 : ablock) : Prop :=
  ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1.
Fixpoint asep_from (b : ablock) (l : list ablock) : Prop :=
  match l with [] => True | b' :: l' => absep b b' /\ asep_from b l' end.
Fixpoint aall_sep (l : list ablock) : Prop :=
  match l with [] => True | b :: l' => asep_from b l' /\ aall_sep l' end.
Lemma asep_from_In : forall b l b', asep_from b l -> In b' l -> absep b b'.
Proof. aceil. intros b l b'. induction l as [|x l IH]; cbn; [tauto|]. intros [H1 H2] [->|Hin]; auto. Qed.
Lemma asep_from_intro : forall b l, (forall b', In b' l -> absep b b') -> asep_from b l.
Proof. aceil. intros b l. induction l as [|x l IH]; cbn; intros H; [exact I|]. split; [apply H; auto| apply IH; auto]. Qed.
Lemma aall_sep_app_l : forall l1 l2, aall_sep (l1 ++ l2) -> aall_sep l1.
Proof. aceil.
  intros l1 l2. induction l1 as [|x l1 IH]; cbn; [tauto|]. intros [H1 H2]. split; [| apply IH; exact H2].
  clear -CEILB H1. induction l1 as [|y l1 IH]; cbn in *; [exact I|]. destruct H1 as [A B]. split; [exact A| apply IH; exact B].
Qed.
Lemma asep_from_app : forall b l1 l2, asep_from b (l1 ++ l2) <-> asep_from b l1 /\ asep_from b l2.
Proof. aceil. intros b l1 l2. induction l1 as [|x l1 IH]; cbn; tauto. Qed.
Lemma ablocks_all_sep : forall LB,
  (forall b1 b2, In b1 LB -> In b2 LB -> ab_addr b1 <> ab_addr b2 ->
      ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1) ->
  List.NoDup (map ab_addr LB) -> aall_sep LB.
Proof. aceil.
  intros LB HP HN.
  assert (G : forall l, (forall b, In b l -> In b LB) -> List.NoDup (map ab_addr l) -> aall_sep l).
  { intros l. induction l as [|x l IH]; cbn; intros HI ND; [exact I|].
    inversion ND as [|y ys Hni Hnd]; subst. split.
    - apply asep_from_intro. intros b' Hb'. apply HP; [apply HI; auto| apply HI; auto|].
      intros E. apply Hni. rewrite E. apply in_map. exact Hb'.
    - apply IH; [intros b Hb; apply HI; auto| exact Hnd]. }
  apply G; [auto| exact HN].
Qed.

Section Blk.
Variable Y : ay_params.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Lemma ay_all_sep : forall s LB LF m mo, y_AHK Y s LB LF m mo -> aall_sep LB.
Proof. aceil. intros s LB LF m mo H. destruct (BLKY _ _ _ _ _ H) as (_ & SEP & ND). apply ablocks_all_sep; assumption. Qed.
End Blk.

Lemma nodup_app_disj : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof. aceil.
  induction l1 as [|a l1 IH]; intros l2 x ND H1 H2; [destruct H1|].
  cbn in ND. inversion ND as [|y ys Hni Hnd]; subst.
  destruct H1 as [<-|H1]; [apply Hni; apply in_or_app; right; exact H2| exact (IH _ _ Hnd H1 H2)].
Qed.

(* [comment removed for export] *)
Lemma u8arr_agree : forall P m m' A bs,
  agree_on bsegs P m m' -> u8arr bsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> u8arr bsegs m' A bs.
Proof. aceil.
  intros P m m' A bs HP [HB HW] HR. split; [eapply bytes_at_agree; eauto| eapply wr_at_agree; eauto].
Qed.
Lemma oshadow_agree : forall P m m' A n,
  agree_on bsegs P m m' -> oshadow m A n -> (forall a, oshw_lo A <= a < oshw_hi A n -> P a) -> oshadow m' A n.
Proof. aceil.
  intros P m m' A n HP (H8 & Hn & HU) HR. split; [exact H8|]. split; [exact Hn|].
  eapply u8arr_agree; [exact HP| exact HU|]. rewrite (blk_shadow_length n) by lia. unfold oshw_lo, oshw_hi in HR. exact HR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma acb8_c8_in : forall m A pre post bs,
  rw_cells bsegs m A (pre ++ CB 8 bs :: post) -> rw_cells bsegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof. aceil.
  intros m A pre post bs [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite yle8_of_bytes by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.
Lemma acb4_c4_in : forall m A pre post bs,
  rw_cells bsegs m A (pre ++ CB 4 bs :: post) -> rw_cells bsegs m A (pre ++ C4 (le_bytes_to_word bs) :: post).
Proof. aceil.
  intros m A pre post bs [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite yle4_of_bytes by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.
(* [comment removed for export] *)
Lemma rw_cells_reshape : forall m A cs cs',
  rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells bsegs m A cs'.
Proof. aceil. intros m A cs cs' [[Hwf Hb] Hw] W' EB ES. split; [split; [exact W'| rewrite EB; exact Hb]| rewrite ES; exact Hw]. Qed.
End RC__1.
Ltac awordify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
  let rec go pre l := lazymatch l with
     | CB 8 ?b :: ?post => apply (acb8_c8_in m A pre post b) in H; cbn [app] in H; go constr:(pre ++ [C8 (le_bytes_to_word b)]) post
     | CB 4 ?b :: ?post => apply (acb4_c4_in m A pre post b) in H; cbn [app] in H; go constr:(pre ++ [C4 (le_bytes_to_word b)]) post
     | ?c :: ?l' => go constr:(pre ++ [c]) l'
     | [] => idtac end in
  go constr:(@nil cell) cs end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma land_align32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x - x mod 32.
Proof. aceil.
  intros x Hx.
  replace 18446744073709551584 with (Z.land (Z.lnot (Z.ones 5)) (Z.ones 64)) by reflexivity.
  rewrite Z.land_assoc. rewrite Z.land_ones by lia.
  rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
  rewrite Z.mod_small; Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Lemma land7_mod : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. aceil. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma stk_carve_at : forall m lo hi A (n : nat),
  stk bsegs m lo hi -> lo <= A -> A + Z.of_nat n <= hi ->
  stk bsegs m lo A /\ exists junk, rw_cells bsegs m A [CB n junk].
Proof. aceil.
  intros m lo hi A n ST H1 H2.
  destruct (stk_split bsegs m lo (A + Z.of_nat n) hi ST ltac:(lia)) as [ST1 _].
  destruct (stk_carve bsegs m lo (A + Z.of_nat n) n ST1 ltac:(lia)) as [ST2 [junk FR]].
  replace (A + Z.of_nat n - Z.of_nat n) with A in ST2, FR by lia. split; [exact ST2| exists junk; exact FR].
Qed.
Lemma stk_carve_at3 : forall m lo hi A (n : nat),
  stk bsegs m lo hi -> lo <= A -> A + Z.of_nat n <= hi ->
  stk bsegs m lo A /\ (exists junk, rw_cells bsegs m A [CB n junk]) /\ stk bsegs m (A + Z.of_nat n) hi.
Proof. aceil.
  intros m lo hi A n ST H1 H2.
  destruct (stk_split bsegs m lo (A + Z.of_nat n) hi ST ltac:(lia)) as [ST1 ST3].
  destruct (stk_carve bsegs m lo (A + Z.of_nat n) n ST1 ltac:(lia)) as [ST2 [junk FR]].
  replace (A + Z.of_nat n - Z.of_nat n) with A in ST2, FR by lia. split; [exact ST2|]. split; [exists junk; exact FR| exact ST3].
Qed.
(* [comment removed for export] *)
Lemma stk_agree : forall P m m' lo hi,
  agree_on bsegs P m m' -> stk bsegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk bsegs m' lo hi.
Proof. aceil.
  intros P m m' lo hi HP (H0 & H1 & H) HR. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [W [b Hb]]. destruct (HP a ltac:(lia) (HR a Ha)) as [E Wm]. split; [apply Wm; exact W|].
  exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

End RC__2.
