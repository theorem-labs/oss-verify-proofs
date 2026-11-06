(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the CALLER-WINDOW call kit over YCbqG.v's journal
   ajournal_x (allocator invariant a parameter ARx, ghost head set Hp after S, program statics PST), generic: no image
   class, no address, no ledger. Credit: WalkS4, lib/A/Prog/PRW_CallerJ.v at 85a188622c5 (statements and proofs taken
   from there; changes below). Donors there: cj_kept from cgif_file_fuzzer lib/YC20.v:311-325 tlzw_kept and
   lib/YC8n.v:272-287 tlzw_kept_of_journal (origin/release/pau-projects-recipes), generalised to ajournal_x's keep
   clauses; aj_call_xW from YCbqGcall.v aj_call_x (cgif YCbq.v:1845-1883 aj_call, origin/ossv/recipes).
   What a walk of a function in the caller-window form needs:
   - fwin_x / fpostW_x / fpostWF_x: lib/A/PRH_Base.v's fwin / fpostW / fpostWF (K0) restated with the image segs and
     the statics PST as parameters, same bodies: PRH_Base.fpostW B ARx SK STK d FP .. is
     fpostW_x (SK := SK) pa_segs B prh_pst ARx STK d FP .. by unfolding (this file does not Require lib/A).
   - START: ajournal_x_init_W, the widened journal (STK + e) (sp + e) at the entry state.
   - CALL of a caller-window callee: aj_call_xW / aj_call_xWF (callee state in mkst form), aj_call_xW_sp /
     aj_call_xWF_sp (the entry form of YCbqGcall.v's aj_call_x_sp: st_ok, ss_resv, the machine state ms).
     The footprint side condition is YCbqG.v's own fp_sub_x (h-hpreset-7 9052c7a7d74 :688-691), whose fourth
     disjunct `sp0 - STK <= a < sp0` is the caller's window: WalkS4's fp_sub_xW is that predicate, so this file
     no longer states one and ajournal_x_sub_W (the name WalkS4's callers use) is YCbqG's ajournal_x_sub.
   - vrd_call_W: h-verbs-3's lib/A/VrdArm.v call rule (6d4cddbdff5), premise shape kept, as a corollary of
     aj_call_xW_sp at e1 := - o.
   - aj_call_xWF_d: WalkH6's caller-window float call rule (h-walk-identity's S8aCallW.v aj_call_xWF), verbatim: no
     fwin_x for the callee and no window-kept clause on either side.
   - END: cj_kept (the keep clauses of ajournal_x relative to the entry, the walker's window and its written cells OR
     exempted) across stretches (cj_kept_exec) and calls (cj_kept_of_journal), chained (cj_kept_trans), closed by
     fpostW_x_of_kept / fpostWF_x_of_kept; fpostW_x_of_apost: apost_base_x is fpostW_x at e = 0.
   Numerals: 16, 4096, 8, 4 and 2 ^ 64 are LENGTH; 0 is LENGTH (the empty window e = 0) or DERIVED (event count);
   register numbers 1, 3, 4 (ra, gp, tp) are WORD. No address literal; no image constant. *)
(* Modified by Theorem Labs, 2026-10: the kit over a world relation R (suffix R). A free or realloc of a live block can
   hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a relation wider than wle with its journal at that
   relation (YCbqG.v ajournal_xR). cj_keptR is cj_kept with the world conjunct R W W2 (a copy of the body; the guard
   cj_kept_R_wle shows by reflexivity that cj_kept is cj_keptR at wle). The R forms of cj_kept_refl / cj_kept_exec /
   ajournal_x_init_W take R and its reflexivity, of cj_kept_trans / ajournal_x_sub_W R and its transitivity, of
   cj_kept_of_journal / fpostW_x_of_apost / fpostW_x_of_kept / fpostWF_x_of_kept R alone; the call rules
   aj_call_xWR / aj_call_xW_spR / aj_call_xWFR / aj_call_xWF_spR / vrd_call_WR / aj_call_xWF_dR take R and both laws
   first, then the plain rule's binders, with the journals, the callee's post (fpostW_xR / fpostWF_xR) and the
   conclusion at R. Each plain lemma is its R form at wle (wle_refl / wle_trans); its statement is unchanged.
   fpostW_x_R_lift: a plain fpostW_x (journal at wle) is fpostW_xR at every R that contains wle. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YCbqGcallW.v; 1356 of its 1435 lines of code are new or changed and 732 lines of the source are left out. *)
(* fuzz_preset, the #102 tx TEXT-STATE GLUE: image-free and allocator-parametric, ONE copy for the tx family's walks
   on the #102 kit (first lib/A/PRH_FnTx.v / PRH_Base.v of walk kit f97c8b2f046b, the tx texts decff67d721f's word for
   word; now PRH_FnTx.v 7cf918708def). OWNER a Theorem Labs lane, on that lane's branch; the SHARED HOME of the #102 tx
   glue (a Theorem Labs lane at 19:36Z: S10's #102 move cites this file). Generic in PA: every image bound is the instance's pa_lo / pa_hi or
   the CfImg's cf_img_lo / cf_img_top; no instance bound is bridged to a fixed image constant.
   It is the #102 form of S10's old-pin glue (lib/A/Prog/S10TxKit.v 8f827d2634fc and S10TxState.v 64aaa3f90115,
   cold/h-hpreset-7-walk-S10-fold), with S10's lemma names wherever a statement keeps its shape; it Requires none of
   S10's files. WHY A RE-WALK AND NOT A RE-FIT: S10's text state cannot be restated by renaming - prhtx_rec takes f,
   prh_ledger takes most / own, prhtx_fp is 28 bytes, and prhtx_out has THREE outcomes (a refused put RETURNS with
   failed = 1 and every later put takes its FAILED arm) where the old text had the fabortW abort arm; so the state
   carries the outcome so far, and every fold is a case analysis. What the #102 texts changed, and what this file does
   about it:
   - struct text has `int failed` at t + 24 (prhtx_rec's f, read as 4 bytes), and the record's footprint is 28 bytes
     (prhtx_fp, prhtx_place, prhtx_trace): every record lemma here is at 28;
   - THE REFUSED OUTCOME REPLACES THE ABORT ARM: every tx text's post is ONE fpostWm (no fabortW disjunct) whose body
     names the outcome (prhtx_out: DONE, FAILED AT ENTRY, REFUSED). So the program-call and tail-call rules here have
     no abort arm (s10_call_W / s10_call_Wm / s10_tail_W / s10_tail_Wm, S10TxKit's s10_call_orW .. less that arm);
   - the ledger carries g_most and g_own_ran_out (prh_ledger's `most own`); a refused grow sets own := 1;
   - the run premise of a caller text is guarded by f0 = 0, and the post's position is `exists j hist', j <= length
     (prhtx_evs ..) /\ iface_room_pos .. (rp_i + j) .. /\ (f0 = 0 -> f1 = 0 -> j = length ..) /\ (f0 <> 0 -> j = 0)`.
   THE TEXT STATE a caller carries after its puts of sizes ks (TxModel's list, the text it would append: add) is
   tx_state: the record, buffer, place, Hp, blocks and live bytes are prhtx_post of the caller's ENTRY at the buffer
   (b, cap), failed f, and what was ACTUALLY appended, pre; the outcome so far is prhtx_out f0 f own0 own b0 cap0 b cap
   (tx_capf len0 cap0 ks) add pre, exactly the text's own outcome over add; the realloc trace (prhtx_trace); the room
   invariant room_live_cf; the ledger at own. Its position is tx_pos: the text's own position clause over ks (tx_jok).
   So at the caller's return the text's post IS the state (tx_pos_post), and a callee's post folds in by
   tx_state_fold / tx_pos_fold, whose outcome half (tx_out_fold, tx_jok_fold) is the case analysis: DONE then DONE is
   DONE; DONE then REFUSED is REFUSED; FAILED then (the callee enters failed: its FAILED arm) is FAILED; REFUSED then
   FAILED is REFUSED. tx_put's own post (three arms and two position conjuncts) becomes the same form by tx_put_res,
   and its GROW premise comes from the caller's run window by tx_put_ev; the window itself by tx_window.
   IMAGE PREMISES (MARKED Section hypotheses, each with its owner):
   - LAWS : AR_laws_x pa_segs B ARx cf_head (the allocator relation's laws; the instance);
   - HPST / HPSTro : alloc.c's statics lie in the image and are not read-only (image facts; B: S1ImgB.v);
   - zs_aligned : the zero-shadow ranges of B are 8-aligned (owner a Theorem Labs lane, the unit's image binding of B);
   - img_shadow_vis_x : the shadow byte of an image address is visible, over the PER-INSTANCE bounds
     `@cf_img_lo ci` / `@cf_img_top ci` (h-mani-a8's rule 18:56Z; its B' instance lib/AU/AImgShadowVisCfB.v);
   - img_box / img_cf_box : the instance's kept_img bounds pa_lo / pa_hi lie in the low half and inside the CfImg
     bounds (closed facts of the instance: a vm_compute witness at it).
   Numerals: 8, 16, 24, 28 (LENGTH: word, the record's field offsets t + 8 / + 16 / + 24 and its 28 accessed bytes),
   4 (LENGTH: failed); 2 ^ 47, 2 ^ 64, 2 ^ 44, 2 ^ 46 (DERIVED: address-space and shadow bounds); 4096 (LENGTH: page);
   64 (LENGTH: GrantRo's hull margin). No ADDRESS. No lemma of a released plain or UBSan file is cited.
   Rule 24: proves no function (kind: glue). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YI00 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require TxModel WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.

(* ======== pure ======== *)
Lemma s10_capf1 : forall len cap n, TxModel.tx_capf len cap [n] = TxModel.tx_cap1 len cap n.
Proof. reflexivity. Qed.

Lemma s10_zsum1 : forall n, TxModel.zsum [n] = n.
Proof. intros n. cbn. lia. Qed.

(* the escaped string's pieces (TxModel.strp, one piece per tx_put call) concatenate to WriterSpec.wstr *)
Lemma s10_spcs_concat : forall c,
  concat (TxModel.spcs c) = if WriterSpec.special c then WriterSpec.esc c else [c].
Proof.
intros c. unfold TxModel.spcs. destruct ((c =? 34) || (c =? 92)) eqn:Hq.
- apply orb_true_iff in Hq. destruct Hq as [Hq | Hq]; apply Z.eqb_eq in Hq; subst c; reflexivity.
- cbn [concat]. rewrite app_nil_r. reflexivity.
Qed.

Lemma s10_spieces_run : forall bs run,
  concat (WriterSpec.spieces_run run bs) =
  run ++ concat (map (fun c => if WriterSpec.special c then WriterSpec.esc c else [c]) bs).
Proof.
induction bs as [|c bs IH]; intros run; cbn [WriterSpec.spieces_run map concat].
- rewrite !app_nil_r. reflexivity.
- destruct (WriterSpec.special c).
  + cbn [concat]. rewrite IH. reflexivity.
  + rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma s10_spcs_all : forall bs,
  concat (concat (map TxModel.spcs bs)) =
  concat (map (fun c => if WriterSpec.special c then WriterSpec.esc c else [c]) bs).
Proof.
induction bs as [|c bs IH]; [reflexivity|]. cbn [map concat]. rewrite concat_app, IH, s10_spcs_concat. reflexivity.
Qed.

Lemma s10_strp_wstr : forall bs, concat (TxModel.strp bs) = WriterSpec.wstr bs.
Proof.
intros bs. unfold TxModel.strp, WriterSpec.wstr, WriterSpec.spieces.
cbn [concat]. rewrite !concat_app, s10_spcs_all, s10_spieces_run. reflexivity.
Qed.

(* ---- address arithmetic (no state) ---- *)
Lemma s10_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma s10_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
unfold SHADOW_OFF in *. lia.
Qed.
(* the hull of a range at least 64 bytes inside [lo, hi) is the shadow of bytes of [lo, hi) (FuzzStrdup.v's
   sd_hull_img, c-omx-alloc; fuzz_grant GrantRo.v:82-100). PER-INSTANCE: lo / hi are the caller's bounds (kept_img's
   pa_lo / pa_hi), not one image's literals *)
Lemma s10_hull_img : forall lo hi a n s, 0 < n -> lo + 64 <= a -> a + n + 64 <= hi ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ lo <= 8 * (s - SHADOW_OFF) < hi.
Proof.
intros lo hi a n s Hn Hlo Hhi Hs. unfold shadow_addr in *.
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.

(* pairwise R is invariant under permutation when R is symmetric (zdisjoint is) *)
Lemma s10_pairwise_perm : forall (A : Type) (R : A -> A -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros A R Hs l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn [pairwise]; intros H.
- exact I.
- destruct H as [Hx Hl]. split; [|exact (IH Hl)].
  rewrite Forall_forall in Hx |- *. intros y Hy. apply Hx. apply (Permutation_in y (Permutation_sym P) Hy).
- destruct H as [Hy [Hx Hl]]. inversion Hy as [|? ? Hyx Hyl]. subst.
  split; [constructor; [apply Hs; exact Hyx | exact Hx] |]. split; [exact Hyl | exact Hl].
- exact (IH2 (IH1 H)).
Qed.

Lemma s10_zdisjoint_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b H. unfold zdisjoint in *. lia. Qed.

(* ---- the tx texts' outcome and position clauses, composed (pure) ---- *)
(* the text's position clause over the call sizes ks: j events of prhtx_evs len0 cap0 ks were made, all of them when
   the text entered and stayed at failed = 0, none when it entered failed *)
Definition tx_jok (len0 cap0 f0 f : Z) (ks : list Z) (j : nat) : Prop :=
  (j <= length (prhtx_evs len0 cap0 ks))%nat /\
  (f0 = 0 -> f = 0 -> j = length (prhtx_evs len0 cap0 ks)) /\ (f0 <> 0 -> j = 0%nat).

Lemma tx_jok_nil : forall len0 cap0 f0, tx_jok len0 cap0 f0 f0 [] 0.
Proof. intros len0 cap0 f0. unfold tx_jok. cbn [prhtx_evs length]. split; [lia | split; intros; lia]. Qed.

Section out. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Variable B : asyms.
(* what was appended is at most the text: all of it, nothing, or a prefix *)
Lemma tx_out_len : forall f0 f own0 own b0 cap0 b cap capf add pre,
  prhtx_out f0 f own0 own b0 cap0 b cap capf add pre -> (length pre <= length add)%nat.
Proof.
intros f0 f own0 own b0 cap0 b cap capf add pre
  [(_ & _ & _ & -> & _) | [(_ & _ & _ & -> & _) | (_ & _ & _ & (rest & ->) & _)]].
- lia.
- cbn [length]. lia.
- rewrite length_app. lia.
Qed.

(* the entry outcome: nothing appended, the outcome DONE when the text entered at failed = 0, else FAILED *)
Lemma tx_out_nil : forall len0 cap0 f0 own0 b0,
  prhtx_out f0 f0 own0 own0 b0 cap0 b0 cap0 (TxModel.tx_capf len0 cap0 []) [] [].
Proof.
intros len0 cap0 f0 own0 b0. unfold prhtx_out. cbn [TxModel.tx_capf].
destruct (Z.eq_dec f0 0) as [E|E].
- left. repeat split; first [exact E | reflexivity].
- right. left. repeat split; first [exact E | reflexivity].
Qed.

(* a callee's outcome folded into the caller's: the case analysis of the header *)
Lemma tx_out_fold : forall len0 cap0 f0 f f1 own0 own own' b0 b b1 cap cap1 (ks kc add addc pre prec : list Z),
  TxModel.zsum ks = Z.of_nat (length add) ->
  prhtx_out f0 f own0 own b0 cap0 b cap (TxModel.tx_capf len0 cap0 ks) add pre ->
  prhtx_out f f1 own own' b cap b1 cap1 (TxModel.tx_capf (len0 + Z.of_nat (length pre)) cap kc) addc prec ->
  prhtx_out f0 f1 own0 own' b0 cap0 b1 cap1 (TxModel.tx_capf len0 cap0 (ks ++ kc)) (add ++ addc)
    (pre ++ prec).
Proof.
intros len0 cap0 f0 f f1 own0 own own' b0 b b1 cap cap1 ks kc add addc pre prec Hks HO HOc.
assert (Ecap : TxModel.tx_capf len0 cap0 (ks ++ kc) =
  TxModel.tx_capf (len0 + TxModel.zsum ks) (TxModel.tx_capf len0 cap0 ks) kc) by (rewrite TxModel.tx_capf_app; reflexivity).
destruct HO as [(Hf0 & Hf & Ho & Ep & Ec) | [(Hf0 & Hf & Ho & Ep & Eb & Ec) | (Hf0 & Hf & Ho & (rest & Ea) & HR)]].
- subst f own pre cap.
  destruct HOc as [(_ & Hf1 & Ho' & Ep' & Ec') | [(Hc & _) | (_ & Hf1 & Ho' & (rest' & Ea') & HR')]].
  + left. split; [exact Hf0|]. split; [exact Hf1|]. split; [exact Ho'|]. split; [rewrite Ep'; reflexivity|].
    rewrite Ecap, Hks. exact Ec'.
  + exfalso. exact (Hc eq_refl).
  + right. right. split; [exact Hf0|]. split; [exact Hf1|]. split; [exact Ho'|].
    split; [exists rest'; rewrite Ea', app_assoc; reflexivity | exact HR'].
- subst f own pre b cap.
  destruct HOc as [(Hc & _) | [(_ & Hf1 & Ho' & Ep' & Eb' & Ec') | (Hc & _)]]; [exfalso; exact (Hf0 Hc) | | exfalso; exact (Hf0 Hc)].
  right. left. split; [exact Hf0|]. split; [exact Hf1|]. split; [exact Ho'|].
  split; [rewrite Ep'; reflexivity|]. split; [exact Eb' | exact Ec'].
- subst f own.
  destruct HOc as [(Hc & _) | [(_ & Hf1 & Ho' & Ep' & _ & _) | (Hc & _)]]; [lia | | lia].
  right. right. split; [exact Hf0|]. split; [lia|]. split; [lia|].
  split; [exists (rest ++ addc); rewrite Ea, Ep', app_nil_r, app_assoc; reflexivity | exact HR].
Qed.

(* the position clause folded likewise *)
Lemma tx_jok_fold : forall len0 cap0 f0 f f1 own0 own own' b0 b b1 cap cap1 (j jq : nat)
  (ks kc add addc pre prec : list Z),
  TxModel.zsum ks = Z.of_nat (length add) ->
  prhtx_out f0 f own0 own b0 cap0 b cap (TxModel.tx_capf len0 cap0 ks) add pre ->
  tx_jok len0 cap0 f0 f ks j ->
  prhtx_out f f1 own own' b cap b1 cap1 (TxModel.tx_capf (len0 + Z.of_nat (length pre)) cap kc) addc prec ->
  tx_jok (len0 + Z.of_nat (length pre)) cap f f1 kc jq ->
  tx_jok len0 cap0 f0 f1 (ks ++ kc) (j + jq).
Proof.
intros len0 cap0 f0 f f1 own0 own own' b0 b b1 cap cap1 j jq ks kc add addc pre prec Hks HO (Hj & HjE & Hj0) HOc
  (Hq & HqE & Hq0).
assert (Elen : length (prhtx_evs len0 cap0 (ks ++ kc)) =
  (length (prhtx_evs len0 cap0 ks) + length (prhtx_evs (len0 + TxModel.zsum ks) (TxModel.tx_capf len0 cap0 ks) kc))%nat)
  by (rewrite prhtx_evs_app, length_app; reflexivity).
unfold tx_jok. rewrite Elen.
destruct HO as [(Hf0 & Hf & Ho & Ep & Ec) | [(Hf0 & Hf & Ho & Ep & Eb & Ec) | (Hf0 & Hf & Ho & (rest & Ea) & HR)]].
- subst f pre cap. rewrite <- Hks in Hq, HqE. specialize (HjE Hf0 eq_refl).
  split; [lia|]. split; [intros _ Hf1; rewrite (HqE eq_refl Hf1); lia | intros Hc; exfalso; exact (Hc Hf0)].
- subst f. specialize (Hj0 Hf0). specialize (Hq0 Hf0).
  split; [lia|]. split; [intros Hc; exfalso; exact (Hf0 Hc) | intros _; lia].
- subst f. assert (Hq00 : jq = 0%nat) by (apply Hq0; lia).
  destruct HOc as [(Hc & _) | [(_ & Hf1 & _) | (Hc & _)]]; [lia | | lia].
  split; [lia|]. split; [intros _ Hc; lia | intros Hc; exfalso; exact (Hc Hf0)].
Qed.

(* the run window of a call of sizes kc, from the text's run premise over all its puts ks ++ kc ++ rest: only when
   the caller is at failed = 0, which is the DONE outcome so far (j = all events of ks) *)
Lemma tx_window : forall sm x os (i0 j : nat) (len0 cap0 f0 f own0 own b0 b cap : Z) (ks add pre kc rest : list Z),
  prhtx_out f0 f own0 own b0 cap0 b cap (TxModel.tx_capf len0 cap0 ks) add pre ->
  tx_jok len0 cap0 f0 f ks j -> TxModel.zsum ks = Z.of_nat (length add) ->
  (f0 = 0 -> prh_run_at sm x os i0 (prhtx_evs len0 cap0 (ks ++ kc ++ rest))) ->
  f = 0 -> prh_run_at sm x os (i0 + j) (prhtx_evs (len0 + Z.of_nat (length pre)) cap kc).
Proof.
intros sm x os i0 j len0 cap0 f0 f own0 own b0 b cap ks add pre kc rest HO (_ & HjE & _) Hks HEV Hf.
destruct HO as [(Hf0 & _ & _ & Ep & Ec) | [(Hf0 & Hff & _) | (_ & Hf1 & _)]]; [| lia | lia].
subst pre cap. rewrite (HjE Hf0 Hf).
specialize (HEV Hf0).
rewrite prhtx_evs_app in HEV. apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in HEV as [_ HEV].
rewrite prhtx_evs_app in HEV. apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in HEV as [HEV _].
rewrite <- Hks. exact HEV.
Qed.

(* tx_put's GROW premise from the caller's window over its one call *)
Lemma tx_put_ev : forall sm x os (i : nat) (len cap n f : Z),
  (f = 0 -> prh_run_at sm x os i (prhtx_evs len cap [n])) ->
  f = 0 -> cap < len + n + 1 ->
  nth_error (PresetRun.hruns sm x os) i =
    Some (if cap =? 0 then PresetReqAt.HMal (2 * (len + n + 1)) else PresetReqAt.HRe cap (2 * (len + n + 1))).
Proof.
intros sm x os i len cap n f HW Hf Hlt. specialize (HW Hf).
cbn [prhtx_evs] in HW. rewrite app_nil_r in HW. rewrite (proj2 (Z.leb_gt _ _) Hlt) in HW.
apply (proj1 (prh_run_at_one sm x os i _)) in HW. unfold prhtx_ev in HW. exact HW.
Qed.

(* tx_put's post (its three arms and its two position conjuncts) as a caller text's outcome and position over [n] *)
Lemma tx_put_res : forall sm x os (i : nat) H0 hist S' (len cap f f1 own own' b b1 cap1 n : Z) (src pre : list Z)
  (R : Prop),
  ((f = 0 /\ f1 = 0 /\ own' = own /\ pre = src /\ cap1 = TxModel.tx_cap1 len cap n) \/
   (f <> 0 /\ f1 = f /\ own' = own /\ pre = [] /\ b1 = b /\ cap1 = cap) \/
   (f = 0 /\ cap < len + n + 1 /\ f1 = 1 /\ own' = 1 /\ pre = [] /\ b1 = b /\ cap1 = cap /\
    prhtx_refused_at S' /\ R)) ->
  (f = 0 -> f1 = 0 -> cap < len + n + 1 ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (Datatypes.S i) H0 hist' S') ->
  (~ (f = 0 /\ f1 = 0 /\ cap < len + n + 1) -> PresetRoomPos.iface_room_pos sm x os i H0 hist S') ->
  prhtx_out f f1 own own' b cap b1 cap1 (TxModel.tx_capf len cap [n]) src pre /\
  exists jq hist', tx_jok len cap f f1 [n] jq /\ PresetRoomPos.iface_room_pos sm x os (i + jq)%nat H0 hist' S'.
Proof.
intros sm x os i H0 hist S' len cap f f1 own own' b b1 cap1 n src pre R HO HG HN.
assert (EL : length (prhtx_evs len cap [n]) = if (len + n + 1 <=? cap)%Z then 0%nat else 1%nat)
  by (cbn [prhtx_evs]; rewrite app_nil_r; destruct (len + n + 1 <=? cap); reflexivity).
destruct HO as [(Hf & Hf1 & Ho & Ep & Ec) | [(Hf & Hf1 & Ho & Ep & Eb & Ec) | (Hf & Hlt & Hf1 & Ho & Ep & Eb & Ec & HR & _)]].
- split; [left; repeat split; first [exact Hf | exact Hf1 | exact Ho | exact Ep | exact Ec]|].
  destruct (Z_le_gt_dec (len + n + 1) cap) as [Hle | Hgt].
  + exists 0%nat, hist. unfold tx_jok. rewrite EL, (proj2 (Z.leb_le _ _) Hle).
    split; [split; [lia | split; intros; lia]|]. rewrite Nat.add_0_r. apply HN. lia.
  + destruct (HG Hf Hf1 ltac:(lia)) as (h' & Hp). exists 1%nat, h'. unfold tx_jok.
    rewrite EL, (proj2 (Z.leb_gt (len + n + 1) cap) ltac:(lia)).
    split; [split; [lia | split; intros; lia]|]. rewrite Nat.add_1_r. exact Hp.
- split; [right; left; repeat split; first [exact Hf | exact Hf1 | exact Ho | exact Ep | exact Eb | exact Ec]|].
  exists 0%nat, hist. unfold tx_jok.
  split; [split; [lia | split; [intros Hc; exfalso; exact (Hf Hc) | intros; lia]]|].
  rewrite Nat.add_0_r. apply HN. intros (Hc & _). exact (Hf Hc).
- split.
  + right. right. split; [exact Hf|]. split; [exact Hf1|]. split; [exact Ho|].
    split; [exists src; rewrite Ep; reflexivity | exists S'; exact HR].
  + exists 0%nat, hist. unfold tx_jok.
    split; [split; [lia | split; [intros _ Hc; lia | intros Hc; exfalso; exact (Hc Hf)]]|].
    rewrite Nat.add_0_r. apply HN. intros (_ & Hc & _). lia.
Qed.
End out.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation TRACE ly W mem t := (prhtx_trace B ly W mem t).

(* ---- the buffer moves of a run of tx_put calls compose ---- *)
Lemma prhtx_grow_refl : forall ly S b cap, prhtx_grow B ly S ly S b cap b cap.
Proof. intros ly S b cap. left. auto. Qed.

Lemma prhtx_grow_trans : forall ly S ly1 S1 ly2 S2 b0 cap0 b1 cap1 b2 cap2,
  prhtx_grow B ly S ly1 S1 b0 cap0 b1 cap1 -> prhtx_grow B ly1 S1 ly2 S2 b1 cap1 b2 cap2 ->
  prhtx_grow B ly S ly2 S2 b0 cap0 b2 cap2.
Proof.
intros ly S ly1 S1 ly2 S2 b0 cap0 b1 cap1 b2 cap2 G1 G2.
destruct G1 as [(-> & -> & E1) | (Hlt1 & bl1 & bl2 & Hsh1 & P1)].
- destruct G2 as [(-> & -> & E2) | (Hlt2 & cl1 & cl2 & Hsh2 & P2)].
  + left. split; [reflexivity|]. split; [reflexivity|]. rewrite E2. exact E1.
  + right. split; [exact Hlt2|]. exists cl1, cl2. rewrite <- E1. split; [exact Hsh2 | exact P2].
- destruct G2 as [(-> & -> & E2) | (Hlt2 & cl1 & cl2 & Hsh2 & P2)].
  + right. split; [exact Hlt1|]. exists bl1, bl2. split; [exact Hsh1|]. rewrite E2. exact P1.
  + right. split; [lia|]. exists bl1, bl2. split; [exact Hsh1|].
    assert (Hc1 : 0 < cap1).
    { destruct Hsh1 as [(Hc0 & _) | (Hc0 & _)]; lia. }
    destruct Hsh2 as [(Hz & _) | (_ & E2)]; [lia|].
    rewrite E2 in P1.
    assert (Pbc : Permutation (bl1 ++ bl2) (cl1 ++ cl2)).
    { apply (Permutation_cons_app_inv cl1 cl2 (a := (b1, cap1))). apply Permutation_sym. exact P1. }
    eapply Permutation_trans; [exact P2|]. apply perm_skip. apply Permutation_sym. exact Pbc.
Qed.

(* ---- the footprint of a tx_put call inside a caller's run: the record (t, t + 28) is the caller's FP; the call's
   buffer (b1, cap1) is the entry buffer (the caller's FP) or a block the run made, not in the entry's list ---- *)
Lemma prhtx_call_fp : forall ly S lyc Sc Hpc Wc memc mdc t b0 cap0 b1 cap1,
  ARx_sep_law segs B ARx -> ARx lyc Sc Hpc Wc memc mdc ->
  prhtx_grow B ly S lyc Sc b0 cap0 b1 cap1 ->
  (0 < cap1 -> In (b1, cap1) (ablocks B lyc Sc)) ->
  forall a, inFP (prhtx_fp t b1 cap1) a ->
  inFP (prhtx_fp t b0 cap0) a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a.
Proof.
intros ly S lyc Sc Hpc Wc memc mdc t b0 cap0 b1 cap1 HSEP HAR G Hin1 a Ha.
unfold prhtx_fp in Ha. apply inFP_cons in Ha. destruct Ha as [Ha | Ha].
{ left. unfold prhtx_fp. apply inFP_cons. left. exact Ha. }
destruct (Z.eqb_spec cap1 0) as [E1 | E1]; [destruct (inFP_nil a Ha)|].
cbn [ablocks_fp map] in Ha. apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [| destruct (inFP_nil a Ha)].
cbn [fst snd] in Ha.
destruct G as [(-> & -> & EB) | (Hlt & bl1 & bl2 & Hsh & P)].
- left. unfold prhtx_fp. apply inFP_cons. right. destruct (Z.eqb_spec cap0 0) as [E0|E0]; [contradiction|].
  cbn [ablocks_fp map]. apply inFP_cons. left. cbn [fst snd]. exact Ha.
- assert (Hc1 : 0 < cap1) by (destruct Hsh as [(Hc0 & _) | (Hc0 & _)]; lia).
  assert (HinC : In (b1, cap1) (ablocks B lyc Sc)) by (apply Hin1; exact Hc1).
  right. exists b1, cap1. split; [exact HinC|]. split; [|exact Ha].
  destruct (HSEP lyc Sc Hpc Wc memc mdc HAR) as (Hpw & _).
  assert (Pm : Permutation (map (fun b => (fst b, req_size (snd b))) (ablocks B lyc Sc) ++
                 map (fun f => (frame_addr lyc (fst f) (snd f), fs_frame_bytes (fst f))) (frames Sc))
               (map (fun b => (fst b, req_size (snd b))) ((b1, cap1) :: bl1 ++ bl2) ++
                 map (fun f => (frame_addr lyc (fst f) (snd f), fs_frame_bytes (fst f))) (frames Sc)))
    by (apply Permutation_app_tail; apply Permutation_map; exact P).
  pose proof (s10_pairwise_perm _ zdisjoint s10_zdisjoint_sym _ _ Pm Hpw) as Hpw2.
  cbn [map app pairwise] in Hpw2. destruct Hpw2 as [Hhd _].
  assert (Hnot : ~ In (b1, cap1) (bl1 ++ bl2)).
  { intros Hold. rewrite Forall_forall in Hhd.
    specialize (Hhd (b1, req_size cap1) ltac:(apply in_or_app; left;
      exact (List.in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ Hold))).
    unfold zdisjoint, req_size in Hhd. cbn [fst snd] in Hhd.
    destruct (Z.eqb_spec cap1 0); cbv iota in Hhd; lia. }
  intros Hold. destruct Hsh as [(Hc0 & Eb) | (Hc0 & Eb)]; rewrite Eb in Hold.
  + exact (Hnot Hold).
  + apply in_app_or in Hold. destruct Hold as [Hold | [Hold | Hold]].
    * apply Hnot. apply in_or_app. left. exact Hold.
    * inversion Hold. lia.
    * apply Hnot. apply in_or_app. right. exact Hold.
Qed.

(* the allocator laws at hl = cf_head *)
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
#[local] Notation AJ := (ajournal_x (SK := SK) segs B prh_pst ARx).
(* the journal over a world relation R (YCbqG.ajournal_xR); AJ is its instance at wle *)
#[local] Notation AJR R := (ajournal_xR (SK := SK) segs B prh_pst ARx R).
(* this unit's crossing relation and its step relation: a run that may re-hide a cf cell *)
#[local] Notation RCF := (YA0nH.wle' segs YGcfRehidePost.RZ_cf).
#[local] Notation SRRCF := (YA0nH.SRr' segs YGcfRehidePost.RZ_cf).

(* ---- THE PROGRAM-CALL RULE IN THE CALLER WINDOW for a callee whose #102 text ends in ONE fpostW (no abort arm):
   S10TxKit.v's s10_call_orW (from YCbqGcall.v aj_call_x, c-omx-alloc) less its abort arm. A callee called at sp0 + o
   (o <= 0, the caller's frame below its entry sp0) with the window dw - o ---- *)
Lemma s10_call_W : forall W E ss ms STK dw sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) spw raw ch1
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJ (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> 0 <= dw -> dw mod 16 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr segs W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (fpostW B ARx SK STK1 (dw - o) FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  fp_sub_x B (STK + dw) (sp0 + dw) FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg ms mdc)
   (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
      c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
      AJ (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
      AJ (STK1 + (dw - o)) (sp0 + dw) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
      (forall a, sp0 + o <= a < sp0 + dw -> ~ inFP FP1 a ->
         aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
      aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W E ss ms STK dw sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o spw raw ch1 Q
HS Hrv HJ Hsp HE2 Hspw Hal Hneg Hstk1 Hbud Hdw0 Hdw16 Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _).
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
assert (Hbase : spZ (ms_regs ms) + (dw - o) = sp0 + dw) by zlia.
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv).
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_x_at segs B prh_pst ARx (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md own lyc Sc Hpc W
(ms_mem ms) mdc k (ms_regs ms) STK1 (o - dw) ch1); try eassumption.
- zlia.
- rewrite Zminus_mod, Hal, Hdw16. reflexivity.
- zlia.
- zlia.
- rewrite Hra. exact Hraw.
- unfold raZ. rewrite Hra. exact Hra4.
- rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ HN. unfold fpostW in HN.
destruct HN as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HW1 & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|]. rewrite Hbase in HJ1.
split; [| split; [exact HJ1 | split; [| split; [exact HP | exact HQ]]]].
- change own with ([] ++ own).
  eapply (ajournal_x_sub segs B prh_pst ARx LAWS pa_segs_low); [exact HJ | exact HJ1 | zlia | zlia | exact HF].
- intros a Ha Hn. apply HW1; [rewrite Hsp'; zlia | exact Hn].
Qed.

(* a callee with an m-form post (fpostWm = fpostW .. (fQmn mem Q)): the caller gets fQmn of the CALL memory *)
Lemma s10_call_Wm : forall W E ss ms STK dw sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) spw raw ch1
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJ (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> 0 <= dw -> dw mod 16 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr segs W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (fpostWm B ARx SK STK1 (dw - o) FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  fp_sub_x B (STK + dw) (sp0 + dw) FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg ms mdc)
   (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
      c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
      AJ (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
      AJ (STK1 + (dw - o)) (sp0 + dw) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
      (forall a, sp0 + o <= a < sp0 + dw -> ~ inFP FP1 a ->
         aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
      aregs_preserved (ms_regs ms) regs2 /\ fQmn (ms_mem ms) Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W E ss ms STK dw sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o spw raw ch1 Q.
exact (s10_call_W W E ss ms STK dw sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o spw raw ch1
  (fQmn (ms_mem ms) Q)).
Qed.

(* the window TAIL-CALL rule: a callee entered by `j` with the caller's frame popped (sp = sp0, ra and every
   callee-saved register the entry's), at the caller's own window dw; its post becomes the caller's *)
Lemma s10_tail_WR : forall (R : world segs -> world segs -> Prop), (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ms STK dw sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 ch1
  (regs0 : bvmap 5 word)
  (Q Q1 : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJR R (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md [] lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ regs0 = sp0 -> spZ (ms_regs ms) = sp0 ->
  0 <= STK1 -> STK1 <= STK -> 0 <= dw -> dw mod 16 = 0 ->
  aregs_preserved regs0 (ms_regs ms) -> getr (ms_regs ms) 1 = getr regs0 1 ->
  YK0s.ret_ok (getr regs0 1) -> 4096 <= raZ regs0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) sp0 (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   YA0nH.SRrG segs R W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (fpostWR B ARx SK R STK1 dw FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q1)) ->
  fp_sub_x B (STK + dw) (sp0 + dw) FP FP1 ly S [] lyc Sc ->
  (forall a, sp0 <= a < sp0 + dw -> inFP FP1 a -> inFP FP a) ->
  (forall a, sp0 <= a < sp0 + dw -> ~ inFP FP a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W0) mem a) ->
  (forall ly' S' Hp' W' regs' mem' md', Q1 ly' S' Hp' W' regs' mem' md' -> Q ly' S' Hp' W' regs' mem' md') ->
  YA0nH.SRrG segs R W (mkCfg ms mdc) (fpostWR B ARx SK R STK dw FP regs0 ly S Hp W0 mem md Q).
Proof.
intros R Rt W E ss ms STK dw sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 ch1 regs0 Q Q1
HS Hrv HJ Hsp0 Hspt Hstk1 Hbud Hdw0 Hdw16 Hpr Hra Hraok Hra4 Hgp Htp Hch Hcallee HF HNS HWIN HQQ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _).
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv).
eapply (YA0nH.SRrG_mono segs R).
{ apply Hcallee. eapply (afn_pre_x_atR segs B prh_pst ARx R (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md [] lyc Sc Hpc W
(ms_mem ms) mdc k (ms_regs ms) STK1 (- dw) ch1); try eassumption.
- zlia.
- apply Z_mod_zero_opp_full. exact Hdw16.
- zlia.
- zlia.
- rewrite Hra. exact Hraok.
- unfold raZ in *. rewrite Hra. exact Hra4.
- rewrite Hspt. exact Hch. }
cbv beta. intros W2 c2 _ HN. unfold fpostWR in HN |- *.
destruct HN as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HW1 & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, (k + k1). rewrite Hra. split; [reflexivity|].
rewrite Hspt in HJ1. rewrite Hsp0.
split; [change (@nil (Z * Z)) with ((@nil (Z * Z)) ++ []);
  eapply (ajournal_x_subR segs B prh_pst ARx LAWS pa_segs_low R Rt); [exact HJ | exact HJ1 | zlia | zlia | exact HF]|].
split; [| split; [| exact (HQQ _ _ _ _ _ _ _ HQ)]].
- intros a Ha Hn. rewrite (HW1 a ltac:(rewrite Hspt; zlia) ltac:(intros H1; exact (Hn (HNS a ltac:(zlia) H1)))).
  apply HWIN; [zlia | exact Hn].
- intros r Hr. rewrite (HP r Hr). exact (Hpr r Hr).
Qed.
(* the row's primed statement: this call crosses a free, so its step relation is SRr' and both posts take their R
   form with the journal's conjunct 4 at wle' *)
Lemma s10_tail_W : forall W E ss ms STK dw sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 ch1
  (regs0 : bvmap 5 word)
  (Q Q1 : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJR RCF (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md [] lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ regs0 = sp0 -> spZ (ms_regs ms) = sp0 ->
  0 <= STK1 -> STK1 <= STK -> 0 <= dw -> dw mod 16 = 0 ->
  aregs_preserved regs0 (ms_regs ms) -> getr (ms_regs ms) 1 = getr regs0 1 ->
  YK0s.ret_ok (getr regs0 1) -> 4096 <= raZ regs0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) sp0 (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRRCF W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (fpostWR B ARx SK RCF STK1 dw FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q1)) ->
  fp_sub_x B (STK + dw) (sp0 + dw) FP FP1 ly S [] lyc Sc ->
  (forall a, sp0 <= a < sp0 + dw -> inFP FP1 a -> inFP FP a) ->
  (forall a, sp0 <= a < sp0 + dw -> ~ inFP FP a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W0) mem a) ->
  (forall ly' S' Hp' W' regs' mem' md', Q1 ly' S' Hp' W' regs' mem' md' -> Q ly' S' Hp' W' regs' mem' md') ->
  SRRCF W (mkCfg ms mdc) (fpostWR B ARx SK RCF STK dw FP regs0 ly S Hp W0 mem md Q).
Proof. exact (s10_tail_WR RCF (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)). Qed.

(* a tail call to a callee with an m-form post, from a caller whose own m-form post is at its entry memory mem *)
Lemma s10_tail_WmR : forall (R : world segs -> world segs -> Prop), (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ms STK dw sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 ch1
  (regs0 : bvmap 5 word)
  (Q Q1 : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJR R (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md [] lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ regs0 = sp0 -> spZ (ms_regs ms) = sp0 ->
  0 <= STK1 -> STK1 <= STK -> 0 <= dw -> dw mod 16 = 0 ->
  aregs_preserved regs0 (ms_regs ms) -> getr (ms_regs ms) 1 = getr regs0 1 ->
  YK0s.ret_ok (getr regs0 1) -> 4096 <= raZ regs0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) sp0 (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   YA0nH.SRrG segs R W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (fpostWmR B ARx SK R STK1 dw FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q1)) ->
  fp_sub_x B (STK + dw) (sp0 + dw) FP FP1 ly S [] lyc Sc ->
  (forall a, sp0 <= a < sp0 + dw -> inFP FP1 a -> inFP FP a) ->
  (forall a, sp0 <= a < sp0 + dw -> ~ inFP FP a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W0) mem a) ->
  (forall ly' S' Hp' W' regs' mem' md', Q1 ly' S' Hp' W' regs' mem' md' -> Q ly' S' Hp' W' regs' mem' md') ->
  (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs (ms_mem ms)) ->
  YA0nH.SRrG segs R W (mkCfg ms mdc) (fpostWmR B ARx SK R STK dw FP regs0 ly S Hp W0 mem md Q).
Proof.
intros R Rt W E ss ms STK dw sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 ch1 regs0 Q Q1
  HS Hrv HJ Hsp0 Hspt Hstk1 Hbud Hdw0 Hdw16 Hpr Hra Hraok Hra4 Hgp Htp Hch Hcallee HF HNS HWIN HQQ HMN.
exact (s10_tail_WR R Rt W E ss ms STK dw sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 ch1 regs0
  (fQmn mem Q) (fQmn (ms_mem ms) Q1) HS Hrv HJ Hsp0 Hspt Hstk1 Hbud Hdw0 Hdw16 Hpr Hra Hraok Hra4 Hgp Htp
  Hch Hcallee HF HNS HWIN
  (fun ly' S' Hp' W' regs' mem' md' H => conj (HQQ _ _ _ _ _ _ _ (proj1 H)) (fun Hm => proj2 H (HMN Hm)))).
Qed.
Lemma s10_tail_Wm : forall W E ss ms STK dw sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 ch1
  (regs0 : bvmap 5 word)
  (Q Q1 : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJR RCF (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md [] lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ regs0 = sp0 -> spZ (ms_regs ms) = sp0 ->
  0 <= STK1 -> STK1 <= STK -> 0 <= dw -> dw mod 16 = 0 ->
  aregs_preserved regs0 (ms_regs ms) -> getr (ms_regs ms) 1 = getr regs0 1 ->
  YK0s.ret_ok (getr regs0 1) -> 4096 <= raZ regs0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) sp0 (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRRCF W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (fpostWmR B ARx SK RCF STK1 dw FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q1)) ->
  fp_sub_x B (STK + dw) (sp0 + dw) FP FP1 ly S [] lyc Sc ->
  (forall a, sp0 <= a < sp0 + dw -> inFP FP1 a -> inFP FP a) ->
  (forall a, sp0 <= a < sp0 + dw -> ~ inFP FP a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W0) mem a) ->
  (forall ly' S' Hp' W' regs' mem' md', Q1 ly' S' Hp' W' regs' mem' md' -> Q ly' S' Hp' W' regs' mem' md') ->
  (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs (ms_mem ms)) ->
  SRRCF W (mkCfg ms mdc) (fpostWmR B ARx SK RCF STK dw FP regs0 ly S Hp W0 mem md Q).
Proof. exact (s10_tail_WmR RCF (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)). Qed.

(* ======== memory agreement off a set ======== *)
Definition s10_agree (m m' : word -> option byte) (P : Z -> Prop) : Prop :=
  forall x : word, P (bv_unsigned x) -> m' x = m x.

Lemma s10_mbyte : forall m m' P a, s10_agree m m' P -> 0 <= a < 2 ^ 64 -> P a ->
  mbyte segs m' a = mbyte segs m a.
Proof. intros m m' P a H Ha HP. unfold mbyte. rewrite H; [reflexivity|]. rewrite unsigned_lit_small by lia. exact HP. Qed.

Lemma s10_val_mem : forall m m' P a n v, s10_agree m m' P ->
  (forall k, (k < n)%nat -> 0 <= a + Z.of_nat k < 2 ^ 64 /\ P (a + Z.of_nat k)) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof.
intros m m' P a n v H HA HV k Hk. destruct (HA k Hk) as [R HP].
rewrite (s10_mbyte m m' P _ H R HP). exact (HV k Hk).
Qed.

Lemma s10_garr8 : forall m m' P a l, s10_agree m m' P ->
  (forall j, (j < length l)%nat -> 0 <= a + Z.of_nat j < 2 ^ 64 /\ P (a + Z.of_nat j)) ->
  garr8 segs m a l -> garr8 segs m' a l.
Proof.
intros m m' P a l H HA HG j Hj. destruct (HG j Hj) as [V R]. split; [|exact R].
apply (s10_val_mem m m' P _ 1 _ H); [|exact V].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r. exact (HA j Hj).
Qed.

Lemma s10_writable : forall m m' P a, s10_agree m m' P -> 0 <= a < 2 ^ 64 -> P a ->
  writable_at segs m a -> writable_at segs m' a.
Proof.
intros m m' P a H Ha HP Hw. unfold writable_at, wview in *. rewrite H; [exact Hw|].
rewrite unsigned_lit_small by lia. exact HP.
Qed.

Lemma s10_aview : forall (W : world segs) mem mem' P a, s10_agree (rdW W mem) (rdW W mem') P ->
  0 <= a < 2 ^ 64 -> P a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a.
Proof. intros W mem mem' P a H Ha HP. unfold aview. rewrite (s10_mbyte _ _ P a H Ha HP). reflexivity. Qed.

(* one read-back byte *)
Lemma s10_val1_of_aview : forall (H : word -> bool) mem a v, aview segs H mem a = Some v ->
  val_mem segs (mrestrict H mem) a 1 v /\ 0 <= v < 256.
Proof.
intros H mem a v E. unfold aview in E.
destruct (mbyte segs (mrestrict H mem) a) as [bb|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as <-. pose proof (bv_unsigned_in_range 8 bb) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|exact Hr].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb.
f_equal. rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by exact Hr. reflexivity.
Qed.

(* ---- the frame chain the unwinder reads from the record: a present region gives one ---- *)
Lemma s10_rdword_present : forall (W : world segs) mem a,
  (forall x, a <= x < a + 8 -> aview segs (w_H W) mem x <> None) ->
  exists v, rdword (aview segs (w_H W) mem) a = Some v /\ 0 <= v.
Proof.
intros W mem a H. unfold rdword.
destruct (aview segs (w_H W) mem a) as [v0|] eqn:E0; [|destruct (H a ltac:(lia) E0)].
destruct (aview segs (w_H W) mem (a + 1)) as [v1|] eqn:E1; [|destruct (H (a + 1) ltac:(lia) E1)].
destruct (aview segs (w_H W) mem (a + 2)) as [v2|] eqn:E2; [|destruct (H (a + 2) ltac:(lia) E2)].
destruct (aview segs (w_H W) mem (a + 3)) as [v3|] eqn:E3; [|destruct (H (a + 3) ltac:(lia) E3)].
destruct (aview segs (w_H W) mem (a + 4)) as [v4|] eqn:E4; [|destruct (H (a + 4) ltac:(lia) E4)].
destruct (aview segs (w_H W) mem (a + 5)) as [v5|] eqn:E5; [|destruct (H (a + 5) ltac:(lia) E5)].
destruct (aview segs (w_H W) mem (a + 6)) as [v6|] eqn:E6; [|destruct (H (a + 6) ltac:(lia) E6)].
destruct (aview segs (w_H W) mem (a + 7)) as [v7|] eqn:E7; [|destruct (H (a + 7) ltac:(lia) E7)].
eexists. split; [reflexivity|].
pose proof (proj2 (s10_val1_of_aview (w_H W) mem _ _ E0)).
pose proof (proj2 (s10_val1_of_aview (w_H W) mem _ _ E1)).
pose proof (proj2 (s10_val1_of_aview (w_H W) mem _ _ E2)).
pose proof (proj2 (s10_val1_of_aview (w_H W) mem _ _ E3)).
pose proof (proj2 (s10_val1_of_aview (w_H W) mem _ _ E4)).
pose proof (proj2 (s10_val1_of_aview (w_H W) mem _ _ E5)).
pose proof (proj2 (s10_val1_of_aview (w_H W) mem _ _ E6)).
pose proof (proj2 (s10_val1_of_aview (w_H W) mem _ _ E7)).
lia.
Qed.

Lemma s10_fpchain_fuel : forall (n : nat) (W : world segs) mem t0 t top,
  (forall a, t0 - 16 <= a < top -> aview segs (w_H W) mem a <> None) ->
  t0 <= t -> t mod 8 = 0 -> t < top - 16 -> (Z.to_nat (top - t) <= n)%nat ->
  exists ch, fpchain (rdword (aview segs (w_H W) mem)) t top ch /\ Forall (fun r => t0 <= fst (fst r)) ch.
Proof.
induction n as [|n IH]; intros W mem t0 t top HP H0 H8 Ht Hn; [exfalso; lia|].
destruct (s10_rdword_present W mem (t - 8) ltac:(intros x Hx; apply HP; lia)) as (ra & Era & Hra0).
destruct (Z_lt_le_dec ra 4096) as [Hlt|Hge].
{ exists []. split; [cbn [fpchain]; exists ra; split; [exact Era | lia] | apply Forall_nil]. }
destruct (s10_rdword_present W mem (t - 16) ltac:(intros x Hx; apply HP; lia)) as (nfp & Enfp & Hnfp0).
destruct (bad_next t top nfp) eqn:Ebad.
{ exists [(t, ra, nfp)]. split; [|constructor; [cbn [fst]; lia | apply Forall_nil]].
  cbn [fpchain]. split; [reflexivity|]. split; [exact H8|]. split; [exact Era|]. split; [exact Enfp|].
  split; [lia|]. rewrite Ebad. reflexivity. }
unfold bad_next in Ebad. apply orb_false_iff in Ebad as [Ebad Hm8]. apply orb_false_iff in Ebad as [Hle Htop].
apply Z.leb_gt in Hle. apply Z.leb_gt in Htop. apply negb_false_iff, Z.eqb_eq in Hm8.
destruct (IH W mem t0 nfp top HP ltac:(lia) Hm8 ltac:(lia) ltac:(lia)) as (ch & Hch & HF).
exists ((t, ra, nfp) :: ch). split; [|constructor; [cbn [fst]; lia | exact HF]].
cbn [fpchain]. split; [reflexivity|]. split; [exact H8|]. split; [exact Era|]. split; [exact Enfp|].
split; [lia|]. unfold bad_next. rewrite (proj2 (Z.leb_gt _ _) Hle), (proj2 (Z.leb_gt _ _) Htop).
rewrite (proj2 (Z.eqb_eq _ _) Hm8). cbn [orb negb]. exact Hch.
Qed.

(* achain at a call made with the record pointer in s0 (tx_value / tx_string / tx_line all set s0 := t) *)
Lemma s10_achain_at : forall ly (W : world segs) mem sp t,
  (forall a, t - 16 <= a < ly_top ly -> aview segs (w_H W) mem a <> None) ->
  t mod 8 = 0 -> sp + 16 <= t -> t < ly_top ly - 16 -> 0 <= t ->
  exists ch, achain ly (aview segs (w_H W) mem) sp t ch.
Proof.
intros ly W mem sp t HP H8 Hsp Htop H0.
destruct (s10_fpchain_fuel (Z.to_nat (ly_top ly - t)) W mem t t (ly_top ly) HP ltac:(lia) H8 Htop ltac:(lia))
  as (ch & Hch & HF).
exists ch. right. split; [exact Hsp|]. split; [exact Htop|]. split; [exact H8|]. split; [exact Hch|].
revert HF. apply Forall_impl. intros r Hr. lia.
Qed.

(* the record's footprint (its 28 accessed bytes) and the buffer's *)
Lemma s10_fp_cases : forall t b cap a, inFP (prhtx_fp t b cap) a ->
  (t <= a < t + 28) \/ (cap <> 0 /\ b <= a < b + req_size cap).
Proof.
intros t b cap a (r & Hr & Ha). unfold prhtx_fp in Hr. destruct Hr as [<- | Hr]; [left; exact Ha|].
destruct (Z.eqb_spec cap 0) as [E|E]; [destruct Hr|].
cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha. right. split; [exact E | exact Ha].
Qed.

(* ---- the pieces of a text state, kept off a write set ---- *)
Lemma s10_rec_keep : forall W mem mem' P t b len cap f,
  s10_agree (rdW W mem) (rdW W mem') P -> 0 <= t -> t + 28 <= 2 ^ 47 -> (forall a, t <= a < t + 28 -> P a) ->
  prhtx_rec W mem t b len cap f -> prhtx_rec W mem' t b len cap f.
Proof.
intros W mem mem' P t b len cap f H H0 H1 HP (R1 & R2 & R3 & Rf & V1 & V2 & V3 & V4).
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact Rf|].
split; [|split; [|split]]; (eapply s10_val_mem; [exact H| |eassumption]); intros k Hk; split; try lia; apply HP; lia.
Qed.

Lemma s10_place_keep : forall ly S W regs mem mem' P dw t,
  s10_agree (rdW W mem) (rdW W mem') P -> 0 <= t -> t + 28 <= 2 ^ 47 ->
  (forall a, t <= a < t + 28 -> P a) -> (forall a, 0 <= a < 2 ^ 46 -> P a) ->
  prhtx_place ly S W regs mem dw t -> prhtx_place ly S W regs mem' dw t.
Proof.
intros ly S W regs mem mem' P dw t H H0 H1 HPt HPs (H8 & Hlo & Hhi & Hw & Hra).
split; [exact H8|]. split; [exact Hlo|]. split; [exact Hhi|]. split.
- intros a Ha. apply (s10_writable _ _ P a H); [lia | apply HPt; lia | exact (Hw a Ha)].
- eapply range_addressable_agree; [|exact Hra]. intros x Hx.
  pose proof (s10_shadow_low x ltac:(lia)). apply (s10_aview W mem mem' P); [exact H | lia | apply HPs; lia].
Qed.

Lemma s10_inv_keep : forall Lam ly S W mem mem' P b len cap txt,
  s10_agree (rdW W mem) (rdW W mem') P -> (forall a, 0 <= a < YM05.alloc_ceiling -> P a) ->
  prhtx_inv B Lam ly S W mem b len cap txt -> prhtx_inv B Lam ly S W mem' b len cap txt.
Proof.
intros Lam ly S W mem mem' P b len cap txt H HP
  (Hl & [Hz | (Hc & Hlc & Hin & Hby & H4096 & Hceil & Hamr & Hw & Hra & Hhull & Hlam)]).
- split; [exact Hl | left; exact Hz].
- pose proof asan_consts as (C1 & _).
  split; [exact Hl|]. right. split; [exact Hc|]. split; [exact Hlc|]. split; [exact Hin|]. split.
  + unfold bytes_at in *. apply (s10_garr8 _ _ P b _ H); [|exact Hby].
    intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. split; [lia | apply HP; lia].
  + split; [exact H4096|]. split; [exact Hceil|]. split; [exact Hamr|]. split; [|split; [|split; [|exact Hlam]]].
    * intros a Ha. apply (s10_writable _ _ P a H); [lia | apply HP; lia | exact (Hw a Ha)].
    * eapply range_addressable_agree; [|exact Hra]. intros x Hx. pose proof (s10_shadow_low x ltac:(lia)).
      apply (s10_aview W mem mem' P); [exact H | lia | apply HP; lia].
    * intros s Hs. pose proof (s10_hull_low b cap s ltac:(lia) ltac:(lia) ltac:(lia) Hs).
      rewrite (s10_aview W mem mem' P s H ltac:(lia) ltac:(apply HP; lia)). exact (Hhull s Hs).
Qed.

(* the record's own 28 bytes are present (its four fields are read back) *)
Lemma s10_rec_present : forall W mem t b len cap f, prhtx_rec W mem t b len cap f ->
  forall a, t <= a < t + 28 -> aview segs (w_H W) mem a <> None.
Proof.
intros W mem t b len cap f (_ & _ & _ & _ & V1 & V2 & V3 & V4) a Ha. unfold aview.
assert (E : exists q w k, mbyte segs (rdW W mem) a = Some (Z_to_bv 8 (le_byte q w k))).
{ destruct (Z_lt_le_dec a (t + 8)) as [H1|H1].
  - exists b, 8%nat, (Z.to_nat (a - t)). specialize (V1 (Z.to_nat (a - t)) ltac:(lia)).
    replace (t + Z.of_nat (Z.to_nat (a - t))) with a in V1 by lia. exact V1.
  - destruct (Z_lt_le_dec a (t + 16)) as [H2|H2].
    + exists len, 8%nat, (Z.to_nat (a - (t + 8))). specialize (V2 (Z.to_nat (a - (t + 8))) ltac:(lia)).
      replace (t + 8 + Z.of_nat (Z.to_nat (a - (t + 8)))) with a in V2 by lia. exact V2.
    + destruct (Z_lt_le_dec a (t + 24)) as [H3|H3].
      * exists cap, 8%nat, (Z.to_nat (a - (t + 16))). specialize (V3 (Z.to_nat (a - (t + 16))) ltac:(lia)).
        replace (t + 16 + Z.of_nat (Z.to_nat (a - (t + 16)))) with a in V3 by lia. exact V3.
      * exists f, 4%nat, (Z.to_nat (a - (t + 24))). specialize (V4 (Z.to_nat (a - (t + 24))) ltac:(lia)).
        replace (t + 24 + Z.of_nat (Z.to_nat (a - (t + 24)))) with a in V4 by lia. exact V4. }
destruct E as (q & w & k & E). rewrite E. discriminate.
Qed.

Lemma s10_trace_keep : forall ly W mem ly' W' mem' t,
  TRACE ly W mem t -> ly_top ly' = ly_top ly ->
  (YM05.alloc_ceiling <= t -> forall a, t - 16 <= a < ly_top ly -> ~ (t <= a < t + 28) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  (YM05.alloc_ceiling <= t -> forall a, t <= a < t + 28 -> aview segs (w_H W') mem' a <> None) ->
  TRACE ly' W' mem' t.
Proof.
intros ly W mem ly' W' mem' t U3 Etop HK HP.
intros Hc. destruct (U3 Hc) as [UP UC]. rewrite Etop. split.
- intros a Ha. destruct (Z_le_gt_dec t a) as [H1|H1]; [|rewrite (HK Hc a Ha ltac:(lia)); apply UP; lia].
  destruct (Z_lt_le_dec a (t + 28)) as [H2|H2]; [apply HP; lia | rewrite (HK Hc a Ha ltac:(lia)); apply UP; lia].
- intros rd ch Hrd Hch. apply (UC rd ch); [|exact Hch].
  intros a Ha Hn. rewrite (Hrd a Ha Hn). exact (HK Hc a Ha Hn).
Qed.

(* image fact: alloc.c's statics lie in the image (image B: S1ImgB.v pst_in_img_B) *)
Hypothesis HPST : forall a, Exists (in_zr a) prh_pst -> in_img segs a.

Lemma s10_ledger_keep : forall ly S Hp W mem mem' md P Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md -> s10_agree (rdW W mem) (rdW W mem') P ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> P a) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem mem' md P Lam peak cnt fail ran most own HAR H HP (HG & Hnd & HF & Hperm).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (Hst : forall a, Exists (in_zr a) prh_pst -> 0 <= a < 2 ^ 64 /\ P a).
{ intros a Ha. pose proof (pa_segs_low a (HPST a Ha)). split; [lia | apply HP; lia]. }
split; [|split; [exact Hnd | split; [|exact Hperm]]].
- unfold prh_glob, prh_most, prh_own in *.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & GR).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ G6r) (conj (conj _ G7r) GR)))))));
  (eapply s10_val_mem; [exact H| |eassumption]); intros k Hk; apply Hst; unfold prh_pst;
  repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
- rewrite Forall_forall in HF |- *. intros [a k] Hin. specialize (HF _ Hin). cbn [fst snd] in *.
  unfold prh_hblock in *. destruct HF as (Hk & Hab & Hhp & Ha16 & Hv).
  split; [exact Hk|]. split; [exact Hab|]. split; [exact Hhp|]. split; [exact Ha16|].
  destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (Hm16 & H4096 & Hc & _).
  pose proof alloc_ceiling_value as (_ & Hc4096).
  apply Z.mod_divide in Hm16 as [q Hq]; [|lia]. apply Z.mod_divide in Hc4096 as [r Hr]; [|lia].
  pose proof (@cf_head_nonneg cp) as Hh0.
  assert (Hrq : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  eapply s10_val_mem; [exact H| |exact Hv]. intros i Hi. split; [lia | apply HP; lia].
Qed.

(* ---- the place of the record: down to a callee, up from its post (the record is on the caller's REAL stack) ---- *)
Lemma s10_place_down : forall ly S W regs regs' mem dw dw' t,
  prhtx_place ly S W regs mem dw t -> spZ regs' <= spZ regs -> spZ regs + dw <= spZ regs' + dw' ->
  prhtx_place ly S W regs' mem dw' t.
Proof.
intros ly S W regs regs' mem dw dw' t (H8 & Hlo & Hhi & Hw & Hra) H1 H2.
split; [exact H8|]. split; [lia|]. split; [lia | split; [exact Hw | exact Hra]].
Qed.

Lemma s10_place_up : forall ly S W mem ly' S' W' regs regs' mem' dw dw' t,
  prhtx_place ly S W regs mem dw t -> prhtx_place ly' S' W' regs' mem' dw' t ->
  prhtx_place ly' S' W' regs mem' dw t.
Proof.
intros ly S W mem ly' S' W' regs regs' mem' dw dw' t (H8 & Hlo & Hhi & _ & _) (_ & _ & _ & Hw' & Hra').
split; [exact H8|]. split; [exact Hlo|]. split; [exact Hhi | split; [exact Hw' | exact Hra']].
Qed.

(* ======== THE TEXT STATE (see the header): relative to the caller's entry (regs0, its window dw0, its entry state
   ly0 S0 Hp0, the record t, the entry buffer b0 / len0 / cap0, failed f0, txt0, the ledger's statics and own0), after
   puts of sizes ks that would append add: the buffer (b, cap), failed f, own, and pre ACTUALLY appended ======== *)
Definition tx_state (Lam : list (Z * Z)) (regs0 : bvmap 5 word) (dw0 : Z) (ly0 : alayout) (S0 : astate)
  (Hp0 : list Z) (t b0 len0 cap0 f0 : Z) (txt0 : list Z) (peak cnt fail ran most own0 : Z)
  (b cap f own : Z) (ks add pre : list Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) : Prop :=
  0 <= t /\ t + 28 <= 2 ^ 47 /\
  TxModel.zsum ks = Z.of_nat (length add) /\
  prhtx_post B Lam regs0 dw0 ly0 S0 Hp0 ly S Hp W mem t b0 cap0 b (len0 + Z.of_nat (length pre)) cap f (txt0 ++ pre) /\
  prhtx_out f0 f own0 own b0 cap0 b cap (TxModel.tx_capf len0 cap0 ks) add pre /\
  TRACE ly W mem t /\
  room_live_cf S /\
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own.

(* its position: the text's own position clause over ks (tx_jok) at the current allocator state *)
Definition tx_pos (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i0 : nat) (rp_H0 : list Z) (len0 cap0 f0 f : Z) (ks : list Z) (S : astate) : Prop :=
  exists j hist, tx_jok len0 cap0 f0 f ks j /\ PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i0 + j)%nat rp_H0 hist S.

(* at the caller's entry: nothing appended; the outcome DONE (f0 = 0) or FAILED (f0 = 1) *)
Lemma tx_state_init : forall Lam regs0 dw0 ly0 S0 Hp0 W0 mem0 md0 ch STK t b0 len0 cap0 f0 txt0
  peak cnt fail ran most own0,
  afn_pre_x segs B ARx STK ly0 S0 Hp0 W0 regs0 mem0 md0 ch -> fwin ly0 W0 regs0 mem0 dw0 ->
  prhtx_place ly0 S0 W0 regs0 mem0 dw0 t -> TRACE ly0 W0 mem0 t ->
  prhtx_rec W0 mem0 t b0 len0 cap0 f0 -> prhtx_inv B Lam ly0 S0 W0 mem0 b0 len0 cap0 txt0 ->
  room_live_cf S0 ->
  prh_ledger B ly0 S0 Hp0 W0 mem0 Lam peak cnt fail ran most own0 ->
  tx_state Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b0 cap0 f0 own0 [] [] []
    ly0 S0 Hp0 W0 mem0.
Proof.
intros Lam regs0 dw0 ly0 S0 Hp0 W0 mem0 md0 ch STK t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0
  HPRE HWIN Hpl Htr Hrec Hinv Hroom Hled.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop).
pose proof HWIN as (Hd0 & _ & Hdtop & _).
pose proof alloc_ceiling_lt as Hc47. pose proof asan_consts as (C1 & _).
pose proof Hpl as (_ & Hplo & Hphi & _ & _).
unfold tx_state. cbn [length Z.of_nat TxModel.zsum]. rewrite Z.add_0_r, app_nil_r.
split; [lia|]. split; [lia|].
split; [reflexivity|]. split; [|split; [exact (tx_out_nil len0 cap0 f0 own0 b0) |
  split; [exact Htr | split; [exact Hroom | exact Hled]]]].
split; [exact Hrec|]. split; [exact Hinv|]. split; [exact Hpl|]. split; [reflexivity|].
split; [apply prhtx_grow_refl | lia].
Qed.

Lemma tx_pos_init : forall rp_sm rp_x rp_os rp_i0 rp_H0 rp_hist0 len0 cap0 f0 S0,
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i0 rp_H0 rp_hist0 S0 ->
  tx_pos rp_sm rp_x rp_os rp_i0 rp_H0 len0 cap0 f0 f0 [] S0.
Proof.
intros rp_sm rp_x rp_os rp_i0 rp_H0 rp_hist0 len0 cap0 f0 S0 Hpos.
exists 0%nat, rp_hist0. split; [apply tx_jok_nil | rewrite Nat.add_0_r; exact Hpos].
Qed.

(* across the caller's own straight-line code: the memory changed only in [lo, hi), inside its frame below its entry
   sp and at or above alloc_ceiling *)
Lemma tx_state_keep : forall Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0
  b cap f own ks add pre ly S Hp W mem mem' md lo hi,
  tx_state Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b cap f own ks add pre
    ly S Hp W mem ->
  ARx ly S Hp W mem md -> ly_top ly <= 2 ^ 47 ->
  YM05.alloc_ceiling <= lo -> hi <= spZ regs0 ->
  (forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x) -> rdW W mem' x = rdW W mem x) ->
  tx_state Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b cap f own ks add pre
    ly S Hp W mem'.
Proof.
intros Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b cap f own ks add pre
  ly S Hp W mem mem' md lo hi
  (Ht0 & Ht47 & Hks & (Hrec & Hinv & Hpl & HHp & Hgr & Hbb) & HO & Htr & Hroom & Hled) HAR Htop47 Hlo Hhi Hag.
set (P := fun a => a < lo \/ hi <= a).
assert (HA : s10_agree (rdW W mem) (rdW W mem') P) by exact Hag.
pose proof asan_consts as (C1 & _).
pose proof alloc_ceiling_lt as Hc47.
assert (HPlow : forall a, 0 <= a < YM05.alloc_ceiling -> P a) by (intros a Ha; left; lia).
assert (HPs : forall a, 0 <= a < 2 ^ 46 -> P a) by (intros a Ha; left; lia).
pose proof Hpl as (_ & Hplo & Hphi & _ & _).
assert (HPt : forall a, t <= a < t + 28 -> P a) by (intros a Ha; right; lia).
split; [exact Ht0|]. split; [exact Ht47|]. split; [exact Hks|].
split; [|split; [exact HO | split; [|split; [exact Hroom|]]]].
- split; [exact (s10_rec_keep W mem mem' P t _ _ _ _ HA Ht0 Ht47 HPt Hrec)|].
  split; [exact (s10_inv_keep Lam ly S W mem mem' P _ _ _ _ HA HPlow Hinv)|].
  split; [exact (s10_place_keep ly S W regs0 mem mem' P dw0 t HA Ht0 Ht47 HPt HPs Hpl)|].
  split; [exact HHp|]. split; [exact Hgr | exact Hbb].
- apply (s10_trace_keep ly W mem ly W mem' t Htr eq_refl).
  + intros Hc a Ha Hn. apply (s10_aview W mem mem' P a HA); [lia | right; lia].
  + intros Hc a Ha. rewrite (s10_aview W mem mem' P a HA ltac:(lia) ltac:(apply HPt; lia)).
    exact (s10_rec_present W mem t _ _ _ _ Hrec a Ha).
- exact (s10_ledger_keep ly S Hp W mem mem' md P Lam peak cnt fail ran most own HAR HA HPlow Hled).
Qed.

(* the premises every tx_* callee text shares, at a call made with sp regsc and window dwc *)
Lemma tx_state_pre : forall Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0
  b cap f own ks add pre ly S Hp W mem regsc dwc,
  tx_state Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b cap f own ks add pre
    ly S Hp W mem ->
  spZ regsc <= spZ regs0 -> spZ regs0 + dw0 <= spZ regsc + dwc ->
  room_live_cf S /\
  prhtx_place ly S W regsc mem dwc t /\ TRACE ly W mem t /\
  prhtx_rec W mem t b (len0 + Z.of_nat (length pre)) cap f /\
  prhtx_inv B Lam ly S W mem b (len0 + Z.of_nat (length pre)) cap (txt0 ++ pre) /\
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own /\
  blocks_bytes S - cap <= blocks_bytes S0 - cap0 /\ Hp = Hp0 /\
  (length pre <= length add)%nat.
Proof.
intros Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b cap f own ks add pre
  ly S Hp W mem regsc dwc (Ht0 & Ht47 & Hks & (Hrec & Hinv & Hpl & HHp & Hgr & Hbb) & HO & Htr & Hroom & Hled) H1 H2.
split; [exact Hroom|].
split; [exact (s10_place_down ly S W regs0 regsc mem dw0 dwc t Hpl H1 H2)|].
split; [exact Htr|]. split; [exact Hrec|]. split; [exact Hinv|]. split; [exact Hled|].
split; [lia|]. split; [exact HHp | exact (tx_out_len _ _ _ _ _ _ _ _ _ _ _ HO)].
Qed.

(* the callee's footprint inside the caller's (the call rules' HF: the caller's FP or a block made since its entry;
   HNS: the callee's FP bytes at or above alloc_ceiling are the caller's FP's) *)
Lemma tx_state_fp : forall Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0
  b cap f own ks add pre ly S Hp W mem md,
  tx_state Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b cap f own ks add pre
    ly S Hp W mem ->
  ARx ly S Hp W mem md ->
  forall a, inFP (prhtx_fp t b cap) a ->
  inFP (prhtx_fp t b0 cap0) a \/ in_tmp_block (ablocks B ly0 S0) (ablocks B ly S) a.
Proof.
intros Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b cap f own ks add pre
  ly S Hp W mem md (_ & _ & _ & (Hrec & Hinv & Hpl & HHp & Hgr & Hbb) & _) HAR.
apply (prhtx_call_fp ly0 S0 ly S Hp W mem md t b0 cap0 b cap (alx_sep segs B ARx LAWS) HAR Hgr).
intros Hc. destruct Hinv as (_ & [(Hz & _) | (_ & _ & Hin & _)]); [lia | exact Hin].
Qed.

Lemma tx_state_fp_win : forall Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0
  b cap f own ks add pre ly S Hp W mem,
  tx_state Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b cap f own ks add pre
    ly S Hp W mem ->
  forall a, YM05.alloc_ceiling <= a -> inFP (prhtx_fp t b cap) a -> inFP (prhtx_fp t b0 cap0) a.
Proof.
intros Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b cap f own ks add pre
  ly S Hp W mem (_ & _ & _ & (Hrec & Hinv & _) & _) a Ha Hf.
destruct (s10_fp_cases _ _ _ _ Hf) as [Hr | (Hc & Hb)].
- exists (t, t + 28). split; [left; reflexivity | exact Hr].
- exfalso. destruct Hinv as (_ & [(Hz & _) | (Hc0 & _ & _ & _ & _ & Hceil & _)]); [lia|].
  unfold req_size in Hb. destruct (Z.eqb_spec cap 0); lia.
Qed.

(* the callee's post folded back: its journal from the call state, its window clause, its prhtx_post at the buffer
   it was given, its outcome, its room and its ledger *)
Lemma tx_state_fold : forall Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0
  b cap f own ks add pre kc addc b1 cap1 f1 own' prec
  ly S Hp W mem md ly' S' Hp' W' mem' md' regsc dwc STK1 k1,
  tx_state Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b cap f own ks add pre
    ly S Hp W mem ->
  ARx ly S Hp W mem md ->
  TxModel.zsum kc = Z.of_nat (length addc) -> spZ regsc <= spZ regs0 -> 0 <= STK1 ->
  ajournal_x (SK := SK) segs B prh_pst ARx (STK1 + dwc) (spZ regsc + dwc)
    (prhtx_fp t b cap) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k1 ->
  (forall a, spZ regsc <= a < spZ regsc + dwc -> ~ inFP (prhtx_fp t b cap) a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  prhtx_post B Lam regsc dwc ly S Hp ly' S' Hp' W' mem' t b cap b1
    (len0 + Z.of_nat (length pre) + Z.of_nat (length prec)) cap1 f1 ((txt0 ++ pre) ++ prec) ->
  prhtx_out f f1 own own' b cap b1 cap1 (TxModel.tx_capf (len0 + Z.of_nat (length pre)) cap kc) addc prec ->
  room_live_cf S' ->
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own' ->
  tx_state Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b1 cap1 f1 own' (ks ++ kc)
    (add ++ addc) (pre ++ prec) ly' S' Hp' W' mem'.
Proof.
intros Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b cap f own ks add pre
  kc addc b1 cap1 f1 own' prec ly S Hp W mem md ly' S' Hp' W' mem' md' regsc dwc STK1 k1
  (Ht0 & Ht47 & Hks & (Hrec & Hinv & Hpl & HHp & Hgr & Hbb) & HO & Htr & Hroom & Hled) HAR Hkc Hsp HSTK1 HJ HWc
  (Hrec2 & Hinv2 & Hpl2 & HHp2 & Hgr2 & Hbb2) HOc Hroom2 Hled2.
pose proof HJ as (HAR2 & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _ & Htop).
pose proof Hpl as (_ & Hplo & Hphi & _ & _).
pose proof asan_consts as (C1 & _).
assert (Hlen : len0 + Z.of_nat (length (pre ++ prec)) = len0 + Z.of_nat (length pre) + Z.of_nat (length prec))
  by (rewrite length_app; lia).
assert (Hspc : YM05.alloc_ceiling <= spZ regsc) by lia.
split; [exact Ht0|]. split; [exact Ht47|].
split; [rewrite TxModel.zsum_app, Hks, Hkc, length_app; lia|].
rewrite Hlen, app_assoc.
split; [|split; [exact (tx_out_fold len0 cap0 f0 f f1 own0 own own' b0 b b1 cap cap1 ks kc add addc pre prec Hks HO HOc)|
  split; [|split; [exact Hroom2 | exact Hled2]]]].
- split; [exact Hrec2|]. split; [exact Hinv2|].
  split; [exact (s10_place_up ly S W mem ly' S' W' regs0 regsc mem' dw0 dwc t Hpl Hpl2)|].
  split; [rewrite HHp2; exact HHp|].
  split; [exact (prhtx_grow_trans ly0 S0 ly S ly' S' b0 cap0 b cap b1 cap1 Hgr Hgr2) | lia].
- apply (s10_trace_keep ly W mem ly' W' mem' t Htr Etop);
    [|intros Hc a Ha; exact (s10_rec_present W' mem' t _ _ _ _ Hrec2 a Ha)].
  intros Hc a Ha Hn.
  assert (Hreal : spZ regs0 + 16 <= t) by lia.
  destruct (Z_lt_le_dec a (spZ regsc + dwc)) as [Hw|Hw].
  + apply HWc; [lia|]. intros Hf. destruct (s10_fp_cases _ _ _ _ Hf) as [Hr | (Hc0 & Hb)]; [exact (Hn Hr)|].
    destruct Hinv as (_ & [(Hz & _) | (_ & _ & _ & _ & _ & Hceil' & _)]); [lia|].
    unfold req_size in Hb. destruct (Z.eqb_spec cap 0); lia.
  + apply F1; lia.
Qed.

(* the position folded: the callee's position clause at the call position rp_i0 + j *)
Lemma tx_pos_fold : forall rp_sm rp_x rp_os rp_i0 rp_H0 len0 cap0 f0 f f1 own0 own own' b0 b b1 cap cap1
  (j jq : nat) hist' S' (ks kc add addc pre prec : list Z),
  TxModel.zsum ks = Z.of_nat (length add) ->
  prhtx_out f0 f own0 own b0 cap0 b cap (TxModel.tx_capf len0 cap0 ks) add pre ->
  tx_jok len0 cap0 f0 f ks j ->
  prhtx_out f f1 own own' b cap b1 cap1 (TxModel.tx_capf (len0 + Z.of_nat (length pre)) cap kc) addc prec ->
  tx_jok (len0 + Z.of_nat (length pre)) cap f f1 kc jq ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i0 + j + jq)%nat rp_H0 hist' S' ->
  tx_pos rp_sm rp_x rp_os rp_i0 rp_H0 len0 cap0 f0 f1 (ks ++ kc) S'.
Proof.
intros rp_sm rp_x rp_os rp_i0 rp_H0 len0 cap0 f0 f f1 own0 own own' b0 b b1 cap cap1 j jq hist' S' ks kc add addc
  pre prec Hks HO Hj HOc Hq Hpos.
exists (j + jq)%nat, hist'.
split; [exact (tx_jok_fold len0 cap0 f0 f f1 own0 own own' b0 b b1 cap cap1 j jq ks kc add addc pre prec Hks HO Hj HOc Hq)|].
rewrite Nat.add_assoc. exact Hpos.
Qed.

(* at the caller's return: the text's position conjunct, in the text's order *)
Lemma tx_pos_post : forall rp_sm rp_x rp_os rp_i0 rp_H0 len0 cap0 f0 f ks S,
  tx_pos rp_sm rp_x rp_os rp_i0 rp_H0 len0 cap0 f0 f ks S ->
  exists j hist', (j <= length (prhtx_evs len0 cap0 ks))%nat /\
    PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i0 + j)%nat rp_H0 hist' S /\
    (f0 = 0 -> f = 0 -> j = length (prhtx_evs len0 cap0 ks)) /\ (f0 <> 0 -> j = 0%nat).
Proof.
intros rp_sm rp_x rp_os rp_i0 rp_H0 len0 cap0 f0 f ks S (j & hist & (Hj & HjE & Hj0) & Hpos).
exists j, hist. split; [exact Hj|]. split; [exact Hpos|]. split; [exact HjE | exact Hj0].
Qed.

(* a fake-frame bookkeeping step (set_fs: tx_string's frame_alloc_0 / its release) keeps the position
   (lib/Spec/PresetRoomPosKeep.v room_pos_set_fs) *)
Lemma s10_pos_set_fs : forall rp_sm rp_x rp_os i rp_H0 S f,
  (exists hist, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os i rp_H0 hist S) ->
  (exists hist, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os i rp_H0 hist (set_fs f S)).
Proof.
intros rp_sm rp_x rp_os i rp_H0 S f (hist & H). exists hist. exact (PresetRoomPosKeep.room_pos_set_fs _ _ _ _ _ _ S f H).
Qed.

(* ---- a read-only literal handed to tx_put: The state-free image binding kept_img B s n (PRH_Base.v, kept_at's
   THIRD case; per byte, the granule is zero-shadow or a const-shadow cell) and the image's bytes give src_rd and
   prhtx_kept at ANY ARx state with the read-only view ---- *)
(* MARKED STAND-IN (owner a Theorem Labs lane, the unit's image binding of B; ARcf gives it by amc_syms / aso_zshadow, YG0f.v:191) *)
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
(* MARKED STAND-IN (owner h-mani-a8, rule 18:56Z: img_shadow_vis_cf over the PER-INSTANCE CfImg bounds, restated over
   ARx; its B' instance lib/AU/AImgShadowVisCfB.v tfib_img_shadow_vis_cf_B) *)
Hypothesis img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> cf_img_lo <= a < cf_img_top ->
  aview segs (w_H W) mem (shadow_addr a) <> None.
(* the instance's kept_img bounds: in the low half, inside its CfImg bounds (closed facts of the instance) *)
Hypothesis img_box : 4096 <= pa_lo /\ pa_hi <= kLowMemEnd.
Hypothesis img_cf_box : cf_img_lo <= pa_lo /\ pa_hi <= cf_img_top.
(* AR_laws_x field 16: the const-shadow cells are kept *)
Let alx_const_cells := alx_const_cells segs B ARx LAWS.
Lemma s10_src_img : forall ly S Hp W mem md Lam s src,
  ARx ly S Hp W mem md -> arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) ->
  kept_img B s (Z.of_nat (length src)) -> (0 < length src)%nat ->
  (forall j, (j < length src)%nat ->
     option_map (fun bb : byte => bv_unsigned bb) (seg_rom segs (Z_to_bv 64 (s + Z.of_nat j))) = Some (nth j src 0)) ->
  src_rd W mem s src /\ prhtx_kept B Lam ly S s (Z.of_nat (length src)).
Proof.
intros ly S Hp W mem md Lam s src HAR HRO HKI Hn Hrom.
pose proof HKI as (Hlo & Hhi & Hro).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof img_box as (Hb1 & Hb2). pose proof img_cf_box as (Hc1 & Hc2).
split; [|left; right; right; exact HKI].
split; [|split; [lia|split; [lia|split; [unfold amem_range; left; lia|split]]]].
- unfold bytes_at. intros j Hj.
  destruct (Hro (s + Z.of_nat j) ltac:(lia)) as (Hr & Hno & Her & _).
  pose proof (HRO _ Hr Hno Her) as E. rewrite (Hrom j Hj) in E.
  exact (s10_val1_of_aview (w_H W) mem _ _ E).
- intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzs | (v & Hc & Hv)]).
  + destruct Hzs as (q & m & Hin & Hq & Hqm).
    pose proof (proj1 (Forall_forall _ _) zs_aligned (q, m) Hin) as (Hq8 & Hm8). cbn [fst snd] in Hq8, Hm8.
    pose proof (alx_zshadow segs B ARx LAWS ly S Hp W mem md (q, m) HAR ltac:(right; exact Hin)) as Hz.
    cbn [fst snd] in Hz. pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
    exact (zero_shadow_range (aview segs (w_H W) mem) SHADOW_OFF q m Hq8 Hm8 Hz x ltac:(lia)).
  + pose proof (proj1 (Forall_forall _ _) (alx_const_cells ly S Hp W mem md HAR) _ (Hc ly)) as Hcell.
    unfold cell_holds, z1, c1 in Hcell. cbn [c_at c_w c_val aeval] in Hcell.
    specialize (Hcell 0%nat ltac:(lia)). rewrite Z.add_0_r in Hcell.
    exists v. split; [|unfold saddr_ok; lia].
    unfold shadow_of_addr. unfold shadow_addr in Hcell. rewrite Hcell. f_equal.
    unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r, (Z.mod_small v (2 ^ 8)) by lia. apply Z.mod_small. lia.
- intros Hn0 s0 Hs. destruct (s10_hull_img pa_lo pa_hi s _ s0 Hn0 Hlo Hhi Hs) as [E Hr].
  rewrite E. apply (img_shadow_vis_x ly S Hp W mem md _ HAR). lia.
Qed.

(* ---- the call side conditions a caller of a tx_* text meets from its own widened journal ---- *)
(* the callee's window (fwin) at sp0 + o, window dw - o: present by the caller's journal *)
Lemma s10_fwin_callR : forall (R : world segs -> world segs -> Prop)
  STK dw sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem md k regsc o,
  AJR R (STK + dw) (sp0 + dw) FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem md k ->
  spZ regsc = sp0 + o -> o <= 0 -> - o <= STK -> 0 <= dw - o -> (dw - o) mod 16 = 0 ->
  fwin lyc W regsc mem (dw - o).
Proof.
intros R STK dw sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem md k regsc o HJ Hsp Ho Hstk Hd0 Hd16.
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hst.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof Hst as (_ & _ & _ & _ & _ & _ & _ & Htop).
split; [exact Hd0|]. split; [exact Hd16|]. split; [rewrite Etop, Hsp; lia|].
intros a Ha. apply Hpres. lia.
Qed.
Lemma s10_fwin_call : forall STK dw sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem md k regsc o,
  ajournal_x (SK := SK) segs B prh_pst ARx (STK + dw) (sp0 + dw) FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem md k ->
  spZ regsc = sp0 + o -> o <= 0 -> - o <= STK -> 0 <= dw - o -> (dw - o) mod 16 = 0 ->
  fwin lyc W regsc mem (dw - o).
Proof.
intros STK dw sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem md k regsc o HJ.
exact (s10_fwin_callR (@wle segs) STK dw sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem md k regsc o HJ).
Qed.

(* the read-only view survives a journal whose footprint does not open the sink (the statics are not read-only) *)
Hypothesis HPSTro : forall a, Exists (in_zr a) prh_pst -> ~ in_roP segs pa_relro_lo pa_relro_hi a.
Lemma s10_rod_keptR : forall (R : world segs -> world segs -> Prop)
  STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
  AJR R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W') mem').
Proof.
intros R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ Hsk H a Hro Hno Her.
pose proof (ajxR_img HJ) as F3.
rewrite F3; [exact (H a Hro Hno Her) | | exact Hno | exact Her | exact (fun Hp => HPSTro a Hp Hro) |
  exact (fp_spares_closed FP a Hsk)].
destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img a Hr)].
Qed.
Lemma s10_rod_kept : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
  ajournal_x (SK := SK) segs B prh_pst ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W') mem').
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (s10_rod_keptR (@wle segs) STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ).
Qed.

(* the text footprint never opens the sink: the record and the buffer are above page 0 *)
Lemma s10_fp_closed : forall Lam ly S W mem t b len cap txt,
  0 < t -> prhtx_inv B Lam ly S W mem b len cap txt -> ~ YI16.sink_open_fp (prhtx_fp t b cap).
Proof.
intros Lam ly S W mem t b len cap txt Ht (_ & Hb). apply sink_closed_pos. unfold prhtx_fp.
constructor; [cbn [fst]; exact Ht|]. destruct (Z.eqb_spec cap 0) as [E|E]; [constructor|].
cbn [ablocks_fp map]. constructor; [|constructor]. cbn [fst].
destruct Hb as [(Hz & _) | (_ & _ & _ & _ & H4096 & _)]; [lia | lia].
Qed.

(* ---- a harness block's footprint facts at ANY later ARx state whose ledger still lists it (tx_value's tree blocks D,
   tx_string's string): the static half of prhtx_bvis does not move, its shadow half is the user range's block
   shadow (field 14) and its granule-tail presence is field 15 ---- *)
Let alx_hshadow := alx_hshadow segs B ARx LAWS.
Let alx_blocks_tail := alx_blocks_tail segs B ARx LAWS.

Lemma s10_aview_present : forall (H : word -> bool) mem a, apresent H mem a -> aview segs H mem a <> None.
Proof.
intros H mem a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

Lemma s10_bvis_lam : forall ly S Hp W mem md Lam peak cnt fail ran most own (W0 : world segs) mem0 x k,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (x, k) Lam ->
  prhtx_bvis W0 mem0 x k -> prhtx_bvis W mem x k.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own W0 mem0 x k HAR HL Hin (H4096 & H8 & Hk0 & Hceil & Hamr & _ & _ & _).
pose proof HL as (_ & _ & HF & _).
pose proof (proj1 (Forall_forall _ _) HF (x, k) Hin) as (Hk & Hab & Hhp & H16 & _). cbn [fst snd] in Hk, Hab, Hhp, H16.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & _ & _ & Hpres & _).
split; [exact H4096|]. split; [exact H8|]. split; [exact Hk0|]. split; [exact Hceil|]. split; [exact Hamr|].
destruct (Z.eq_dec k 0) as [->|Hkn].
{ split; [apply range_addressable_nil; lia|]. split; [intros Hc; lia|].
  intros a Ha. change ((0 + 7) / 8 * 8) with 0 in Ha. lia. }
assert (Hrq : req_size (k + cf_head) = k + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
destruct (alx_hshadow ly S Hp W mem md _ _ HAR Hab Hhp) as [Hbs Hhull].
rewrite Hrq in Hbs, Hhull. replace (x - cf_head + cf_head) with x in Hbs, Hhull by lia.
replace (k + cf_head - cf_head) with k in Hbs, Hhull by lia.
split; [exact (block_shadow_range (aview segs (w_H W) mem) SHADOW_OFF x k x k Hbs ltac:(lia) ltac:(lia))|].
split; [intros _; apply Hhull; lia|].
intros a Ha. destruct (Z_lt_le_dec a (x + k)) as [Hlt|Hge].
- apply s10_aview_present. rewrite Hrq in Hpres. exact (proj1 (Hpres a ltac:(lia))).
- apply (alx_blocks_tail ly S Hp W mem md _ _ a HAR Hab). rewrite Hrq. replace (x - cf_head + (k + cf_head)) with (x + k) by lia.
  apply Z.mod_divide in H16 as [j Hj]; [|lia].
  pose proof (Z.div_mod (k + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (k + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod (x + k + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + k + 7) 8 ltac:(lia)).
  lia.
Qed.

(* ======== PREP for the batch kit's texts (a working branch 4dcec0343c87; NOT the record glue, which is ec9d6e6a0914 on
   a working branch). The batch posts are BUDGETED (PRH_Base.fpostWb = YCbqGwild.fpostW_xbR at wle' segs RZ_cf,
   PRH_Base.v:1578-1583; fpostWbm its fQmn form: the journal at a budget WS the post chooses, of which it claims P WS =
   wbudget_if f0 [] k WS), and each tx text takes a GUARDED room premise and a GUARDED consumer window (f0 = 0 -> ..).
   Added here: the budgeted window call rule (s10_call_Wb / _Wbm) and tail-call rule (s10_tail_Wb / _Wbm), the fold over
   a budgeted callee journal (tx_state_fold_w), each beside its R form, and the per-call threading of the guarded
   premises from the caller's own (tx_room_window, tx_cons_window) and of the budget (tx_budget_fold). The glue above is
   no longer the record glue's (prhtx_out's arguments, :177-290; the R forms and RCF / SRRCF, :486-606, :1135-1180). The
   threading is the DONE path's: a call entered with failed = 0 has a caller still at failed = 0, whose outcome so far
   is DONE (tx_out_done); a call entered failed needs no room, no window and claims no budget (the guards). ======== *)
#[local] Notation AJW := (ajournal_xw (SK := SK) segs B prh_pst ARx).
(* the WS journal over a world relation R (YCbqG.ajournal_xwR); AJW is its instance at wle *)
#[local] Notation AJWR R := (ajournal_xwR (SK := SK) segs B prh_pst ARx R).


(* the DONE arm read off: a text still at failed = 0 was entered at failed = 0 and appended its whole text so far,
   at the model cap *)
Lemma tx_out_done : forall f0 f own0 own b0 cap0 b cap capf add pre,
  prhtx_out f0 f own0 own b0 cap0 b cap capf add pre -> f = 0 -> f0 = 0 /\ pre = add /\ cap = capf.
Proof.
intros f0 f own0 own b0 cap0 b cap capf add pre
  [(Hf0 & _ & _ & Ep & Ec) | [(Hf0 & Hff & _) | (_ & Hf1 & _)]] Hf; [| lia | lia].
split; [exact Hf0 | split; [exact Ep | exact Ec]].
Qed.

(* a callee's GUARDED consumer window (f = 0 -> prh_cons_from .. (rp_i + j) k_callee) from the caller's (over all its
   pieces ks ++ kc ++ rest), on the DONE path: j is all events of ks (tx_jok), and the callee's events are the next
   ones (prhtx_evs_app, PRH_Base.prh_cons_from_sub) *)
Lemma tx_cons_window : forall sm x os (i0 j : nat) (len0 cap0 f0 f own0 own b0 b cap : Z) (ks add pre kc rest : list Z),
  prhtx_out f0 f own0 own b0 cap0 b cap (TxModel.tx_capf len0 cap0 ks) add pre ->
  tx_jok len0 cap0 f0 f ks j -> TxModel.zsum ks = Z.of_nat (length add) ->
  (f0 = 0 -> prh_cons_from sm x os i0 (length (prhtx_evs len0 cap0 (ks ++ kc ++ rest)))) ->
  f = 0 -> prh_cons_from sm x os (i0 + j) (length (prhtx_evs (len0 + Z.of_nat (length pre)) cap kc)).
Proof.
intros sm x os i0 j len0 cap0 f0 f own0 own b0 b cap ks add pre kc rest HO (_ & HjE & _) Hks HC Hf.
destruct (tx_out_done f0 f own0 own b0 cap0 b cap _ add pre HO Hf) as (Hf0 & -> & ->).
rewrite (HjE Hf0 Hf). specialize (HC Hf0).
rewrite prhtx_evs_app, length_app, prhtx_evs_app, length_app in HC.
rewrite <- Hks.
eapply (prh_cons_from_sub sm x os i0 _ (length (prhtx_evs len0 cap0 ks)) _); [|exact HC].
lia.
Qed.

(* a callee's GUARDED room premise from the caller's room at its entry depot d0, the caller's journal so far (its
   wild part covered by d0's and a budget WS) and the caller's budget so far (at most the events of ks), on the
   DONE path: the room left is the events still to come, of which the callee's are the first (YCbqGwild's
   wild_room_step / wild_room_le) *)
Lemma tx_room_window : forall (U : Univ) (d0 d WS : list (list Z)) (len0 cap0 f0 f own0 own b0 b cap : Z)
  (ks add pre kc rest : list Z),
  prhtx_out f0 f own0 own b0 cap0 b cap (TxModel.tx_capf len0 cap0 ks) add pre ->
  TxModel.zsum ks = Z.of_nat (length add) ->
  (f0 = 0 -> YCbqGwild.wild_room U [] (length (prhtx_evs len0 cap0 (ks ++ kc ++ rest))) d0) ->
  incl (wild_part U d) (wild_part U d0 ++ WS) ->
  wbudget_if f0 [] (length (prhtx_evs len0 cap0 ks)) WS ->
  f = 0 -> YCbqGwild.wild_room U [] (length (prhtx_evs (len0 + Z.of_nat (length pre)) cap kc)) d.
Proof.
intros U d0 d WS len0 cap0 f0 f own0 own b0 b cap ks add pre kc rest HO Hks Hr Hi Hb Hf.
destruct (tx_out_done f0 f own0 own b0 cap0 b cap _ add pre HO Hf) as (Hf0 & -> & ->).
specialize (Hr Hf0). specialize (Hb Hf0). unfold YCbqGwild.wbudget in Hb.
rewrite <- Hks.
rewrite prhtx_evs_app, length_app in Hr.
set (k1 := length (prhtx_evs len0 cap0 ks)) in *.
set (krest := length (prhtx_evs (len0 + TxModel.zsum ks) (TxModel.tx_capf len0 cap0 ks) (kc ++ rest))) in *.
pose proof (YCbqGwild.wild_room_step U [] (k1 + krest) d0 d WS Hr Hi ltac:(lia)) as Hs.
apply (YCbqGwild.wild_room_le U [] (k1 + krest - YCbqGwild.wfresh [] WS)); [|exact Hs].
unfold krest. rewrite prhtx_evs_app, length_app. lia.
Qed.

(* the caller's budget so far, one callee further: the callee's budget is claimed at its entry failure f, which is 0
   whenever the caller was entered at failed = 0 (DEAD, carried by the caller) *)
Lemma tx_budget_fold : forall (len0 cap0 f0 f own0 own b0 b cap : Z) (ks add pre kc : list Z) (WS WS1 : list (list Z)),
  prhtx_out f0 f own0 own b0 cap0 b cap (TxModel.tx_capf len0 cap0 ks) add pre ->
  TxModel.zsum ks = Z.of_nat (length add) -> (f0 = 0 -> f = 0) ->
  wbudget_if f0 [] (length (prhtx_evs len0 cap0 ks)) WS ->
  wbudget_if f [] (length (prhtx_evs (len0 + Z.of_nat (length pre)) cap kc)) WS1 ->
  wbudget_if f0 [] (length (prhtx_evs len0 cap0 (ks ++ kc))) (WS ++ WS1).
Proof.
intros len0 cap0 f0 f own0 own b0 b cap ks add pre kc WS WS1 HO Hks Hdead Hb Hb1 Hf0.
pose proof (Hdead Hf0) as Hf.
destruct (tx_out_done f0 f own0 own b0 cap0 b cap _ add pre HO Hf) as (_ & -> & ->).
specialize (Hb Hf0). specialize (Hb1 Hf). unfold YCbqGwild.wbudget in Hb, Hb1 |- *.
rewrite <- Hks in Hb1.
rewrite YCbqGwild.wfresh_app, prhtx_evs_app, length_app. lia.
Qed.

(* ---- THE PROGRAM-CALL RULE IN THE CALLER WINDOW for a BUDGETED callee (s10_call_W at a caller budget WS0, the
   callee's post fpostWb P): YCbqGwild.afn_pre_x_at_w for the callee's entry, YCbqG.ajournal_xw_sub for the
   composition, whose budget is WS0 ++ WS1 ---- *)
(* the same rule over a transitive world relation R: the caller's journal, the callee's post and the composition at R
   (the step relation SRrG at R); s10_call_Wb is its instance at RCF (:1396) *)
Lemma s10_call_WbR : forall (R : world segs -> world segs -> Prop), (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ms STK dw sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 (o : Z) spw raw
  ch1 (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJWR R (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> 0 <= dw -> dw mod 16 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   YA0nH.SRrG segs R W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (YCbqGwild.fpostW_xbR (SK := SK) segs B prh_pst ARx R P STK1 (dw - o) FP1 (ms_regs ms) lyc Sc Hpc W
        (ms_mem ms) mdc Q)) ->
  fp_sub_x B (STK + dw) (sp0 + dw) FP FP1 ly S own lyc Sc ->
  YA0nH.SRrG segs R W (mkCfg ms mdc)
   (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
      c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\ P WS1 /\
      AJWR R (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
      AJWR R (STK1 + (dw - o)) (sp0 + dw) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
      (forall a, sp0 + o <= a < sp0 + dw -> ~ inFP FP1 a ->
         aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
      aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rt W E ss ms STK dw sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 o spw raw ch1 P Q
  HS Hrv HJ Hsp HE2 Hspw Hal Hneg Hstk1 Hbud Hdw0 Hdw16 Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (ajxR_stk HJ) as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
assert (Hbase : spZ (ms_regs ms) + (dw - o) = sp0 + dw) by zlia.
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv).
eapply (YA0nH.SRrG_mono segs R).
{ apply Hcallee. eapply (YCbqGwild.afn_pre_x_at_wR (SK := SK) segs B prh_pst ARx R (STK + dw) (sp0 + dw) FP ly S Hp W0
    mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 (ms_regs ms) STK1 (o - dw) ch1); try eassumption.
- zlia.
- rewrite Zminus_mod, Hal, Hdw16. reflexivity.
- zlia.
- zlia.
- rewrite Hra. exact Hraw.
- unfold raZ. rewrite Hra. exact Hra4.
- rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ HN. unfold YCbqGwild.fpostW_xbR in HN.
destruct HN as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HPW & HJ1 & HW1 & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1, WS1. rewrite Hra. split; [reflexivity|]. split; [exact HPW|].
rewrite Hbase in HJ1.
split; [| split; [exact HJ1 | split; [| split; [exact HP | exact HQ]]]].
- change own with ([] ++ own).
  eapply (ajournal_xw_subR segs B prh_pst ARx LAWS pa_segs_low R Rt);
    [exact HJ | exact HJ1 | zlia | zlia | exact HF].
- intros a Ha Hn. apply HW1; [rewrite Hsp'; zlia | exact Hn].
Qed.
Lemma s10_call_Wb : forall W E ss ms STK dw sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 (o : Z) spw raw
  ch1 (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJWR RCF (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> 0 <= dw -> dw mod 16 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRRCF W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (fpostWb B ARx SK P STK1 (dw - o) FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  fp_sub_x B (STK + dw) (sp0 + dw) FP FP1 ly S own lyc Sc ->
  SRRCF W (mkCfg ms mdc)
   (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
      c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\ P WS1 /\
      AJWR RCF (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
      AJWR RCF (STK1 + (dw - o)) (sp0 + dw) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
      (forall a, sp0 + o <= a < sp0 + dw -> ~ inFP FP1 a ->
         aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
      aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (s10_call_WbR RCF (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)). Qed.

(* a budgeted callee with an m-form post (fpostWbm = fpostWb .. (fQmn mem Q)) *)
(* its m-form over R; s10_call_Wbm is its instance at RCF (:1451) *)
Lemma s10_call_WbmR : forall (R : world segs -> world segs -> Prop), (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ms STK dw sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 (o : Z) spw raw
  ch1 (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJWR R (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> 0 <= dw -> dw mod 16 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   YA0nH.SRrG segs R W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (YCbqGwild.fpostW_xbR (SK := SK) segs B prh_pst ARx R P STK1 (dw - o) FP1 (ms_regs ms) lyc Sc Hpc W
        (ms_mem ms) mdc (fQmn (ms_mem ms) Q))) ->
  fp_sub_x B (STK + dw) (sp0 + dw) FP FP1 ly S own lyc Sc ->
  YA0nH.SRrG segs R W (mkCfg ms mdc)
   (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
      c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\ P WS1 /\
      AJWR R (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
      AJWR R (STK1 + (dw - o)) (sp0 + dw) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
      (forall a, sp0 + o <= a < sp0 + dw -> ~ inFP FP1 a ->
         aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
      aregs_preserved (ms_regs ms) regs2 /\ fQmn (ms_mem ms) Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rt W E ss ms STK dw sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 o spw raw ch1 P Q.
exact (s10_call_WbR R Rt W E ss ms STK dw sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 o spw raw ch1 P
  (fQmn (ms_mem ms) Q)).
Qed.
Lemma s10_call_Wbm : forall W E ss ms STK dw sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 (o : Z) spw raw
  ch1 (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJWR RCF (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> 0 <= dw -> dw mod 16 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRRCF W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (fpostWbm B ARx SK P STK1 (dw - o) FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  fp_sub_x B (STK + dw) (sp0 + dw) FP FP1 ly S own lyc Sc ->
  SRRCF W (mkCfg ms mdc)
   (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
      c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\ P WS1 /\
      AJWR RCF (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
      AJWR RCF (STK1 + (dw - o)) (sp0 + dw) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
      (forall a, sp0 + o <= a < sp0 + dw -> ~ inFP FP1 a ->
         aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
      aregs_preserved (ms_regs ms) regs2 /\ fQmn (ms_mem ms) Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (s10_call_WbmR RCF (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)). Qed.

(* tx_state_fold over a BUDGETED callee journal (AJW at its budget WS1), over any world relation R: the same fold,
   which reads no depot and no world conjunct; tx_state_fold_w is its instance at wle *)
Lemma tx_state_fold_wR : forall (R : world segs -> world segs -> Prop)
  Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0
  b cap f own ks add pre kc addc b1 cap1 f1 own' prec
  ly S Hp W mem md ly' S' Hp' W' mem' md' regsc dwc STK1 k1 WS1,
  tx_state Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b cap f own ks add pre
    ly S Hp W mem ->
  ARx ly S Hp W mem md ->
  TxModel.zsum kc = Z.of_nat (length addc) -> spZ regsc <= spZ regs0 -> 0 <= STK1 ->
  AJWR R (STK1 + dwc) (spZ regsc + dwc) (prhtx_fp t b cap) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k1 WS1 ->
  (forall a, spZ regsc <= a < spZ regsc + dwc -> ~ inFP (prhtx_fp t b cap) a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  prhtx_post B Lam regsc dwc ly S Hp ly' S' Hp' W' mem' t b cap b1
    (len0 + Z.of_nat (length pre) + Z.of_nat (length prec)) cap1 f1 ((txt0 ++ pre) ++ prec) ->
  prhtx_out f f1 own own' b cap b1 cap1 (TxModel.tx_capf (len0 + Z.of_nat (length pre)) cap kc) addc prec ->
  room_live_cf S' ->
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own' ->
  tx_state Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b1 cap1 f1 own' (ks ++ kc)
    (add ++ addc) (pre ++ prec) ly' S' Hp' W' mem'.
Proof.
intros R Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b cap f own ks add pre
  kc addc b1 cap1 f1 own' prec ly S Hp W mem md ly' S' Hp' W' mem' md' regsc dwc STK1 k1 WS1
  (Ht0 & Ht47 & Hks & (Hrec & Hinv & Hpl & HHp & Hgr & Hbb) & HO & Htr & Hroom & Hled) HAR Hkc Hsp HSTK1 HJ HWc
  (Hrec2 & Hinv2 & Hpl2 & HHp2 & Hgr2 & Hbb2) HOc Hroom2 Hled2.
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_stk HJ) as Hstk.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _ & Htop).
pose proof Hpl as (_ & Hplo & Hphi & _ & _).
pose proof asan_consts as (C1 & _).
assert (Hlen : len0 + Z.of_nat (length (pre ++ prec)) = len0 + Z.of_nat (length pre) + Z.of_nat (length prec))
  by (rewrite length_app; lia).
assert (Hspc : YM05.alloc_ceiling <= spZ regsc) by lia.
split; [exact Ht0|]. split; [exact Ht47|].
split; [rewrite TxModel.zsum_app, Hks, Hkc, length_app; lia|].
rewrite Hlen, app_assoc.
split; [|split; [exact (tx_out_fold len0 cap0 f0 f f1 own0 own own' b0 b b1 cap cap1 ks kc add addc pre prec Hks HO HOc)|
  split; [|split; [exact Hroom2 | exact Hled2]]]].
- split; [exact Hrec2|]. split; [exact Hinv2|].
  split; [exact (s10_place_up ly S W mem ly' S' W' regs0 regsc mem' dw0 dwc t Hpl Hpl2)|].
  split; [rewrite HHp2; exact HHp|].
  split; [exact (prhtx_grow_trans ly0 S0 ly S ly' S' b0 cap0 b cap b1 cap1 Hgr Hgr2) | lia].
- apply (s10_trace_keep ly W mem ly' W' mem' t Htr Etop);
    [|intros Hc a Ha; exact (s10_rec_present W' mem' t _ _ _ _ Hrec2 a Ha)].
  intros Hc a Ha Hn.
  assert (Hreal : spZ regs0 + 16 <= t) by lia.
  destruct (Z_lt_le_dec a (spZ regsc + dwc)) as [Hw|Hw].
  + apply HWc; [lia|]. intros Hf. destruct (s10_fp_cases _ _ _ _ Hf) as [Hr | (Hc0 & Hb)]; [exact (Hn Hr)|].
    destruct Hinv as (_ & [(Hz & _) | (_ & _ & _ & _ & _ & Hceil' & _)]); [lia|].
    unfold req_size in Hb. destruct (Z.eqb_spec cap 0); lia.
  + apply F1; lia.
Qed.
Lemma tx_state_fold_w : forall Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0
  b cap f own ks add pre kc addc b1 cap1 f1 own' prec
  ly S Hp W mem md ly' S' Hp' W' mem' md' regsc dwc STK1 k1 WS1,
  tx_state Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b cap f own ks add pre
    ly S Hp W mem ->
  ARx ly S Hp W mem md ->
  TxModel.zsum kc = Z.of_nat (length addc) -> spZ regsc <= spZ regs0 -> 0 <= STK1 ->
  AJW (STK1 + dwc) (spZ regsc + dwc) (prhtx_fp t b cap) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k1 WS1 ->
  (forall a, spZ regsc <= a < spZ regsc + dwc -> ~ inFP (prhtx_fp t b cap) a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  prhtx_post B Lam regsc dwc ly S Hp ly' S' Hp' W' mem' t b cap b1
    (len0 + Z.of_nat (length pre) + Z.of_nat (length prec)) cap1 f1 ((txt0 ++ pre) ++ prec) ->
  prhtx_out f f1 own own' b cap b1 cap1 (TxModel.tx_capf (len0 + Z.of_nat (length pre)) cap kc) addc prec ->
  room_live_cf S' ->
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own' ->
  tx_state Lam regs0 dw0 ly0 S0 Hp0 t b0 len0 cap0 f0 txt0 peak cnt fail ran most own0 b1 cap1 f1 own' (ks ++ kc)
    (add ++ addc) (pre ++ prec) ly' S' Hp' W' mem'.
Proof. exact (tx_state_fold_wR (@wle segs)). Qed.

(* ---- THE TAIL-CALL RULE for a BUDGETED callee (s10_tail_W at a caller budget WS0, the callee's post fpostWb P1): the
   caller's post at budget WS0 ++ WS1, whose claim P follows from the callee's P1 (for tx_value's tail arms the two
   budgets are the same term: PRH_FnTx.v :987-990) ---- *)
Lemma s10_tail_WbR : forall (R : world segs -> world segs -> Prop), (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ms STK dw sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k WS0 STK1 FP1 ch1
  (regs0 : bvmap 5 word) (P P1 : list (list Z) -> Prop)
  (Q Q1 : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJWR R (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md [] lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  spZ regs0 = sp0 -> spZ (ms_regs ms) = sp0 ->
  0 <= STK1 -> STK1 <= STK -> 0 <= dw -> dw mod 16 = 0 ->
  aregs_preserved regs0 (ms_regs ms) -> getr (ms_regs ms) 1 = getr regs0 1 ->
  YK0s.ret_ok (getr regs0 1) -> 4096 <= raZ regs0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) sp0 (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   YA0nH.SRrG segs R W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (YCbqGwild.fpostW_xbR (SK := SK) segs B prh_pst ARx R P1 STK1 dw FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q1)) ->
  fp_sub_x B (STK + dw) (sp0 + dw) FP FP1 ly S [] lyc Sc ->
  (forall a, sp0 <= a < sp0 + dw -> inFP FP1 a -> inFP FP a) ->
  (forall a, sp0 <= a < sp0 + dw -> ~ inFP FP a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W0) mem a) ->
  (forall WS1, P1 WS1 -> P (WS0 ++ WS1)) ->
  (forall ly' S' Hp' W' regs' mem' md', Q1 ly' S' Hp' W' regs' mem' md' -> Q ly' S' Hp' W' regs' mem' md') ->
  YA0nH.SRrG segs R W (mkCfg ms mdc)
    (YCbqGwild.fpostW_xbR (SK := SK) segs B prh_pst ARx R P STK dw FP regs0 ly S Hp W0 mem md Q).
Proof.
intros R Rt W E ss ms STK dw sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k WS0 STK1 FP1 ch1 regs0 P P1 Q Q1
  HS Hrv HJ Hsp0 Hspt Hstk1 Hbud Hdw0 Hdw16 Hpr Hra Hraok Hra4 Hgp Htp Hch Hcallee HF HNS HWIN HPP HQQ.
pose proof (ajxR_stk HJ) as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv).
eapply (YA0nH.SRrG_mono segs R).
{ apply Hcallee. eapply (YCbqGwild.afn_pre_x_at_wR (SK := SK) segs B prh_pst ARx R (STK + dw) (sp0 + dw) FP ly S Hp W0
    mem md [] lyc Sc Hpc W (ms_mem ms) mdc k WS0 (ms_regs ms) STK1 (- dw) ch1); try eassumption.
- zlia.
- apply Z_mod_zero_opp_full. exact Hdw16.
- zlia.
- zlia.
- rewrite Hra. exact Hraok.
- unfold raZ in *. rewrite Hra. exact Hra4.
- rewrite Hspt. exact Hch. }
cbv beta. intros W2 c2 _ HN. unfold YCbqGwild.fpostW_xbR in HN |- *.
destruct HN as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HPW & HJ1 & HW1 & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, (k + k1), (WS0 ++ WS1). rewrite Hra. split; [reflexivity|].
split; [exact (HPP WS1 HPW)|].
rewrite Hspt in HJ1. rewrite Hsp0.
split; [change (@nil (Z * Z)) with ((@nil (Z * Z)) ++ []);
  eapply (ajournal_xw_subR segs B prh_pst ARx LAWS pa_segs_low R Rt); [exact HJ | exact HJ1 | zlia | zlia | exact HF]|].
split; [| split; [| exact (HQQ _ _ _ _ _ _ _ HQ)]].
- intros a Ha Hn. rewrite (HW1 a ltac:(rewrite Hspt; zlia) ltac:(intros H1; exact (Hn (HNS a ltac:(zlia) H1)))).
  apply HWIN; [zlia | exact Hn].
- intros r Hr. rewrite (HP r Hr). exact (Hpr r Hr).
Qed.
Lemma s10_tail_Wb : forall W E ss ms STK dw sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k WS0 STK1 FP1 ch1
  (regs0 : bvmap 5 word) (P P1 : list (list Z) -> Prop)
  (Q Q1 : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJWR RCF (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md [] lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  spZ regs0 = sp0 -> spZ (ms_regs ms) = sp0 ->
  0 <= STK1 -> STK1 <= STK -> 0 <= dw -> dw mod 16 = 0 ->
  aregs_preserved regs0 (ms_regs ms) -> getr (ms_regs ms) 1 = getr regs0 1 ->
  YK0s.ret_ok (getr regs0 1) -> 4096 <= raZ regs0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) sp0 (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRRCF W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (fpostWb B ARx SK P1 STK1 dw FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q1)) ->
  fp_sub_x B (STK + dw) (sp0 + dw) FP FP1 ly S [] lyc Sc ->
  (forall a, sp0 <= a < sp0 + dw -> inFP FP1 a -> inFP FP a) ->
  (forall a, sp0 <= a < sp0 + dw -> ~ inFP FP a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W0) mem a) ->
  (forall WS1, P1 WS1 -> P (WS0 ++ WS1)) ->
  (forall ly' S' Hp' W' regs' mem' md', Q1 ly' S' Hp' W' regs' mem' md' -> Q ly' S' Hp' W' regs' mem' md') ->
  SRRCF W (mkCfg ms mdc) (fpostWb B ARx SK P STK dw FP regs0 ly S Hp W0 mem md Q).
Proof. exact (s10_tail_WbR RCF (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)). Qed.

(* a budgeted tail call to a callee with an m-form post, from a caller whose own m-form post is at its entry memory;
   over R, and s10_tail_Wbm is its instance at RCF (:1654) *)
Lemma s10_tail_WbmR : forall (R : world segs -> world segs -> Prop), (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ms STK dw sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k WS0 STK1 FP1 ch1
  (regs0 : bvmap 5 word) (P P1 : list (list Z) -> Prop)
  (Q Q1 : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJWR R (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md [] lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  spZ regs0 = sp0 -> spZ (ms_regs ms) = sp0 ->
  0 <= STK1 -> STK1 <= STK -> 0 <= dw -> dw mod 16 = 0 ->
  aregs_preserved regs0 (ms_regs ms) -> getr (ms_regs ms) 1 = getr regs0 1 ->
  YK0s.ret_ok (getr regs0 1) -> 4096 <= raZ regs0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) sp0 (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   YA0nH.SRrG segs R W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (YCbqGwild.fpostW_xbR (SK := SK) segs B prh_pst ARx R P1 STK1 dw FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc
        (fQmn (ms_mem ms) Q1))) ->
  fp_sub_x B (STK + dw) (sp0 + dw) FP FP1 ly S [] lyc Sc ->
  (forall a, sp0 <= a < sp0 + dw -> inFP FP1 a -> inFP FP a) ->
  (forall a, sp0 <= a < sp0 + dw -> ~ inFP FP a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W0) mem a) ->
  (forall WS1, P1 WS1 -> P (WS0 ++ WS1)) ->
  (forall ly' S' Hp' W' regs' mem' md', Q1 ly' S' Hp' W' regs' mem' md' -> Q ly' S' Hp' W' regs' mem' md') ->
  (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs (ms_mem ms)) ->
  YA0nH.SRrG segs R W (mkCfg ms mdc)
    (YCbqGwild.fpostW_xbR (SK := SK) segs B prh_pst ARx R P STK dw FP regs0 ly S Hp W0 mem md (fQmn mem Q)).
Proof.
intros R Rt W E ss ms STK dw sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k WS0 STK1 FP1 ch1 regs0 P P1 Q Q1
  HS Hrv HJ Hsp0 Hspt Hstk1 Hbud Hdw0 Hdw16 Hpr Hra Hraok Hra4 Hgp Htp Hch Hcallee HF HNS HWIN HPP HQQ HMN.
exact (s10_tail_WbR R Rt W E ss ms STK dw sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k WS0 STK1 FP1 ch1 regs0 P P1
  (fQmn mem Q) (fQmn (ms_mem ms) Q1) HS Hrv HJ Hsp0 Hspt Hstk1 Hbud Hdw0 Hdw16 Hpr Hra Hraok Hra4 Hgp Htp
  Hch Hcallee HF HNS HWIN HPP
  (fun ly' S' Hp' W' regs' mem' md' H => conj (HQQ _ _ _ _ _ _ _ (proj1 H)) (fun Hm => proj2 H (HMN Hm)))).
Qed.
Lemma s10_tail_Wbm : forall W E ss ms STK dw sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k WS0 STK1 FP1 ch1
  (regs0 : bvmap 5 word) (P P1 : list (list Z) -> Prop)
  (Q Q1 : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJWR RCF (STK + dw) (sp0 + dw) FP ly S Hp W0 mem md [] lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  spZ regs0 = sp0 -> spZ (ms_regs ms) = sp0 ->
  0 <= STK1 -> STK1 <= STK -> 0 <= dw -> dw mod 16 = 0 ->
  aregs_preserved regs0 (ms_regs ms) -> getr (ms_regs ms) 1 = getr regs0 1 ->
  YK0s.ret_ok (getr regs0 1) -> 4096 <= raZ regs0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) sp0 (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRRCF W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
     (fpostWbm B ARx SK P1 STK1 dw FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q1)) ->
  fp_sub_x B (STK + dw) (sp0 + dw) FP FP1 ly S [] lyc Sc ->
  (forall a, sp0 <= a < sp0 + dw -> inFP FP1 a -> inFP FP a) ->
  (forall a, sp0 <= a < sp0 + dw -> ~ inFP FP a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W0) mem a) ->
  (forall WS1, P1 WS1 -> P (WS0 ++ WS1)) ->
  (forall ly' S' Hp' W' regs' mem' md', Q1 ly' S' Hp' W' regs' mem' md' -> Q ly' S' Hp' W' regs' mem' md') ->
  (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs (ms_mem ms)) ->
  SRRCF W (mkCfg ms mdc) (fpostWbm B ARx SK P STK dw FP regs0 ly S Hp W0 mem md Q).
Proof. exact (s10_tail_WbmR RCF (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)). Qed.

End c.

(* ---- the audit read-outs: every definition of this file with its implicit arguments shown (the Print implicit
   check), and the assumptions of its two composition lemmas ---- *)
Set Printing Implicit.
Print tx_jok.
Print tx_state.
Print tx_pos.
Print s10_agree.
Unset Printing Implicit.
Print Assumptions tx_state_fold.
Print Assumptions tx_put_res.
