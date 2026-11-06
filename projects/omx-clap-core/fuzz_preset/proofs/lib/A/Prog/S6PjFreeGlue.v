(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_free_seg_loop.v, with its module paths and module names changed; 138 of its 215 lines of code are new or changed and 422 lines of the source are left out. *)
(* fuzz_preset image A, slice S6 (WalkS6): the SHARED GLUE of pj_free's segment files (S6PjFreeEnt.v, S6PjFreeLH.v,
   S6PjFreeLKC.v, S6PjFreeTail.v), ONE copy each. rule 24: proves no function (kind: walk glue).
   Moved, statements and proofs unchanged up to the pfa_ names, from the sub-lanes' files, where each had been written
   twice or three times: S6PjFreeLH.v (blob 210d9585155a): U_add, reg_of_U, pres (pres_bv), nd_app, ndr, ndl, nd_perm,
   lam_now, inFP_hbl, inFP_hbl_inv, lam_blk, hb_vis, hb_apart, v_apart, frame_same and the tactic pfa_reg (pflh_reg:
   the call-state arm takes the register list out of setpc before vm_compute, so no image term is computed);
   S6PjFreeLKC.v (blob 0a710cd3d435): U_srl3, U_cell; S6PjFreeTail.v (blob d9017977f324): stk_ff. The replaced copies
   (pfk_*, pfl_*, pfe_reg) had the same statements, except pfk_hb_vis (two of pfa_hb_vis's four conjuncts) and
   pfk_reg / pfe_reg (pfa_reg's arms).
   Section hypothesis: AR_laws_x at cf_head (LAWS). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YCbqGcallW YC80xf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YC80xf_inv YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnReader PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PRW_StepKit S6PjCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjStringCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfHeadSh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon PjFreePure S6PjFree S6PjFreeKeep.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- bv / U bookkeeping ---- *)
Lemma pfa_U_add : forall E a b, U E (SAlu ALU_ADD a b) = (U E a + U E b) mod 2 ^ 64.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. reflexivity. Qed.
Lemma pfa_reg_of_U : forall E e (w : word) z, w = sv_denot E e -> U E e = z -> w = Z_to_bv 64 z.
Proof. intros E e w z -> <-. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma pfa_pres : forall r1 r2 (r : bv 5), aregs_preserved r1 r2 -> acallee_saved (bv_unsigned r) -> getr r2 r = getr r1 r.
Proof. intros r1 r2 r HP Hr. pose proof (HP _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
(* ---- NoDup bookkeeping (the NoDup pj_oshapeR states) (glue another loop segment can use; image B's pj_free_seg_loop.v) ---- *)
Lemma pfa_nd_app : forall (l1 l2 : list (Z * Z)) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; intros l2 x HN H1 H2; [destruct H1|].
cbn [app] in HN. inversion HN as [|y' l' Hy HN']; subst.
destruct H1 as [<- | H1]; [apply Hy; apply list_elem_of_In; apply in_or_app; right; exact H2 | exact (IH l2 x HN' H1 H2)].
Qed.
Lemma pfa_ndr : forall (l1 l2 : list (Z * Z)), NoDup (l1 ++ l2) -> NoDup l2.
Proof. induction l1 as [|y l1 IH]; intros l2 HN; [exact HN|]. cbn [app] in HN. inversion HN; subst. apply IH. assumption. Qed.
Lemma pfa_ndl : forall (l1 l2 : list (Z * Z)), NoDup (l1 ++ l2) -> NoDup l1.
Proof.
induction l1 as [|y l1 IH]; intros l2 HN; [constructor|]. cbn [app] in HN. inversion HN as [|y' l' Hy HN']; subst.
constructor; [intros H; apply Hy; apply list_elem_of_In; apply list_elem_of_In in H; apply in_or_app; left; exact H
  | exact (IH l2 HN')].
Qed.
Lemma pfa_nd_perm : forall (l l' : list (Z * Z)), Permutation l l' -> NoDup l -> NoDup l'.
Proof. intros l l' HP HN. rewrite <- HP. exact HN. Qed.
Lemma pfa_lam_now : forall (L0 Fd Lam : list (Z * Z)) b, Permutation L0 (Fd ++ Lam) -> In b L0 -> ~ In b Fd -> In b Lam.
Proof.
intros L0 Fd Lam b HP Hb Hn. pose proof (Permutation_in _ HP Hb) as H2.
apply in_app_or in H2 as [H2|H2]; [contradiction | exact H2].
Qed.
Lemma pfa_U_srl3 : forall E x, U E (SAlu ALU_SRL x (SLit 3)) = U E x / 8.
Proof.
intros E x. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
replace (Z.land (zcanon 3) 63) with 3 by (vm_compute; reflexivity).
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. pose proof (U_range E x) as R. unfold M64 in R.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia|].
apply (Z.le_lt_trans _ (U E x)); [apply Z.div_le_upper_bound; lia | lia].
Qed.
(* glue another loop segment can use: the ASan cell (x >> 3) + the shadow offset of an application address below 2 ^ 47 *)
Lemma pfa_U_cell : forall E x bx xv, U E x = xv -> U E bx = SHADOW_OFF -> 0 <= xv < 2 ^ 47 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) bx) = xv / 8 + SHADOW_OFF.
Proof.
intros E x bx xv Hx Hb Hr. rewrite pfa_U_add, pfa_U_srl3, Hx, Hb.
assert (0 <= xv / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold SHADOW_OFF in *. apply Z.mod_small. lia.
Qed.

(* a register of a seated state, its symbolic value computed (the call form st_ok (setpc ss sigma) included: the
   symbolic register list is taken out of setpc before vm_compute, so no image term is computed) *)
Ltac pfa_reg HS r R :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as R;
    lazymatch type of R with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in R end
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as R;
    cbn [setpc ss_regs] in R;
    lazymatch type of R with _ = sv_denot _ (sr_get ?rs ?rr) =>
      let e' := eval vm_compute in (sr_get rs rr) in change (sr_get rs rr) with e' in R end
  end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
Context {PA : PAImg A_prog_listing}.
#[local] Notation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Existing Instance prh_img_A.
#[local] Existing Instance CfParams_preset.

(* ---- the footprint of harness blocks (glue another loop segment can use) ---- *)
Lemma pfa_inFP_hbl : forall (D : list (Z * Z)) a k x, In (a, k) D ->
  a - cf_head <= x < a - cf_head + req_size (k + cf_head) -> inFP (ablocks_fp (prhPj_hbl D)) x.
Proof.
intros D a k x Hin Hx. exists (a - cf_head, a - cf_head + req_size (k + cf_head)). split; [|cbn [fst snd]; lia].
unfold ablocks_fp, prhPj_hbl. rewrite map_map. apply in_map_iff. exists (a, k). split; [reflexivity | exact Hin].
Qed.
Lemma pfa_inFP_hbl_inv : forall (D : list (Z * Z)) x, inFP (ablocks_fp (prhPj_hbl D)) x ->
  exists a k, In (a, k) D /\ a - cf_head <= x < a - cf_head + req_size (k + cf_head).
Proof.
intros D x (r & Hr & Hx). unfold ablocks_fp, prhPj_hbl in Hr. rewrite map_map in Hr.
apply in_map_iff in Hr as ((a & k) & <- & Hin). cbn [fst snd] in Hx. exists a, k. split; [exact Hin | exact Hx].
Qed.
(* glue another loop segment can use *)
Lemma pfa_stk_ff : 0 <= STK_fuzz_free (PI := prh_img_A).
Proof. vm_compute. discriminate. Qed.

Section e.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx (@cf_head CP).
Variable Pm : (word -> option byte) -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).

(* ---- a harness block of the ledger: its bounds (glue another loop segment can use; image B's pj_free_glue.v pfg_lam_blk) ---- *)
Lemma pfa_lam_blk : forall ly S Hp W mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ 4096 + cf_head <= a /\ a + k <= YM05.alloc_ceiling /\ a mod 16 = 0 /\
  In (a - cf_head, k + cf_head) (ablocks B ly S) /\ In (a - cf_head) Hp.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HLd Hin.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLd Hin) as (Hk & Hab & Hhp & Ha16 & _).
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hcl & _).
change (@cf_head CP) with 16 in *.
pose proof (req_size_pos (k + 16) ltac:(lia)) as [_ Hrq].
repeat split; first [assumption | lia].
Qed.

(* ---- a harness block's user bytes: addressable, hull visible, in application memory, not the runtime's (glue
   another loop segment can use; image B's pfl_hb_vis) ---- *)
Lemma pfa_hb_vis : forall ly S Hp W mem md Lam peak cnt fail ran most own a k x n,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  a <= x -> x + n <= a + k -> 0 < n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x n /\ shadow_hull_vis (aview SEGS (w_H W) mem) x n /\
  amem_range x n /\ (forall y, x <= y < x + n -> ~ aowned B ly S y).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k x n HAR HL Hin H1 H2 Hn.
destruct (pfa_lam_blk ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin) as (Hk0 & Ha0 & Hak & _ & Hab & Hhp).
destruct (alx_hshadow SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab Hhp) as (Hbs & Hhv).
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & _ & Hcb & Happ & Hpo & _).
change (@cf_head CP) with 16 in *.
pose proof (req_size_pos (k + 16) ltac:(lia)) as [_ Hr1].
split; [exact (block_shadow_range _ SHADOW_OFF (a - 16 + 16) (req_size (k + 16) - 16) x n Hbs ltac:(lia) ltac:(lia))|].
split; [exact (shadow_hull_vis_sub_cf _ (a - 16 + 16) (req_size (k + 16) - 16) x n (Hhv ltac:(lia)) ltac:(lia) ltac:(lia))|].
split.
{ pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold in_app, amem_range, kLowShadowBeg, ASAN_CEIL in *. lia. }
intros y Hy. exact (proj2 (Hpo y ltac:(lia))).
Qed.

(* ---- two distinct harness blocks: the user bytes of one miss the allocator block of the other (glue another loop segment can use) ---- *)
Lemma pfa_hb_apart : forall ly S Hp W mem md Lam peak cnt fail ran most own a k a' k' x,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> In (a', k') Lam -> (a, k) <> (a', k') -> a <= x < a + k ->
  ~ (a' - cf_head <= x < a' - cf_head + req_size (k' + cf_head)).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k a' k' x HAR HL H1 H2 Hne Hx Hx'.
destruct (pfa_lam_blk ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL H1) as (Hk0 & Ha0 & Hak & _ & Hab & _).
destruct (pfa_lam_blk ly S Hp W mem md Lam peak cnt fail ran most own a' k' HAR HL H2) as (Hk0' & Ha0' & Hak' & _ & Hab' & _).
assert (Hne' : (a - cf_head, k + cf_head) <> (a' - cf_head, k' + cf_head)).
{ intros E. injection E as E1 E2. apply Hne. f_equal; lia. }
pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab Hab' Hne') as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
change (@cf_head CP) with 16 in *.
pose proof (req_size_pos (k + 16) ltac:(lia)) as [_ Hr1].
lia.
Qed.

(* ---- v's node misses the allocator block of every harness block of D in the ledger (glue another loop segment can use; image B's
   pfl_v_apart over A's three places of v) ---- *)
Lemma pfa_v_apart : forall en nd ly S Hp W mem md Lam peak cnt fail ran most own a k x,
  pf_vnode B en nd ly S Lam W mem -> ARx ly S Hp W mem md ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> In (a, k) (fe_D en) -> a - cf_head <= x < a - cf_head + req_size (k + cf_head) ->
  ~ (fe_v en <= x < fe_v en + 56).
Proof.
intros en nd ly S Hp W mem md Lam peak cnt fail ran most own a k x HVN HAR HL Hin HinD Hx Hv.
pose proof HVN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hplace).
destruct (pfa_lam_blk ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin) as (Hk0 & Ha0 & Hak & _ & Hab & _).
change (@cf_head CP) with 16 in *.
pose proof (req_size_pos (k + 16) ltac:(lia)) as [_ Hr1].
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & _ & Hcb & _).
destruct Hplace as [(a' & k' & Hin' & HnD & Ha' & Hk') | [(b & m & Hb & Hnl & Hb1 & Hb2) |
  (cid & pos & Hf & Hf1 & Hf2)]].
- assert (Hne : (a', k') <> (a, k)) by (intros E; rewrite E in HnD; exact (HnD HinD)).
  apply (pfa_hb_apart ly S Hp W mem md Lam peak cnt fail ran most own a' k' a k x HAR HL Hin' Hin Hne ltac:(lia)).
  change (@cf_head CP) with 16. lia.
- assert (Hne : (b, m) <> (a - 16, k + 16)).
  { intros E. injection E as E1 E2. apply Hnl.
    replace (b + 16) with a by lia. replace (m - 16) with k by lia. exact Hin. }
  pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hb Hab Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos m ltac:(lia)) as [_ Hr2]. lia.
- pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab Hf) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* ---- a stretch that stores nothing and keeps sp, gp, tp, s11 keeps pj_free's frame (glue another loop segment can use) ---- *)
(* over any world relation R (the frame's journal at R; the re-hiding move puts every cut after a free at wle');
   pfa_frame_same is its instance at wle *)
Lemma pfa_frame_sameR : forall (R : world SEGS -> world SEGS -> Prop) en ly S Hp W regs regs' mem md md' k,
  pf_frameR SK B ARx Pm R en ly S Hp W regs mem md k ->
  ajournal_xR (SK := SK) SEGS B PST ARx R (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] ly S Hp W mem md' k ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 27 = getr regs 27 ->
  pf_frameR SK B ARx Pm R en ly S Hp W regs' mem md' k.
Proof.
intros R en ly S Hp W regs regs' mem md md' k (HJ & HW & Hsp & HSV & HP & H3 & H4 & H27 & HR & HPm) HJ' E2 E3 E4 E27.
split; [exact HJ'|]. split; [exact HW|]. split; [unfold spZ; rewrite E2; exact Hsp|]. split; [exact HSV|].
split; [exact HP|]. split; [rewrite E3; exact H3|]. split; [rewrite E4; exact H4|]. split; [rewrite E27; exact H27|].
split; [exact HR | exact HPm].
Qed.
Lemma pfa_frame_same : forall en ly S Hp W regs regs' mem md md' k,
  pf_frame SK B ARx Pm en ly S Hp W regs mem md k ->
  AJ (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] ly S Hp W mem md' k ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 27 = getr regs 27 ->
  pf_frame SK B ARx Pm en ly S Hp W regs' mem md' k.
Proof. exact (pfa_frame_sameR (@wle SEGS)). Qed.
End e.
End d.
