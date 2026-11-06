(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module names changed; 689 of its 743 lines of code are new or changed and 724 lines of the source are left out. *)
(* fuzz_preset, image A' (asan, sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the LAST INNER SEGMENT of
   stretch CMP of round_trip_text's walk ON THE #102 PINS (lane CmpFF of RttCmp, WalkRtt102, the text owner):
   cmp_ff : rtt_seg RT_O2 rtt_at_o2 -> cf_head = PresetReqAt.HEAD ->
            from Rtt102CmpDefs.v's cut cmp_at_pn at +788 (RT_C3) to Rtt102Cut.v's RT_O2 (+808).
   RE-FITTED TO THE BATCH KIT'S CUT 7cdbb61b5fa0 on WalkRtt102b's shared layer 80a1d52c32c7: the text takes prh_cons_from at
   entry and states r = 0, so the cut is GRANTED ONLY - cmp_at_pn / cmp_out and rtt_rb have no refusal arm
   (parse_noting's ran-out outcome is refuted at its call, upstream of this segment), and the read-back blocks are
   stated up to permutation over the reader's own rd_blocks (passed through). The pre-cut form was green at
   5a13ff1076b (pins102 97c76900674).
   tfuzz_free_specX is in the POST-IMPLICATION form (no position at entry); fpre states frm_zero at entry (from the
   cut's rtt_fx).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma); the function-level lookup
   (proof-index round_trip_text EXIT=0, no released ASan proof) is the brief's.
   THE CODE (A' +0x314 .. +0x328, A' capstone listing :199-203):
     +788 mv s8, a0     ; +792 mv a0, s5 ; +796 jal __wrap_free    free (want): a live NON-harness block
     +800 mv a0, s6     ; +804 jal fuzz_free                        fuzz_free (q): the writer's harness block
     +808 = RT_O2
   THE WALK, AT THE RE-HIDING RELATION (R FORM): every step and call concludes YA0nH.SRr' SEGS RZ_cf, and every journal
   is at RZW := YA0nH.wle' SEGS RZ_cf (Rtt102Cut.v rtt_J). Concrete steps (Rtt102FR1KitA.v fr_addi / fr_jal); the direct
   free by YGcallx.v aj_free_at_x_ctR at R := RZW over the free row's call post APOST (AFREE : afree_realizes_xR, with
   the laws POST_AR / POST_J; its trace premise `admits` from the fixed membership rtt_trace_at gives,
   YCbqG.admits_ct_fix; its call memory's QMm from QMR at the cut's room, hull budget and read-only view; its caller
   journal at `[] ++ [the free's trace]`, whose fixed trace YCbqG.ajournal_xw_fix1R drops, which is Rtt102Cut.rtt_Jc at
   the call state); its memnorm keep from the call post by POST_MN (the leaf free_leaf_xA keeps only the raw frame,
   and the raw frame cannot give memnorm: owned statics lie in a read-only segment at preset, MemnormT.v:29-34); its
   room by PrhRoomFree.RF_free, the carried state by Rtt102FR1Kit.v rtt_free_keep; fuzz_free by the kit's fr_call_at
   at the kit's tfuzz_free_specX (taken at every float state: the call is made at the cut's fxc; its hull budget from the
   run's position, ff_hull), whose post is budgeted at its own FIXED trace (wbudget [trace] 0), read back as the plain
   post at wle' by PRH_Base.fpost_of_fpostb_fix (`eapply .. in Hb; [|exact Hfix]`); the carried state by
   rtt_carry_keep / rtt_copy_keep / rtt_back_keep.
   The read-back tree at back (F + 32), its free order (pj_foR, at DOC_D and at every depth bound) and K0-CAP's
   pj_ncapR are moved across both calls by ff_node_keep (Rtt102CmpLib.v rcl_nodeR_move), ff_fo_keep (PRH_PjOrder.v
   pj_foR_frame) and ff_ncap_keep (Rtt102Cut.v rtt_ncapR_agree: PRH_Reader.v has no frame lemma for pj_ncapR), over
   ff_foot_agree.
   THE MODEL-RUN POSITION: rtt_pre's prh_run_at .. (ck_rtt_evs ..) is split
   (PRH_Base.prh_run_at_app_iff) at RT_K_P D, where rt_text = w_evs ++ r_evs ++ parse_evs ++ r_free ++ w_free
   (lib/Spec/PresetReqAt.v:310-311) has HFr (last rcaps 0) then HFr (last wcaps 0 + HEAD) (:171, :115); cmp_at_pn gives
   cap = last rcaps 0 and capw = last wcaps 0 there, so PresetRoomPosKeep.room_pos_keep_free advances the position
   across free (want) and tfuzz_free_specX's post-implication arm (run event HFr (capw + cf_head)) across fuzz_free (q),
   to RT_K_T D.
   THE CLASS-24 BOUND: RF_free's rl_b24_ok at the free's call state from cmp_at_pn's ccnt24 bound
   (CfRoomLivePreset.preset_rl_b24_ok); tfuzz_free_specX's ccnt24 at its call state from the same bound and
   ff_ccnt24_drop (a free's block list loses one block, aj_free_at_x_ctR's post; ccnt24 counts the class-24 requests of
   the allocator's live blocks, which ablocks keeps).
   THE HULL BUDGET (both calls): PresetDrvHullA.drv_cf_hull_ok_at_call_A at the run's position and rtt_pre's last
   conjunct (at most 4 calls, Rtt102Cut.rtt_pre_os4), within CfParams_preset's caps (ff_hull).
   THE CfParams INSTANCE IS FIXED to CfParamsPreset.CfParams_preset (as Rtt102CmpA.v, the composition, fixes it).
   B IS A GENERIC Section variable: PAL : PALib B is a generic hypothesis; the A' instance is discharged at the binder
   of B, which has not yet run PALibCore. No as_code route at a fixed B in this file.
   Numerals: 788 / 792 / 796 / 800 / 804 / 808 (DERIVED: byte offsets inside round_trip_text, A' = B'); 1 / 10 / 21 /
   22 / 23 / 24 / 27 / 0 (WORD: register numbers); 0 / -1 (WORD: rc); 16384 (LENGTH: ASTACK), 192 / 104 (LENGTH: the
   frame below sp0), 2 ^ 31 / 2 ^ 40 / 2 ^ 64 (LENGTH); 24 (LENGTH: the batch class); 56 / 24 / 48 / 8 (LENGTH: the
   pj node layout of PRH_Reader.v pj_hdrR - node bytes, kids and cap offsets, key-pointer stride), 256 (LENGTH: a byte's
   range, ff_rd_u64_det). No ADDRESS literal: every pc is pa_sigma / pa_val of the listing. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf YG00cf YGcfRoom YO0f.
(* the re-hiding move's world relation and step relation (YA0nH), its step lemmas (YSRrG), the zone (YGcfRehidePost) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAtNoMiss PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetSecTotal PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetDrvHullA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnTx PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA S1Ledger Rtt102Cut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Rtt102FR1Kit Rtt102FR1KitA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Rtt102CmpLib Rtt102CmpDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* the listing offset of round_trip_text's entry (DERIVED: 4 * its slot) *)
Definition RTT_K : Z := 4 * Z.of_nat (A_prog_slot AS_round_trip_text).

(* a register that is not callee-saved (ra, a0) refutes acallee_saved, by computation of its index (S10Env ts_cs) *)
Ltac ff_not_cs Hr := unfold acallee_saved in Hr;
  lazymatch type of Hr with context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v in Hr end;
  lia.

(* ---- pure helpers ---- *)
Lemma ff_firstn1 : forall {A : Type} (l : list A) j e, firstn 1 (skipn j l) = [e] -> nth_error l j = Some e.
Proof.
intros A l. induction l as [|a l IH]; intros j e H.
- destruct j; cbn in H; discriminate.
- destruct j as [|j]; cbn in H |- *.
  + injection H as ->. reflexivity.
  + exact (IH j e H).
Qed.

(* the two frees' events of rt_text, read off the run at its entry position: the first as the run's event (for
   room_pos_keep_free), the second as a run segment (for tfuzz_free_specX's post-implication arm) *)
Lemma ff_run_ev : forall sm x os i (a b c rest : list PresetReqAt.hev) e1 e2,
  prh_run_at sm x os i ((a ++ b ++ c ++ [e1] ++ [e2]) ++ rest) ->
  nth_error (PresetRun.hruns sm x os) (i + (length a + length b + length c)) = Some e1 /\
  prh_run_at sm x os (Datatypes.S (i + (length a + length b + length c))) [e2].
Proof.
intros sm x os i a b c rest e1 e2 H.
apply prh_run_at_app_iff in H as [H _].
apply prh_run_at_app_iff in H as [_ H].
apply prh_run_at_app_iff in H as [_ H].
apply prh_run_at_app_iff in H as [_ H].
apply prh_run_at_app_iff in H as [H1 H2].
assert (E : (i + (length a + length b + length c))%nat = (i + length a + length b + length c)%nat) by lia.
rewrite E. split.
- exact (ff_firstn1 _ _ _ H1).
- replace (Datatypes.S (i + length a + length b + length c))
    with (i + length a + length b + length c + length [e1])%nat by (cbn [length]; lia).
  exact H2.
Qed.

Lemma ff_len5 : forall (a b c : list PresetReqAt.hev) e1 e2,
  length (a ++ b ++ c ++ [e1] ++ [e2]) = Datatypes.S (Datatypes.S (length a + length b + length c)).
Proof. intros a b c e1 e2. rewrite !length_app. cbn [length]. lia. Qed.

(* a list that holds x, and splits around it: the rest *)
Lemma ff_perm_drop : forall (l b1 b2 R : list (Z * Z)) x, Permutation l (x :: R) -> l = b1 ++ x :: b2 ->
  Permutation (b1 ++ b2) R.
Proof.
intros l b1 b2 R x HP E. subst l. apply Permutation_sym. eapply Permutation_cons_app_inv.
apply Permutation_sym. exact HP.
Qed.
Lemma ff_perm_drop_app : forall (l b1 b2 Dl R : list (Z * Z)) x, Permutation l (Dl ++ x :: R) ->
  l = b1 ++ x :: b2 -> Permutation (b1 ++ b2) (Dl ++ R).
Proof. intros l b1 b2 Dl R x HP E. subst l. eapply Permutation_app_inv. exact HP. Qed.

(* the realigned sp of round_trip_text (Rtt102Cut.v RT_R) below the entry sp0 *)
Lemma ff_sp1 : forall sp0, sp0 mod 16 = 0 ->
  sp0 - 192 <= RT_R sp0 <= sp0 - 160 /\ RT_R sp0 mod 32 = 0 /\ (RT_R sp0 - sp0) mod 16 = 0.
Proof.
intros sp0 H. unfold RT_R, RT_FRAME.
pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)) as Hm.
pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)) as Hd.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hd2. rewrite H in Hd2.
set (q1 := (sp0 - 160) / 32) in *. set (r1 := (sp0 - 160) mod 32) in *. set (q2 := sp0 / 16) in *.
clearbody q1 r1 q2.
split; [lia|]. split.
- replace (sp0 - 160 - r1) with (q1 * 32) by lia. apply Z_mod_mult.
- replace (sp0 - 160 - r1 - sp0) with ((2 * q1 - q2) * 16) by lia. apply Z_mod_mult.
Qed.

(* ======================================================================================================== *)
Section ff. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
Context {RF : PrhRoomFree (cp := CfParamsPreset.CfParams_preset) (RL := RL)}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Notation STKR := (@STK_round_trip_text prh_img_A).
#[local] Existing Instance prh_img_A.
(* the world relation of every journal of the walk (Rtt102Cut.v rtt_J) and the step relation's zone *)
#[local] Notation RZ := YGcfRehidePost.RZ_cf.
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variables (CTX0 : list (list Z)).
(* the cut's predicates, every instance / implicit state argument BY NAME (the text owner's statement-trap rule,
   2026-10-29: fxc and fx' are second FPStates in scope) *)
#[local] Notation PRE := (rtt_pre (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx CTX0).
#[local] Notation RJ := (rtt_J (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation RCARRY := (rtt_carry (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation RSEG := (rtt_seg (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK CTX0).
#[local] Notation AT_O2 := (rtt_at_o2 (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation POST := (rtt_post (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation CMP_PN := (cmp_at_pn (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).

(* ---- THE CLASS-24 COUNT ACROSS A FREE: ccnt24 counts the class-24 requests of the allocator's live blocks
   (YGcfRoomLive.v:1141), and ablocks keeps each block's request (YG0d.v:421-422), so a block list that loses one
   block does not raise it ---- *)
Lemma ff_ccnt24_drop : forall ly S ly2 S2 (l1 l2 : list (Z * Z)) x,
  ablocks B ly S = l1 ++ x :: l2 -> ablocks B ly2 S2 = l1 ++ l2 ->
  YGcfRoomLive.ccnt24 S2 <= YGcfRoomLive.ccnt24 S.
Proof.
intros ly S ly2 S2 l1 l2 x E1 E2.
assert (M : forall ly0 S0, map snd (blocks S0) = map snd (ablocks B ly0 S0))
  by (intros ly0 S0; unfold ablocks; rewrite map_map; reflexivity).
unfold YGcfRoomLive.ccnt24, PresetRoom.ccnt. rewrite (M ly S), (M ly2 S2), E1, E2.
rewrite !map_app, !filter_app, !length_app. cbn [List.map List.filter].
(* the dropped block's request counts 1 or 0; closed in nat (no lia: Nat2Z.inj_le, then monotonicity) *)
match goal with |- context [if ?c then _ else _] => destruct c end; cbn [List.length];
  apply Nat2Z.inj_le; first [apply Nat.le_refl | apply Nat.add_le_mono_l, Nat.le_succ_diag_r].
Qed.

(* ---- Section hypotheses (the brief's categories; each with its owner; Rtt102CmpA.v passes them by position) ---- *)
(* (a) the allocator laws at the cf instance's head (engine fold, YCbqG.v AR_laws_x) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* (a) MARKED STAND-IN (owned by the kit / the core's PALib): the unit's image binding of B, generic here *)
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.
(* (a) the free wrapper's call form and model (YGcallx.v Sections r / rR, as aj_free_at_x_ctR takes them; the model
   free is the cf instance owner's free_cf). At the cf instance (YGcallcf.v, ARx := ARcf /\ xs_placed_cf): QM := QM_cf, QMm :=
   QMm_cf, mt := malloc_cf, nmax := cf_malloc_max, WFx := Wf_cf (as_universe B); WFL by ARx_wf_law_xs, AMX by
   alloc_model_laws_x_cf, QMQ by QMQ_cf. OWNLOW is gone: aj_free_at_x_ctR reads the call's journal off POST_J (the
   cf instance's POST_J_cf_keep takes it there) *)
Variable QM : astate -> Prop.
Variable QMm : astate -> (word -> option byte) -> Prop.
Variable mt : Z -> list Z -> YG00.M sptr.
Variable nmax : Z.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis AMX : alloc_model_laws_x B QM mt nmax YG00cf.free_cf WFx.
Hypothesis QMQ : forall S mem, QMm S mem -> QM S.
(* (a) the free wrapper's call post under the re-hide and its three laws (YGcallx.v Section rR: POST_AR / POST_J; and
   the memnorm keep, which the leaf free_leaf_xA no longer carries). At the cf instance: APOST :=
   YGcallMxmnKeep.APOST_cf_keep, POST_AR := POST_AR_cf_keep, POST_J := POST_J_cf_keep (LAWS segs_low errno_low
   OWNLOW), POST_MN := fun .. H => proj2 H *)
Variable APOST : Z -> alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.
Hypothesis POST_AR : apost_ar_law SEGS ARx APOST.
Hypothesis POST_J : apost_j_law (rc := rc) (SK := SK) SEGS B ARx RZW APOST.
Hypothesis POST_MN : forall stk ly S Hp W regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md',
  APOST stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
  YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem'.
(* (a) the free wrapper's text (owner: the cf instance owner) under the re-hide, at any float state. At the cf instance:
   YGcallMxmnKeep.afree_realizes_x_cf_rh_keep from YGcfMallocComposeKeep.afree_realizes_cf_rh_keep *)
Hypothesis AFREE : forall fx' : YK11.FPState,
  afree_realizes_xR (fx := fx') SEGS B ARx QMm YG00cf.free_cf RZW APOST.
(* (a) by the cf instance owner: the call's trailing conjuncts on the state and the call memory, from the non-primary room, the
   hull budget and the read-only view. At the cf instance: YGcallcf.QMm_cf_of_room with YGcfRoomLive.room_live_room,
   cf_hull_ok from hull_budget S [] (CfParams_preset's cf_hull_ok is that meter) and arodata_ok_cf from
   YGcfAroBridge.arodata_ok_cf_of_P *)
Hypothesis QMR : forall ly S Hp W mem md, ARx ly S Hp W mem md -> qtight S -> room_live_cf S ->
  PresetHullBudget.hull_budget S [] ->
  arodata_okP SEGS (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA) B (aview SEGS (w_H W) mem) ->
  QMm S mem.
(* (a) by the cf instance owner: the generic call form is the cf instance's, so RF_free and PresetRoomPosKeep's free keep apply.
   At the cf instance: YGcallcf.acall_pre_x_xs_cf *)
Hypothesis ACF : forall ly S Hp W regs mem md ch, acall_pre_x SEGS B ARx QMm ly S Hp W regs mem md ch ->
  YG0dcf.acall_pre_cf SEGS B ly S Hp W regs mem md ch.
(* (c) MARKED STAND-IN (owned by the kit, the image binding of B): alloc.c's statics are not the runtime's own statics *)
Hypothesis pal_pst_static : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* (a) PRH_Base.v prh_head_wide (the preset instance has cf_head = 16) *)
Hypothesis HW : prh_head_wide.
(* (b) the callee's kit text, fuzz_free (PRH_FnAlloc.v), at every float state: the call is made at the cut's fxc *)
Hypothesis TFF : forall fx' : YK11.FPState,
  @tfuzz_free_specX fx' rc CfParamsPreset.CfParams_preset prh_img_A RL A_prog_listing PA B ARx SK.

Lemma ff_sigma : SIGMA AS_round_trip_text = BASE + RTT_K.
Proof. vm_compute. reflexivity. Qed.

(* THE HULL BUDGET at an allocator call of the walk: the run's position and its at most 4 calls bound both meters
   (PresetDrvHullA.drv_cf_hull_ok_at_call_A), and the run's caps are within CfParams_preset's (by computation) *)
Lemma ff_hull : forall sm x os i H0 hist S, (length os <= 4)%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PresetHullBudget.hull_budget S [].
Proof.
intros sm x os i H0 hist S Hl Hp.
destruct (PresetDrvHullA.drv_cf_hull_ok_at_call_A sm x os i H0 hist S Hl Hp) as [HN HT].
assert (HC : PresetSecTotal.SEC_N_CAP <= @YGcfNames.cf_kmax CfParamsPreset.CfParams_preset /\
  PresetSecTotal.SEC_T_CAP <= @YGcfNames.cf_T_max CfParamsPreset.CfParams_preset) by (vm_compute; split; discriminate).
destruct HC as [HCN HCT]. rewrite PresetRoomPos.rp_nsec_layer in HN.
unfold PresetHullBudget.hull_budget. cbv [PresetSecTotal.nsec PresetRun.nprodR]. cbn [PresetSecTotal.tsec].
lia.
Qed.

(* ---- the read-back tree's footprint at back (F + 32) across a call whose keeps are rtt_kept: the two memories agree
   on it (bytes kept, footprint present after) - what the tree (pj_nodeR) and its free order (pj_foR) both read ---- *)
Lemma ff_foot_agree : forall D fxc lyc Sc Hpc Wc regsc memc mdc kc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos slo shi E P
    Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2 Db,
  RCARRY D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ->
  RCARRY D fxc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos ->
  rtt_kept (L := A_prog_listing) (PA := PA) B lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E P ->
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  incl Db Lamc -> incl Db Lam2 ->
  (forall x, E x -> ~ in_zr x (frame_rng lyc (RT_CID, pos))) ->
  (forall x, E x -> forall a k, In (a, k) Db -> ~ (a - cf_head <= x < a - cf_head + req_size (k + cf_head))) ->
  frame_addr ly2 RT_CID pos = frame_addr lyc RT_CID pos /\
  pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (pj_footR (frame_addr lyc RT_CID pos + RT_BACK) Db).
Proof.
intros D fxc lyc Sc Hpc Wc regsc memc mdc kc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos slo shi E P
  Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2 Db HC HC2 HK HLc HL2 HDc HD2 HEfr HEdb.
pose proof HC as (_ & HJc & (Efr & _ & _ & _) & _).
pose proof HC2 as (_ & HJ2 & (_ & _ & _ & Hpr2) & _).
pose proof HJ2 as (HAR2 & _).
destruct (rtt_fa_eq B ARx SK D lyc Sc Hpc Wc memc mdc kc pos HJc) as (Fac & _).
destruct (rtt_fa_eq B ARx SK D ly2 S2 Hp2 W2 mem2 md2 k2 pos HJ2) as (Fa2 & _).
assert (EF : frame_addr ly2 RT_CID pos = frame_addr lyc RT_CID pos) by (rewrite Fa2, Fac; reflexivity).
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
pose proof HK as (_ & K2 & _ & K4).
assert (Hin : In (RT_CID, pos) (frames Sc)) by (rewrite Efr; left; reflexivity).
pose proof cf_head_nonneg as Hch0.
split; [exact EF|].
intros x Hx. split.
- apply mbyte_of_aview. destruct Hx as [Hx | ((a, kk) & HinD & Hx)].
  + apply (K4 RT_CID pos x Hin).
    * left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efs1. unfold RT_BACK in Hx. lia.
    * intros HE. apply (HEfr x HE). unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efs1. unfold RT_BACK in Hx. lia.
  + unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    destruct (prh_ledger_hblock (PI := prh_img_A) B _ _ _ _ _ _ _ _ _ _ a kk _ _ HLc (HDc _ HinD)) as (Hk0 & Hbc & _).
    destruct (prh_ledger_hblock (PI := prh_img_A) B _ _ _ _ _ _ _ _ _ _ a kk _ _ HL2 (HD2 _ HinD)) as (_ & Hb2 & _).
    assert (Hrq : 1 <= req_size (kk + cf_head) /\ kk + cf_head <= req_size (kk + cf_head)) by (apply req_size_pos; lia).
    replace x with (a - cf_head + (x - (a - cf_head))) by lia.
    apply (K2 (a - cf_head) (kk + cf_head) (x - (a - cf_head)) Hbc Hb2); [lia|].
    intros HE. apply (HEdb _ HE a kk HinD). lia.
- intros _. apply apresent_writable.
  eapply (rcl_foot_present B ARx LAWS HW); [exact HAR2 | exact HL2 | exact HD2 | | exact Hx].
  intros y Hy. apply Hpr2. rewrite EF, Efs1. unfold RT_BACK in Hy. lia.
Qed.

(* the read-back tree at back, across such a call (Rtt102CmpLib.v rcl_nodeR_move) *)
Lemma ff_node_keep : forall D fxc lyc Sc Hpc Wc regsc memc mdc kc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos slo shi E P
    Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2 t Db,
  RCARRY D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ->
  RCARRY D fxc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos ->
  rtt_kept (L := A_prog_listing) (PA := PA) B lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E P ->
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  incl Db Lamc -> incl Db Lam2 ->
  (forall x, E x -> ~ in_zr x (frame_rng lyc (RT_CID, pos))) ->
  (forall x, E x -> forall a k, In (a, k) Db -> ~ (a - cf_head <= x < a - cf_head + req_size (k + cf_head))) ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc RT_CID pos + RT_BACK) t Db ->
  pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) (frame_addr ly2 RT_CID pos + RT_BACK) t Db.
Proof.
intros D fxc lyc Sc Hpc Wc regsc memc mdc kc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos slo shi E P
  Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2 t Db HC HC2 HK HLc HL2 HDc HD2 HEfr HEdb HN.
destruct (ff_foot_agree D fxc lyc Sc Hpc Wc regsc memc mdc kc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos slo shi E P
  Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2 Db HC HC2 HK HLc HL2 HDc HD2 HEfr HEdb)
  as (EF & HA).
rewrite EF.
apply (rcl_nodeR_move SEGS t _ _ (prh_lin Lamc) (prh_lin Lam2) _ Db HN HA).
intros a kk HinD _. unfold prh_lin. exact (HD2 _ HinD).
Qed.

(* the read-back tree's free order at back, across such a call (PRH_PjOrder.v:298 pj_foR_frame) *)
Lemma ff_fo_keep : forall D fxc lyc Sc Hpc Wc regsc memc mdc kc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos slo shi E P
    Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2 (d : nat) Db (FL : list Z),
  RCARRY D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ->
  RCARRY D fxc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos ->
  rtt_kept (L := A_prog_listing) (PA := PA) B lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E P ->
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  incl Db Lamc -> incl Db Lam2 ->
  (forall x, E x -> ~ in_zr x (frame_rng lyc (RT_CID, pos))) ->
  (forall x, E x -> forall a k, In (a, k) Db -> ~ (a - cf_head <= x < a - cf_head + req_size (k + cf_head))) ->
  (exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) d (frame_addr lyc RT_CID pos + RT_BACK)
     Db F /\ map (fun b => snd b + cf_head) F = FL) ->
  exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) d (frame_addr ly2 RT_CID pos + RT_BACK)
     Db F /\ map (fun b => snd b + cf_head) F = FL.
Proof.
intros D fxc lyc Sc Hpc Wc regsc memc mdc kc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos slo shi E P
  Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2 d Db FL HC HC2 HK HLc HL2 HDc HD2 HEfr
  HEdb (F & HF & EF0).
destruct (ff_foot_agree D fxc lyc Sc Hpc Wc regsc memc mdc kc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos slo shi E P
  Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2 Db HC HC2 HK HLc HL2 HDc HD2 HEfr HEdb)
  as (EF & HA).
exists F. split; [|exact EF0].
rewrite EF.
apply (PRH_PjOrder.pj_foR_frame SEGS d _ _ (prh_lin Lamc) (prh_lin Lam2) _ Db F HF); [|exact HA].
intros a kk HinD. unfold prh_lin. exact (HD2 _ HinD).
Qed.

(* K0-CAP of the read-back tree at back, across such a call (Rtt102Cut.v rtt_ncapR_agree over ff_foot_agree) *)
Lemma ff_ncap_keep : forall D fxc lyc Sc Hpc Wc regsc memc mdc kc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos slo shi E P
    Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2 t Db,
  RCARRY D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ->
  RCARRY D fxc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos ->
  rtt_kept (L := A_prog_listing) (PA := PA) B lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E P ->
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  incl Db Lamc -> incl Db Lam2 ->
  (forall x, E x -> ~ in_zr x (frame_rng lyc (RT_CID, pos))) ->
  (forall x, E x -> forall a k, In (a, k) Db -> ~ (a - cf_head <= x < a - cf_head + req_size (k + cf_head))) ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc RT_CID pos + RT_BACK) t Db ->
  pj_ncapR SEGS (mrestrict (w_H Wc) memc) (frame_addr lyc RT_CID pos + RT_BACK) t ->
  pj_ncapR SEGS (mrestrict (w_H W2) mem2) (frame_addr ly2 RT_CID pos + RT_BACK) t.
Proof.
intros D fxc lyc Sc Hpc Wc regsc memc mdc kc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos slo shi E P
  Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2 t Db HC HC2 HK HLc HL2 HDc HD2 HEfr HEdb
  HN HNC.
destruct (ff_foot_agree D fxc lyc Sc Hpc Wc regsc memc mdc kc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos slo shi E P
  Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2 Db HC HC2 HK HLc HL2 HDc HD2 HEfr HEdb)
  as (EF & HA).
rewrite EF. exact (rtt_ncapR_agree SEGS t _ _ _ _ Db HN HNC HA).
Qed.

(* ---- THE INNER CUT at +800 (free (want) has returned): cmp_at_pn's state with want's block gone; X is the text's
   block alone; the class-24 count bounded (fuzz_free's entry premise); the exact model-run position after free (want),
   with the writer's capacity the model's (the cut is granted only) ---- *)
Definition ff_mid (D : rtt_in) (fxc : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k pos : Z) : Prop :=
  RCARRY D fxc ly S Hp W regs mem md k pos /\ rtt_back ly W mem pos /\
  getr regs 27 = w64 (SIGMA AS_round_trip_text + RT_O1 + RT_S11) /\
  rtt_copy_kept D W mem /\ getr regs 23 = w64 (frame_addr ly RT_CID pos + RT_BACK) /\
  exists q capw rc0 Lamp peakp cntp ranp,
    getr regs 22 = w64 q /\ getr regs 24 = w64 rc0 /\ q <> 0 /\
    rtt_led (PI := prh_img_A) B D ly S Hp W mem Lamp peakp cntp ranp 0 /\
    ~ In (q - cf_head, capw + cf_head) (ablocks B (ri_ly D) (ri_S D)) /\
    cmp_out B D ly S W mem pos rc0 Lamp cntp ranp [(q - cf_head, capw + cf_head)] [(q, capw)] /\
    YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
    rtt_pos D S (Datatypes.S (RT_K_P D)) /\ capw = last (PresetReqAt.wcaps (ri_t D) (ri_p D)) 0.

(* ======================================================================================================== *)
(* ---- THE TAIL: from +800, fuzz_free (q), to RT_O2 ---- *)
Lemma ff_tail : RSEG RT_O2 AT_O2 -> cf_head = PresetReqAt.HEAD ->
  forall D, PRE D -> forall fxc ly S Hp W regs mem md k pos, ff_mid D fxc ly S Hp W regs mem md k pos ->
  YA0nH.SRr' SEGS RZ W (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (RTT_K + RT_C4))) mem (YK11.seg_rom SEGS)) md)
    (POST D).
Proof.
intros SO2 HHEAD D HP fxc ly S Hp W regs mem md k pos HM.
destruct HM as (HC & HBK & HS11 & HCK & R23 & (q & capw & rc0 & Lamp & peakp & cntp & ranp & R22 & R24 & Hq0 & HLED &
  Hqnew & HOUT & H24 & HGRp)).
pose proof (@pa_segs_low _ A_prog_listing PA) as Hsegs.
pose proof (rtt_pre_facts (fx := fx) B ARx CTX0 D HP) as (HAR0 & Hsp0 & Hsp16 & H64 & HDL & _ & _ & _).
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrun & Hran0 & _).
pose proof HC as (HFX & HJ & HFR & HSV & HCR & HMN & HROD & HROOM & HNODE & HVIS).
pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
pose proof HJ as (HAR & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hstkf : 0 <= @STK_fuzz_free prh_img_A /\ @STK_fuzz_free prh_img_A + 192 <= STKR)
  by (split; apply Z.leb_le; vm_compute; reflexivity).
destruct (ff_sp1 (ri_sp D) Hsp16) as (Hsp1 & Hsp32 & Ho16).
set (sp0 := ri_sp D) in *. set (sp1 := RT_R sp0) in *.
(* lia reads a set name as an atom: the two equations relate it to the terms the kit's statements produce *)
assert (Esp0 : sp0 = ri_sp D) by reflexivity. assert (Esp1 : sp1 = RT_R (ri_sp D)) by reflexivity.
assert (Hwc : 0 <= PjWriteHyp.wcalls (ri_t D) (ri_p D)) by (unfold PjWriteHyp.wcalls; lia).
pose proof (Nat2Z.is_nonneg (PjRoundTrip.tcalls (ri_t D))) as Htc.
unfold cmp_out in HOUT. cbv zeta in HOUT. cbn [app] in HOUT.
destruct HOUT as (Hr0 & Hrc & Hcnt & Db & HPL & HDbn & HDbsz & HDbtb & HDbfo & HDblen & HPA & HNB & HDbfoK & HNC).
assert (Hrc0 : - 2 ^ 31 <= rc0 < 2 ^ 31) by (rewrite Hrc; lia).
assert (HqL : In (q, capw) Lamp).
{ apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. right. left. reflexivity. }
assert (HincL : incl (ri_Lam D) Lamp).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. right. right. exact Hbk. }
assert (Hqb : In (q - cf_head, capw + cf_head) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HPA)). left. reflexivity. }
(* fuzz_free's hull budget at its call state (the run's position after free (want), ff_hull) *)
assert (HHULL : PresetHullBudget.hull_budget S []).
{ destruct HGRp as ((hist2 & HPOS2) & _).
  exact (ff_hull _ _ _ _ _ _ S (rtt_pre_os4 (fx := fx) B ARx CTX0 D HP) HPOS2). }
unfold RT_C4.
(* +800 mv a0, s6 *)
eapply (fr_addi (fx := fxc) W regs mem md _ _ (RTT_K + 800) _ _ _ 10%bv 22%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | unfold RTT_K; vm_compute; discriminate | unfold RTT_K; vm_compute; reflexivity |].
intros mat1.
(* +804 jal fuzz_free *)
eapply (fr_jal (fx := fxc) W _ mem _ _ _ (RTT_K + 800 + 4) (SIGMA AS_fuzz_free));
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | unfold RTT_K; vm_compute; discriminate | unfold RTT_K; vm_compute; reflexivity | vm_compute; reflexivity |].
intros mat2.
match goal with |- YA0nH.SRr' _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ => set (regsF := r); set (mdF := m) end.
assert (HJm : RJ D ly S Hp W mem mdF k pos).
{ unfold mdF. apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW).
  apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW). exact HJ. }
pose proof (ajxR_ar HJm) as HARm.
assert (HC2 : RCARRY D fxc ly S Hp W regs mem mdF k pos)
  by exact (rtt_carry_md (fx := fx) B ARx SK D fxc ly S Hp W regs mem md k pos mdF HC HJm).
(* the call's registers *)
assert (F10 : getr regsF 10 = w64 q).
{ unfold regsF. rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac. rewrite R22.
  unfold v_addi, w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (FK : forall r : bv 5, r <> 1%bv -> r <> 10%bv -> getr regsF r = getr regs r).
{ intros r H1 H10. unfold regsF. rewrite getr_other by exact H1. rewrite getr_other by exact H10. reflexivity. }
assert (F2 : spZ regsF = sp0 + (sp1 - sp0)).
{ unfold spZ. rewrite FK by reg_neq_tac. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (F8 : s0Z regsF = sp0).
{ unfold s0Z. rewrite FK by reg_neq_tac. rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
assert (F1 : getr regsF 1 = Z_to_bv 64 (BASE + (RTT_K + 808))).
{ unfold regsF. rewrite getr_same by reg_neq_tac. f_equal; lia. }
assert (HRA : YK0s.ret_ok (Z_to_bv 64 (BASE + (RTT_K + 808)))).
{ apply (ret_ok_codeptr_v (PI := PA)); unfold RTT_K; vm_compute; [split; [discriminate | reflexivity] | reflexivity]. }
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (RTT_K + 808)))) by (vm_compute; discriminate).
assert (HRAc : bv_unsigned (Z_to_bv 64 (BASE + (RTT_K + 808))) < YM05.alloc_ceiling).
{ assert (E : bv_unsigned (Z_to_bv 64 (BASE + (RTT_K + 808))) < 2 ^ 40) by (vm_compute; reflexivity). lia. }
destruct (rtt_chain_at (fx := fx) B ARx SK CTX0 rtt_stkr_A D ly S Hp W mem mdF k pos sp1 HP HJm HSV ltac:(lia))
  as (ch1 & Hach & Hch1).
assert (Eq0 : (q =? 0) = false) by (apply Z.eqb_neq; exact Hq0).
set (FP1 := ablocks_fp [(q - cf_head, capw + cf_head)]).
(* fuzz_free's trace is a FIXED one (the closure's frame-pointer clause at round_trip_text's context) *)
assert (Hfix : In (call_trace ly (pc_free_ra0 (as_code B)) regsF ch1) (as_universe B)).
{ apply (rtt_trace_at (fx := fx) B ARx CTX0 rtt_fp_A D ly regsF ch1 (bv_unsigned (Z_to_bv 64 (BASE + (RTT_K + 808))))
    RT_fuzz_free HP Hch1).
  - unfold raZ. rewrite F1. reflexivity.
  - vm_compute. right. left. reflexivity. }
eapply (YSRrG.SRr'_bind SEGS RZ).
{ eapply (fr_call_at B ARx SK LAWS W regsF mem STKR sp0 (ri_FP D) (ri_ly D) (set_depot (st_depot S) (ri_S D)) (ri_Hp D)
    (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)] ly S Hp mdF k (@STK_fuzz_free prh_img_A) FP1 (sp1 - sp0)
    (Z_to_bv 64 (BASE + (RTT_K + 808))) ch1 (SIGMA AS_fuzz_free)).
  - exact HJm.
  - exact F2.
  - exact Ho16.
  - lia.
  - lia.
  - lia.
  - rewrite FK by reg_neq_tac. exact R3.
  - rewrite FK by reg_neq_tac. exact R4.
  - exact F1.
  - exact HRA.
  - exact HRA4.
  - replace (sp0 + (sp1 - sp0)) with sp1 by lia. rewrite F8. exact Hach.
  - intros HAF.
    pose proof (TFF fxc (ri_most D) 0 ly S Hp W regsF mem mdF ch1 q capw Lamp peakp cntp SIZE_MAXZ ranp) as HT.
    rewrite Eq0 in HT.
    (* the text's post is budgeted at the call's own trace, which is FIXED: the plain post back
       (PRH_Base.fpost_of_fpostb_fix) *)
    eapply (YSRrG.SRr'_mono SEGS RZ).
    { apply HT.
      + split; [exact HAF|]. split; [exact HROD|]. split.
        * rewrite F2. replace (sp0 + (sp1 - sp0)) with sp1 by lia. rewrite Eshi. lia.
        * split; [unfold raZ; rewrite F1; exact HRAc|].
          (* fpre's K0-FRM0-ENTRY: the cut's float state has rounding mode 0 (rtt_fx) *)
          exact (proj1 HFX).
      + intros _. exact HROOM.
      + intros _. exact H24.
      + intros _. exact HHULL.
      + (* the trace's admission, from its fixed membership (YCbqG.admits_ct_fix) *)
        apply admits_ct_fix. exact Hfix.
      + exact F10.
      + right. exact HqL.
      + exact (proj1 HLED). }
    intros W' c' _ Hb. eapply fpost_of_fpostb_fix in Hb; [exact Hb | exact Hfix].
  - (* the footprint is q's block, made since the entry *)
    intros a Ha. right. left. unfold FP1, ablocks_fp in Ha. destruct Ha as (rg & [<- | []] & Ha). cbn [fst snd] in Ha.
    exists (q - cf_head), (capw + cf_head). split; [exact Hqb|]. split; [exact Hqnew | lia]. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k1 & -> & HJ3 & HJ1 & HP3 & (HQ & HMN3)).
destruct HQ as (HRL3i & _ & _ & Hadv & _ & _ &
  [(Hq0' & _) | (_ & EHp3 & _ & (b1 & b2 & Eb1 & Eb2) & (l1 & l2 & EL & HL3))]); [exfalso; exact (Hq0 Hq0')|].
pose proof (HRL3i Hq0) as HRL3.
replace (BASE + (RTT_K + 808)) with (SIGMA AS_round_trip_text + RT_O2) by (rewrite ff_sigma; unfold RT_O2; lia).
(* the kept facts *)
assert (Hcl : ~ YI16.sink_open_fp FP1).
{ apply sink_closed_ablocks_fp. constructor; [cbn [fst]|constructor].
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem mdF _ _ HARm Hqb) as (_ & H4096 & _). lia. }
pose proof (rtt_kept_of_journal B ARx SK STK_fuzz_free (sp0 + (sp1 - sp0)) FP1 ly S Hp W mem mdF ly3 S3 Hp3 W3 mem3 md3 k1
  HJ1 Hcl) as HK.
(* the caller's journal is the call rule's from rtt_J at S (rtt_Jc at S); at the new state it is rtt_J again *)
assert (HJ3r : RJ D ly3 S3 Hp3 W3 mem3 md3 (k + k1) pos)
  by exact (rtt_J_of_Jc B ARx SK D S ly3 S3 Hp3 W3 mem3 md3 (k + k1) pos HJ3).
replace (sp0 + (sp1 - sp0)) with sp1 in HK by lia.
assert (HEoff : forall x, inFP FP1 x -> rtt_off D ly S x).
{ intros x (rg & [<- | []] & Hx). cbn [fst snd] in Hx.
  eapply (rtt_newblk_off (fx := fx) B ARx SK CTX0 LAWS D ly S Hp W mem mdF k pos);
    [exact HP | exact HJm | exact (proj1 HLED) | exact HincL | exact Hqb | exact Hqnew | lia]. }
assert (HPL3 : Permutation (l1 ++ l2) (Db ++ ri_Lam D)) by exact (ff_perm_drop_app Lamp l1 l2 Db (ri_Lam D) (q, capw) HPL EL).
assert (HincL3 : incl (ri_Lam D) (l1 ++ l2)).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL3)). apply in_or_app. right. exact Hbk. }
destruct (rtt_fa_eq B ARx SK D ly3 S3 Hp3 W3 mem3 md3 (k + k1) pos HJ3r) as (Fa3 & _).
destruct (rtt_fa_eq B ARx SK D ly S Hp W mem mdF k pos HJm) as (Fac & _).
assert (KP : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr regs r).
{ intros r Hr. rewrite (ts_ap _ _ r HP3 Hr). apply FK; intros E; subst r; ff_not_cs Hr. }
assert (HCR3 : rtt_cregs B D ly3 regs3 pos).
{ unfold rtt_cregs. rewrite Fa3. rewrite Fac in R18, R25, R26.
  rewrite !KP by ts_cs.
  repeat split; assumption. }
assert (HFR3 : frames S3 = frames S) by exact (ajxR_frs HJ1).
assert (HC3 : RCARRY D fxc ly3 S3 Hp3 W3 regs3 mem3 md3 (k + k1) pos)
  by (eapply (rtt_carry_keep (fx := fx) B ARx SK CTX0 LAWS pst_not_ro_A rtt_stkr_A D fxc ly S Hp W regs mem mdF k pos
        ly3 S3 Hp3
        W3 regs3 mem3 md3 (k + k1) (sp1 - STK_fuzz_free) sp1 (inFP FP1) PST);
      [exact HP | exact HC2 | exact HJ3 | exact HFR3 | exact HK | lia | exact (fun a Ha => Ha) | exact HEoff
      | exact (proj1 HLED) | exact HincL | exact HL3 | exact HincL3 | exact HCR3 | exact HMN3 | exact HRL3]).
assert (HEsh : forall x, inFP FP1 x ->
  ~ in_zr x (shadow_addr (frame_addr ly RT_CID pos), fs_frame_bytes RT_CID / 8)).
{ intros x (rg & [<- | []] & Hx). cbn [fst snd] in Hx.
  exact (rtt_blk_off_sh B ARx LAWS ly S Hp W mem mdF _ _ x HARm Hqb Hx RT_CID pos
    ltac:(pose proof HFR as (Efr & _); rewrite Efr; left; reflexivity)). }
assert (HBK3 : rtt_back ly3 W3 mem3 pos).
{ apply (rtt_back_keep (fx := fx) B ARx SK LAWS D fxc ly S Hp W regs mem mdF k pos ly3 S3 W3 mem3 _ _ (inFP FP1) PST
    HC2 HK HEsh);
    [|exact HBK].
  intros cid pos'. rewrite Fa3, Fac. reflexivity. }
assert (HCK3 : rtt_copy_kept D W3 mem3)
  by exact (rtt_copy_keep (fx := fx) B ARx SK CTX0 D fxc ly S Hp W regs mem mdF k pos ly3 S3 W3 mem3 _ _ _ _ HP HC2 HK
    HEoff HCK).
assert (R233 : getr regs3 23 = w64 (frame_addr ly3 RT_CID pos + RT_BACK)).
{ rewrite KP by ts_cs. rewrite R23. rewrite Fa3, Fac. reflexivity. }
assert (R243 : getr regs3 24 = w64 rc0) by (rewrite KP by ts_cs; exact R24).
assert (HS113 : rtt_s11 regs3) by (unfold rtt_s11; rewrite KP by ts_cs; exact HS11).
apply (SO2 D HP fxc ly3 S3 Hp3 W3 regs3 mem3 md3 (k + k1) pos).
split; [exact HC3|]. split; [exact HBK3|]. split; [exact HS113|]. split; [exact HCK3|]. split; [exact R233|].
exists rc0, (l1 ++ l2), peakp, cntp, ranp.
split; [exact R243|]. split; [exact Hrc0|].
split; [split; [exact HL3 | exact (proj2 HLED)]|].
unfold rtt_rb. cbv zeta.
(* the reading's tree at back, the position advanced by the two frees (the cut is granted only) *)
destruct HGRp as ((hist2 & HPOS2) & Ecapw).
rewrite Nat.add_succ_r in HPOS2.
destruct (ff_run_ev _ _ _ _ (PresetReqAt.w_evs (ri_t D) (ri_p D)) (PresetReqAt.r_evs (ri_t D) (ri_p D))
   (PresetReqAt.parse_evs ReaderRes.jr_strtod (ri_tb D) [])
   (if ri_copy D =? 0 then [PresetReqAt.HBulk (PresetReqAt.fo (ri_t D))] else [])
   (PresetReqAt.HFr (last (PresetReqAt.rcaps (ri_t D) (ri_p D)) 0))
   (PresetReqAt.HFr (last (PresetReqAt.wcaps (ri_t D) (ri_p D)) 0 + PresetReqAt.HEAD)) Hrun) as (_ & Ev2).
assert (Ev2' : prh_run_at ReaderRes.jr_strtod (ri_x D) (ri_os D) (Datatypes.S (ri_i D + RT_K_P D))
  [PresetReqAt.HFr (capw + cf_head)]) by (rewrite Ecapw, HHEAD; exact Ev2).
(* fuzz_free's post-implication arm, at the run's w_free event *)
destruct (Hadv Hq0 _ _ _ _ _ _ HPOS2 Ev2') as (hist3 & HPOS3).
assert (EKT : RT_K_T D = Datatypes.S (Datatypes.S (RT_K_P D))).
{ exact (ff_len5 (PresetReqAt.w_evs (ri_t D) (ri_p D)) (PresetReqAt.r_evs (ri_t D) (ri_p D))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (ri_tb D) [])
    (PresetReqAt.HFr (last (PresetReqAt.rcaps (ri_t D) (ri_p D)) 0))
    (PresetReqAt.HFr (last (PresetReqAt.wcaps (ri_t D) (ri_p D)) 0 + PresetReqAt.HEAD))). }
assert (HDbL : incl Db Lamp).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hbk. }
assert (HDbL3 : incl Db (l1 ++ l2)).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL3)). apply in_or_app. left. exact Hbk. }
assert (Hdq : forall a k0, In (a, k0) Db -> a <> q).
{ intros a k0 Hin Ea. subst a.
  pose proof (prh_ledger_nodup (PI := prh_img_A) B _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HLED)) as HND.
  (* prh_ledger states stdpp's NoDup; pass to Stdlib's List.NoDup (S1Ledger.v:124-125) *)
  apply NoDup_ListNoDup in HND.
  apply (Permutation_NoDup (Permutation_map fst HPL)) in HND.
  rewrite map_app in HND. cbn [map fst] in HND.
  apply NoDup_remove_2 in HND. apply HND. apply in_or_app. left. apply in_map_iff.
  exists (q, k0). split; [reflexivity | exact Hin]. }
assert (HEfr : forall x, inFP FP1 x -> ~ in_zr x (frame_rng ly (RT_CID, pos))).
{ intros x Hx. destruct (HEoff x Hx) as (_ & Hf). apply Hf. pose proof HFR as (Efr & _). rewrite Efr. left. reflexivity. }
assert (HEdb : forall x, inFP FP1 x -> forall a k0, In (a, k0) Db ->
  ~ (a - cf_head <= x < a - cf_head + req_size (k0 + cf_head))).
{ intros x Hx a k0 Hin Hx2.
  destruct (prh_ledger_hblock (PI := prh_img_A) B _ _ _ _ _ _ _ _ _ _ a k0 _ _ (proj1 HLED) (HDbL _ Hin))
    as (Hk0 & Hab & _).
  destruct Hx as (rg & [<- | []] & Hx). cbn [fst snd] in Hx.
  assert (Hne : (a - cf_head, k0 + cf_head) <> (q - cf_head, capw + cf_head)).
  { intros E. injection E as E1 _. apply (Hdq a k0 Hin). lia. }
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem mdF _ _ _ _ HARm Hab Hqb Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
split; [exact Hr0|]. split; [exact Hrc|]. split; [lia|].
  split.
  { unfold rtt_pos. exists hist3.
    replace (ri_i D + RT_K_T D)%nat with (Datatypes.S (ri_i D + RT_K_P D) + length [PresetReqAt.HFr (capw + cf_head)])%nat
      by (rewrite EKT; cbn [length]; lia).
    exact HPOS3. }
exists Db. split; [exact HPL3|]. split; [exact HDbn|]. split; [exact HDbsz|]. split; [exact HDbtb|].
  split.
  { eapply ff_fo_keep; [exact HC2 | exact HC3 | exact HK | exact (proj1 HLED) | exact HL3 | exact HDbL | exact HDbL3
      | exact HEfr | exact HEdb | exact HDbfo]. }
  split; [exact HDblen|].
  split; [rewrite Eb2; exact (ff_perm_drop _ b1 b2 _ _ HPA Eb1)|].
  split.
  { eapply ff_node_keep; [exact HC2 | exact HC3 | exact HK | exact (proj1 HLED) | exact HL3 | exact HDbL | exact HDbL3
      | exact HEfr | exact HEdb | exact HNB]. }
  split.
  { (* back's free order at every depth bound (rtt_rb's at the batch kit's cut) *)
    intros HH nn Hnn.
    eapply ff_fo_keep; [exact HC2 | exact HC3 | exact HK | exact (proj1 HLED) | exact HL3 | exact HDbL | exact HDbL3
      | exact HEfr | exact HEdb | exact (HDbfoK HH nn Hnn)]. }
  (* K0-CAP *)
  eapply ff_ncap_keep; [exact HC2 | exact HC3 | exact HK | exact (proj1 HLED) | exact HL3 | exact HDbL | exact HDbL3
    | exact HEfr | exact HEdb | exact HNB | exact HNC].
Qed.

(* ======================================================================================================== *)
(* ---- THE HEAD: from +788 (cmp_at_pn), s8 := rc, a0 := want, the direct free of want, to +800 (ff_mid) ---- *)
Lemma cmp_ff : RSEG RT_O2 AT_O2 -> cf_head = PresetReqAt.HEAD ->
  forall D, PRE D -> forall fxc ly S Hp W regs mem md k pos, CMP_PN D fxc ly S Hp W regs mem md k pos ->
  YA0nH.SRr' SEGS RZ W (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (RTT_K + RT_C3))) mem (YK11.seg_rom SEGS)) md)
    (POST D).
Proof.
intros SO2 HHEAD D HP fxc ly S Hp W regs mem md k pos HPN.
pose proof HPN as (HC & HBK & HS11 & HCK & R23 & (q & capw & want & cap & rc0 & Lamp & peakp & cntp & ranp &
  R22 & R21 & R10 & Hq0 & Hw0 & HLED & (Hcap & Hwin & Hwnew & Hwhp & _) & Hqnew & H24S & HOUT & (hist & Hpos) &
  Ecap & Ecapw)).
pose proof (@pa_segs_low _ A_prog_listing PA) as Hsegs.
pose proof (rtt_pre_facts (fx := fx) B ARx CTX0 D HP) as (HAR0 & Hsp0 & Hsp16 & H64 & HDL & _ & _ & _).
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrun & Hran0 & _).
pose proof HC as (HFX & HJ & HFR & HSV & HCR & HMN & HROD & HROOM & HNODE & HVIS).
pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hstkv : 16384 + 192 <= STKR) by (apply Z.leb_le; vm_compute; reflexivity).
destruct (ff_sp1 (ri_sp D) Hsp16) as (Hsp1 & Hsp32 & Ho16).
set (sp0 := ri_sp D) in *. set (sp1 := RT_R sp0) in *.
assert (Esp0 : sp0 = ri_sp D) by reflexivity. assert (Esp1 : sp1 = RT_R (ri_sp D)) by reflexivity.
unfold cmp_out in HOUT. cbv zeta in HOUT. cbn [app] in HOUT.
destruct HOUT as (Hr0 & Hrc & Hcnt & Db & HPL & HDbn & HDbsz & HDbtb & HDbfo & HDblen & HPA & HNB & HDbfoK & HNC).
assert (HincL : incl (ri_Lam D) Lamp).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. right. right. exact Hbk. }
unfold RT_C3.
(* +788 mv s8, a0 *)
eapply (fr_addi (fx := fxc) W regs mem md _ _ (RTT_K + 788) _ _ _ 24%bv 10%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | unfold RTT_K; vm_compute; discriminate | unfold RTT_K; vm_compute; reflexivity |].
intros mat1.
(* +792 mv a0, s5 *)
eapply (fr_addi (fx := fxc) W _ mem _ _ _ (RTT_K + 788 + 4) _ _ _ 10%bv 21%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | unfold RTT_K; vm_compute; discriminate | unfold RTT_K; vm_compute; reflexivity |].
intros mat2.
(* +796 jal __wrap_free *)
eapply (fr_jal (fx := fxc) W _ mem _ _ _ (RTT_K + 788 + 4 + 4) (pc_wrap_free (as_code B)));
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | unfold RTT_K; vm_compute; discriminate | unfold RTT_K; vm_compute; reflexivity
  | rewrite <- (pal_free B PAL); vm_compute; reflexivity |].
intros mat3.
match goal with |- YA0nH.SRr' _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ => set (regsT := r); set (mdT := m) end.
assert (HJm : RJ D ly S Hp W mem mdT k pos).
{ unfold mdT. apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW).
  apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW).
  apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW). exact HJ. }
pose proof (ajxR_ar HJm) as HARm. pose proof (ajxR_qt HJm) as HQTm.
assert (HC2 : RCARRY D fxc ly S Hp W regs mem mdT k pos)
  by exact (rtt_carry_md (fx := fx) B ARx SK D fxc ly S Hp W regs mem md k pos mdT HC HJm).
(* the call's registers *)
assert (FK : forall r : bv 5, r <> 1%bv -> r <> 10%bv -> r <> 24%bv -> getr regsT r = getr regs r).
{ intros r H1 H10 H24. unfold regsT. rewrite getr_other by exact H1. rewrite getr_other by exact H10.
  rewrite getr_other by exact H24. reflexivity. }
assert (T10 : getr regsT 10 = w64 want).
{ unfold regsT. rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac.
  rewrite getr_other by reg_neq_tac. rewrite R21.
  unfold v_addi, w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (T24 : getr regsT 24 = w64 rc0).
{ unfold regsT. rewrite getr_other by reg_neq_tac. rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac.
  rewrite R10. unfold v_addi, w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (T2 : spZ regsT = sp0 + (sp1 - sp0)).
{ unfold spZ. rewrite FK by reg_neq_tac. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (T8 : s0Z regsT = sp0).
{ unfold s0Z. rewrite FK by reg_neq_tac. rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
assert (T1 : getr regsT 1 = Z_to_bv 64 (BASE + (RTT_K + 800))).
{ unfold regsT. rewrite getr_same by reg_neq_tac. f_equal; lia. }
assert (HRA : YK0s.ret_ok (Z_to_bv 64 (BASE + (RTT_K + 800)))).
{ apply (ret_ok_codeptr_v (PI := PA)); unfold RTT_K; vm_compute; [split; [discriminate | reflexivity] | reflexivity]. }
assert (T3 : getr regsT 3 = w64 (as_gp B)) by (rewrite FK by reg_neq_tac; exact R3).
assert (T4 : getr regsT 4 = w64 (as_tp B)) by (rewrite FK by reg_neq_tac; exact R4).
destruct (rtt_chain_at (fx := fx) B ARx SK CTX0 rtt_stkr_A D ly S Hp W mem mdT k pos sp1 HP HJm HSV ltac:(lia))
  as (ch1 & Hach & Hch1).
assert (Hchp : chain_pre ly (aview SEGS (w_H W) mem) regsT ch1).
{ apply (achain_chain_pre ly _ sp1 sp0 ch1 regsT Hach); [rewrite T2; lia | exact T8 |].
  unfold raZ. rewrite T1. vm_compute. discriminate. }
assert (Htr : In (call_trace ly (pc_free_ra0 (as_code B)) regsT ch1) (as_universe B)).
{ apply (rtt_trace_at (fx := fx) B ARx CTX0 rtt_fp_A D ly regsT ch1 (bv_unsigned (Z_to_bv 64 (BASE + (RTT_K + 800))))
    RT_free HP Hch1).
  - unfold raZ. rewrite T1. reflexivity.
  - vm_compute. right. right. left. reflexivity. }
(* the free's trace is FIXED, so the allocator admits it at the call state (YCbqG.admits_ct_fix) *)
assert (Hadm : admits (as_universe B) (call_trace ly (pc_free_ra0 (as_code B)) regsT ch1) S)
  by exact (admits_ct_fix _ _ _ _ _ S Htr).
(* the call's trailing conjuncts at the call memory: the cut's room, the hull budget at the run's position (ff_hull)
   and the read-only view (the cut's carried arodata_okP) *)
assert (HHULL : PresetHullBudget.hull_budget S [])
  by exact (ff_hull _ _ _ _ _ _ S (rtt_pre_os4 (fx := fx) B ARx CTX0 D HP) Hpos).
assert (HQM : QMm S mem) by exact (QMR ly S Hp W mem mdT HARm HQTm HROOM HHULL HROD).
assert (HCR2 : forall ly2 S2 Hp2 W2 mem2 md2' k2 regs2, RJ D ly2 S2 Hp2 W2 mem2 md2' k2 pos ->
  aregs_preserved regsT regs2 -> rtt_cregs B D ly2 regs2 pos).
{ intros ly2 S2 Hp2 W2 mem2 md2' k2 regs2 HJ2 HP2.
  destruct (rtt_fa_eq B ARx SK D ly2 S2 Hp2 W2 mem2 md2' k2 pos HJ2) as (Fa2 & _).
  destruct (rtt_fa_eq B ARx SK D ly S Hp W mem mdT k pos HJm) as (Fac & _).
  assert (KP : forall r : bv 5, acallee_saved (bv_unsigned r) -> r <> 24%bv -> getr regs2 r = getr regs r).
  { intros r Hr H24. rewrite (ts_ap _ _ r HP2 Hr). apply FK; [intros E; subst r; ff_not_cs Hr
      | intros E; subst r; ff_not_cs Hr | exact H24]. }
  unfold rtt_cregs. rewrite Fa2. rewrite Fac in R18, R25, R26.
  rewrite !KP by (first [ts_cs | reg_neq_tac]).
  repeat split; assumption. }
(* +796 lands at the free wrapper: free (want), a live block made since the entry, no harness block *)
eapply (YSRrG.SRr'_bind SEGS RZ).
{ exact (aj_free_at_x_ctR (fx := fxc) (rc := rc) (SK := SK) SEGS B PST ARx QM QMm mt nmax YG00cf.free_cf WFx LAWS Hsegs
    (pal_env B PAL) WFL AMX QMQ RZW (YA0nH.wle'_trans SEGS RZ) APOST POST_AR POST_J
    (AFREE fxc) W regsT mem STKR sp0 (ri_FP D) (ri_ly D) (set_depot (st_depot S) (ri_S D)) (ri_Hp D) (ri_W D) (ri_mem D)
    (ri_md D) [(RT_CID, pos)]
    ly S Hp mdT k want cap (sp1 - sp0) _ ch1 HJm Hwin Hwhp T10 T2 Ho16 ltac:(lia) ltac:(lia) T3 T4 T1 HRA HQM Hchp Hadm
    (fun H => False_ind _ (Hwnew H))). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md3 & -> & HJ2 & HP2 & (l1 & l2 & El1 & El2) & Efr2 & HPREx & _ &
  (qf & trc & Hqf & Hqin & Hpath & Hgf & Hleaf) & HKA).
(* the caller's journal at `[] ++ [the free's trace]`: the fixed trace leaves the budget (YCbqG.ajournal_xw_fix1R),
   which is the call rule's journal from rtt_J at S (rtt_Jc at S); at the new state it is rtt_J again *)
pose proof (ajournal_xw_fix1R Htr HJ2) as HJ2c.
assert (HJ2r : RJ D ly2 S2 Hp W2 mem2 md3 (k + (st_nev S2 - st_nev S)) pos)
  by exact (rtt_J_of_Jc B ARx SK D S ly2 S2 Hp W2 mem2 md3 (k + (st_nev S2 - st_nev S)) pos HJ2c).
(* the free's memnorm keep, from its call post (POST_MN at the leaf's APOST, the call memory to the return memory) *)
assert (HMN2 : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2).
{ intros HM0. destruct Hleaf as (ly' & regs' & mem' & md' & Hc' & HAP & _).
  unfold cfg_at in Hc'. injection Hc'. intros. subst.
  exact (POST_MN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAP HM0). }
pose proof (ACF ly S Hp W regsT mem mdT ch1 HPREx) as HPREcf.
(* RF_free's live-set premise at the free's call state: cmp_at_pn's position-free class-24 bound *)
assert (Hb24 : YGcfRoomLive.rl_b24_ok (PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1) S)
  by exact (CfRoomLivePreset.preset_rl_b24_ok S H24S).
pose proof (RF_free (fx := fxc) SEGS B ly S Hp W regsT mem mdT ch1 _ qf _ trc (tt, S2) HPREcf Hb24 HROOM Hpath) as HRL2.
cbn [snd] in HRL2.
assert (HEoff : forall x, want <= x < want + req_size cap -> rtt_off D ly S x).
{ intros x Hx. eapply (rtt_newblk_off (fx := fx) B ARx SK CTX0 LAWS D ly S Hp W mem mdT k pos);
    [exact HP | exact HJm | exact (proj1 HLED) | exact HincL | exact Hwin | exact Hwnew | exact Hx]. }
assert (HEled : forall x, want <= x < want + req_size cap -> forall a k0, In (a, k0) Lamp ->
  ~ (a - cf_head <= x < a - cf_head + req_size (k0 + cf_head))).
{ intros x Hx. eapply (rtt_blk_off_ledger B ARx LAWS ly S Hp W mem mdT); [exact HARm | exact (proj1 HLED) | exact Hwin
    | exact Hwhp | exact Hx]. }
assert (Hblk : forall a k0, In (a, k0) Lamp -> In (a - cf_head, k0 + cf_head) (ablocks B ly S) ->
  In (a - cf_head, k0 + cf_head) (ablocks B ly2 S2)).
{ intros a k0 Hin Hb.
  destruct (prh_ledger_hblock (PI := prh_img_A) B _ _ _ _ _ _ _ _ _ _ a k0 _ _ (proj1 HLED) Hin) as (_ & _ & Hh & _).
  apply (prh_in_split_other _ _ l1 l2 (want, cap) _ El1); [rewrite El2; intros y Hy; exact Hy | | exact Hb].
  intros E. injection E as E1 _. rewrite <- E1 in Hwhp. exact (Hwhp Hh). }
destruct (rtt_free_keep (fx := fx) B ARx SK CTX0 LAWS pal_pst_static HW pst_in_img_A pst_not_ro_A rtt_stkr_A D fxc ly S
  Hp W regs
  mem mdT k pos ly2 S2 W2 regs2 mem2 md3 (k + (st_nev S2 - st_nev S)) (sp0 + (sp1 - sp0) - ASTACK) (sp0 + (sp1 - sp0))
  (fun a => want <= a < want + req_size cap) Lamp peakp cntp ranp 0 HP HC2 HJ2c Efr2 HKA ltac:(lia) HEoff
  (fun x Hx => rtt_blk_off_sh B ARx LAWS ly S Hp W mem mdT want cap x HARm Hwin Hx RT_CID pos
     ltac:(pose proof HFR as (Efr & _); rewrite Efr; left; reflexivity))
  HEled Hblk HLED HincL (HCR2 _ _ _ _ _ _ _ _ HJ2r HP2) HMN2 HRL2)
  as (HC3 & HLED3 & HCK3 & HBK3).
(* fuzz_free's class-24 premise at its call state: the free of want lost one block (aj_free_at_x_ctR's post) *)
assert (H242 : YGcfRoomLive.ccnt24 S2 <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
{ pose proof (ff_ccnt24_drop ly S ly2 S2 l1 l2 (want, cap) El1 El2) as Hd. lia. }
(* the registers the tail reads *)
assert (KP2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regsT r)
  by (intros r Hr; exact (ts_ap _ _ r HP2 Hr)).
assert (R222 : getr regs2 22 = w64 q) by (rewrite KP2 by ts_cs; rewrite FK by reg_neq_tac; exact R22).
assert (R242 : getr regs2 24 = w64 rc0) by (rewrite KP2 by ts_cs; exact T24).
assert (S112 : getr regs2 27 = w64 (SIGMA AS_round_trip_text + RT_O1 + RT_S11))
  by (rewrite KP2 by ts_cs; rewrite FK by reg_neq_tac; exact HS11).
assert (R232 : getr regs2 23 = w64 (frame_addr ly2 RT_CID pos + RT_BACK)).
{ rewrite KP2 by ts_cs. rewrite FK by reg_neq_tac. rewrite R23.
  destruct (rtt_fa_eq B ARx SK D ly2 S2 Hp W2 mem2 md3 _ pos HJ2r) as (Fa2 & _).
  destruct (rtt_fa_eq B ARx SK D ly S Hp W mem mdT k pos HJm) as (Fac & _).
  rewrite Fa2, Fac. reflexivity. }
assert (HKr := rtt_kept_of_acall B ly S W mem ly2 S2 W2 mem2 _ _ _ HKA).
assert (HEfr : forall x, want <= x < want + req_size cap -> ~ in_zr x (frame_rng ly (RT_CID, pos))).
{ intros x Hx. destruct (HEoff x Hx) as (_ & Hf). apply Hf. pose proof HFR as (Efr & _). rewrite Efr. left. reflexivity. }
(* the free's run event is the model's r_free (the cut is granted only) *)
assert (Hqnn : qf <> PNull).
{ intros E. subst qf. assert (E0 : sptr_addr B ly PNull = 0) by reflexivity. rewrite E0 in Hqf. exact (Hw0 (eq_sym Hqf)). }
destruct (ff_run_ev _ _ _ _ (PresetReqAt.w_evs (ri_t D) (ri_p D)) (PresetReqAt.r_evs (ri_t D) (ri_p D))
   (PresetReqAt.parse_evs ReaderRes.jr_strtod (ri_tb D) [])
   (if ri_copy D =? 0 then [PresetReqAt.HBulk (PresetReqAt.fo (ri_t D))] else [])
   (PresetReqAt.HFr (last (PresetReqAt.rcaps (ri_t D) (ri_p D)) 0))
   (PresetReqAt.HFr (last (PresetReqAt.wcaps (ri_t D) (ri_p D)) 0 + PresetReqAt.HEAD)) Hrun) as (Ev1 & _).
assert (Ev1' : nth_error (PresetRun.hruns ReaderRes.jr_strtod (ri_x D) (ri_os D)) (ri_i D + RT_K_P D) =
  Some (PresetReqAt.HFr cap)) by (rewrite Ecap; exact Ev1).
pose proof (PresetRoomPosKeep.room_pos_keep_free SEGS B ly S Hp W regsT mem mdT ch1 ReaderRes.jr_strtod (ri_x D)
  (ri_os D) (ri_i D + RT_K_P D) (ri_H0 D) hist qf cap _ trc S2 HPREcf Hadm Hqin Hqnn Hpath Hpos Ev1') as HPOS2.
assert (HDbL : incl Db Lamp).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hbk. }
assert (HEdb : forall x, want <= x < want + req_size cap -> forall a k0, In (a, k0) Db ->
  ~ (a - cf_head <= x < a - cf_head + req_size (k0 + cf_head))).
{ intros x Hx a k0 Hin. exact (HEled x Hx a k0 (HDbL _ Hin)). }
apply (ff_tail SO2 HHEAD D HP fxc ly2 S2 Hp W2 regs2 mem2 md3 (k + (st_nev S2 - st_nev S)) pos).
split; [exact HC3|]. split; [exact (HBK3 HBK)|]. split; [exact S112|]. split; [exact (HCK3 HCK)|].
split; [exact R232|].
exists q, capw, rc0, Lamp, peakp, cntp, ranp.
split; [exact R222|]. split; [exact R242|]. split; [exact Hq0|]. split; [exact HLED3|].
split; [exact Hqnew|].
split.
{ split; [exact Hr0|]. split; [exact Hrc|]. split; [exact Hcnt|].
  exists Db. split; [exact HPL|]. split; [exact HDbn|]. split; [exact HDbsz|]. split; [exact HDbtb|].
  split.
  { eapply ff_fo_keep; [exact HC2 | exact HC3 | exact HKr | exact (proj1 HLED) | exact (proj1 HLED3) | exact HDbL
      | exact HDbL | exact HEfr | exact HEdb | exact HDbfo]. }
  split; [exact HDblen|].
  split; [rewrite El2; exact (ff_perm_drop _ l1 l2 _ _ HPA El1)|].
  split.
  { eapply ff_node_keep; [exact HC2 | exact HC3 | exact HKr | exact (proj1 HLED) | exact (proj1 HLED3) | exact HDbL
      | exact HDbL | exact HEfr | exact HEdb | exact HNB]. }
  split.
  { (* back's free order at every depth bound *)
    intros HH nn Hnn.
    eapply ff_fo_keep; [exact HC2 | exact HC3 | exact HKr | exact (proj1 HLED) | exact (proj1 HLED3) | exact HDbL
      | exact HDbL | exact HEfr | exact HEdb | exact (HDbfoK HH nn Hnn)]. }
  (* K0-CAP *)
  eapply ff_ncap_keep; [exact HC2 | exact HC3 | exact HKr | exact (proj1 HLED) | exact (proj1 HLED3) | exact HDbL
    | exact HDbL | exact HEfr | exact HEdb | exact HNB | exact HNC]. }
split; [exact H242|].
split; [|exact Ecapw].
unfold rtt_pos. exists (hist ++ YGcfRoom.freed_cf S qf). rewrite Nat.add_succ_r. exact HPOS2.
Qed.

End ff.

(* ---- THE STATEMENT CHECK (the text owner's rule, 2026-10-29, with its amendment: implicits on, notations off, the BODY
   of every Prop definition printed), checked in: cmp_ff (a theorem: its type is its statement, Check) and the inner
   cut ff_mid (a Prop definition: Print) bind a second FPState (fxc) beside the contract's fx. PASS is `fx` wherever a
   cut predicate takes its class-implicit FPState (rtt_pre / rtt_carry / rtt_seg / rtt_at_o2 / rtt_post / cmp_at_pn),
   and `fxc` only as an explicit argument (the cut's state argument, `@YK11.mkst fxc`). The intermediate lemmas the
   proof states (ff_tail, ff_foot_agree, ff_node_keep, ff_fo_keep, ff_ncap_keep) are checked the same way: the
   proof-context form of the trap (a local FPState captured by a later implicit) would show here as `fxc` in a
   class-implicit position. ---- *)
Set Printing Implicit.
Unset Printing Notations.
(* the body printed whole: no `(...)` elision of a subterm that could hold an FPState *)
Set Printing Depth 1000.
Check @cmp_ff.
Print ff_mid.
Check @ff_tail.
Check @ff_foot_agree.
Check @ff_node_keep.
Check @ff_fo_keep.
Check @ff_ncap_keep.
Set Printing Notations.
Unset Printing Implicit.
Print Assumptions cmp_ff.
