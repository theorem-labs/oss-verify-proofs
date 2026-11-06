(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct Refund.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState LayoutPA AInv ALogic1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AInvWfp.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dl_first | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@H; @Hi; @CE; @RSB; @R; @R1; @R2; @Hx; @FR; @APP; @RB; @X1; @H0; @B6; @Hr; @H1; @H2; @G1; @FS2; @S1; @D; @Rv; @SR; @S2; @G4; @Ha; @LT; @Hc; @SB; @As; @W1; @Rj; @SZ; @N; @IN; @GE; @FSH; @B1; @Hs; @Hb; @W2; @HB6; @Hz; @Hv; @SF1; @LTw; @SF2; @AF; @Hn; @K; @LO; @SA; @HI; @F4'; @S; @Q2; @Q7; @IS; @RB1; @RB2; @U2; @LT2; @GE2; @H4; @H5; @H3; @A1; @Ab; @SCE; @B3; @B4; @Mb; @SF3; @NN; @HIGH; @Rz; @Rz'; @e; @NZ; @Hk; @PR; @SR1; @SR2; @G5; @STR; @X; @Q4; @Q6; @E5; @C; @L2; @B6b; @B6a; @N2; @EN; @S3; @FR'; @B2; @A2; @ST; @E2; @HB; @HE; @Mn; @G; @SHP; @B'; @IM; @A64; @LOB; @D1; @Bge; @Ilt; @Blo; @Ige; @Psp0; @SF4; @N31; @B7; @B8; @B5; @RG])).
Ltac hot_lia_full := first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dl_first | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac mem_side := cbn; first [ (let E := fresh "E" in intros E; discriminate E) | solve [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [ exact I | reflexivity ] ] | solve [ repeat first [ left; reflexivity | right ] ] | tauto ].
Local Ltac mem_hyp Hr := cbn in Hr; first [ solve [ repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]); first [ discriminate Hr | destruct Hr ] ] | intuition discriminate ].
(* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac kun := unfold kSpaceSize, kSpaceReserve, kRegionSize, kFreeArrayOffset, kFreeArraySize, kUserMapSize, kFreeArrayMapSize,
  kRegionInfoSize, kPageSize, kChunksBlockCount, kPtrArrayReserve, kSecondaryHeaderSize, kChunkHeaderSize, kHighMemBeg,
  kHighShadowMapBeg, kHighShadowMapSize, kLowShadowMapBeg, kLowMemEnd, kQuarantineBatchBytes, kQuarantineBatchCount,
  kDepotNodesBlock, kStackStoreBlockBytes, kDepotNodesL1, kFakeStackBytes, kFakeFlagsOffset, kFakeFramesOffset, kFakeFlagsBytes,
  kMaxPrimaryUser, kMaxSize in *.

Section Pasan.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Context {DR : DepotRep}.
#[local] Notation WF := (WF AL_pasan).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma place_facts : forall A, WF A -> let P := a_pl A in
  (app_rangeA AL_pasan (p_thr P) 4096 /\ p_thr P + 4096 <= alloc_ceiling /\ p_thr P mod 4096 = 0) /\
  (app_rangeA AL_pasan (p_ctx P) 0x10000 /\ p_ctx P + 0x10000 <= alloc_ceiling /\ p_ctx P mod 4096 = 0) /\
  (app_rangeA AL_pasan (p_nodes0 P) kDepotNodesBlock /\ p_nodes0 P + kDepotNodesBlock <= alloc_ceiling /\ p_nodes0 P mod 4096 = 0) /\
  (app_rangeA AL_pasan (p_frames0 P) kStackStoreBlockBytes /\ p_frames0 P + kStackStoreBlockBytes <= alloc_ceiling /\ p_frames0 P mod 4096 = 0) /\
  (app_rangeA AL_pasan (p_fs P) kFakeStackBytes /\ p_fs P + kFakeStackBytes <= alloc_ceiling /\ p_fs P mod 4096 = 0) /\
  (app_rangeA AL_pasan (p_itab P) 0x38e000 /\ p_itab P + 0x38e000 <= alloc_ceiling /\ p_itab P mod 4096 = 0) /\
  (app_rangeA AL_pasan (p_m64k P) 0x10000 /\ p_m64k P + 0x10000 <= alloc_ceiling /\ p_m64k P mod 4096 = 0) /\
  (app_rangeA AL_pasan (p_gvec P) 4096 /\ p_gvec P + 4096 <= alloc_ceiling /\ p_gvec P mod 4096 = 0) /\
  (app_rangeA AL_pasan (p_dvec P) 4096 /\ p_dvec P + 4096 <= alloc_ceiling /\ p_dvec P mod 4096 = 0) /\
  (app_rangeA AL_pasan (p_m11 P) 4096 /\ p_m11 P + 4096 <= alloc_ceiling /\ p_m11 P mod 4096 = 0) /\
  (app_rangeA AL_pasan (p_dtls P) 4096 /\ p_dtls P + 4096 <= alloc_ceiling /\ p_dtls P mod 4096 = 0) /\
  (app_rangeA AL_pasan (p_pa P) kPtrArrayReserve /\ p_pa P + kPtrArrayReserve <= alloc_ceiling /\ p_pa P mod 4096 = 0) /\
  (alloc_ceiling + 0x800000 <= p_sp0 P <= 2^47 /\ 0 <= p_stk_span P <= 0x240000 /\ p_sp0 P mod 16 = 0) /\
  (0 <= p_stk_top P < 2^64 /\ 0 <= p_stk_bot P < 2^64).
Proof. intros A W. pose proof (wfP A W) as P. apply wf_place_cheap in P. cbv zeta in *. tauto. Qed.
Lemma place_fs : forall A, WF A -> app_rangeA AL_pasan (a_fs A) kFakeStackBytes /\ a_fs A + kFakeStackBytes <= alloc_ceiling /\ a_fs A mod 4096 = 0.
Proof. intros A W. pose proof (place_facts A W) as P. cbv zeta in P. unfold a_fs. tauto. Qed.

Lemma fsize_facts : forall k, 0 <= k <= 10 -> fsize k mod 8 = 0 /\ (fsize k + 7) / 8 = fsize k / 8 /\ fsize k / 8 = 8 * 2 ^ k /\ fsize k mod 64 = 0.
Proof.
  intros k Hk. unfold fsize. assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  replace (64 * 2 ^ k) with ((8 * 2 ^ k) * 8) by lia.
  rewrite Z_mod_mult, Z.div_add_l, Z_div_mult by lia. change (7 / 8) with 0.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. all: replace (8 * 2 ^ k * 8) with (2 ^ k * 64) by lia; apply Z_mod_mult.
Qed.

Lemma sh_disjoint : forall a n b s, a mod 8 = 0 -> b mod 8 = 0 -> n mod 8 = 0 -> s mod 8 = 0 ->
  a + n <= b \/ b + s <= a -> sh a + n / 8 <= sh b \/ sh b + s / 8 <= sh a.
Proof.
  intros a n b s Ha Hb Hn Hs D. rewrite <- (sh_add a n Ha Hn), <- (sh_add b s Hb Hs).
  destruct D; [left|right]; apply sh_mono; lia.
Qed.

Lemma wr_at_of_mapped : forall (v : mem) a n, 0x60a000 <= a -> a + n <= 2^64 -> mapped v a n -> wr_at (cl_segs LPA) v a n.
Proof.
  intros v a n Ha Hn M. split; [lia|]. split; [lia|]. intros i Hi. cbn [cl_segs LPA]. unfold wa.
  rewrite pa_wview_overlay by (rewrite unsigned_lit by lia; lia). apply M. exact Hi.
Qed.
Lemma mapped_sub : forall (v : mem) a n b k, mapped v a n -> a <= b -> b + k <= a + n -> mapped v b k.
Proof. intros v a n b k M H1 H2 i Hi. replace (b + i) with (a + (b - a + i)) by lia. apply M. lia. Qed.

(* [comment removed for export] *)
Lemma frame_facts : forall A m md ff f, pa_ainv A m md -> a_fframes A !! ff = Some f ->
  let k := ff_class f in let fs := a_fs A in
  0 <= k <= 10 /\ ff = fframe_addr fs k (ff_pos (a_fhint A k) k (ff_age f)) /\ Z.of_nat (ff_age f) < fslots k /\
  fs + kFakeFramesOffset <= ff /\ ff + fsize k <= fs + kFakeStackBytes /\
  app_rangeA AL_pasan fs kFakeStackBytes /\ fs + kFakeStackBytes <= alloc_ceiling /\ fs mod 4096 = 0 /\
  64 <= fsize k <= 65536 /\ ff mod 64 = 0 /\ ff mod Z.min (fsize k) 4096 = 0 /\
  sh fs <= sh ff /\ sh ff + fsize k / 8 <= sh fs + kFakeStackBytes / 8 /\
  0x7fff8200 <= sh fs /\ sh fs + kFakeStackBytes / 8 <= kHighMemBeg.
  (* [comment removed for export] *)
Proof.
  intros A m md ff f AI Hf. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W. pose proof alloc_ceiling_val as CE.
  (first [ pose proof ((wfF A W)) as dR_1; dand3 dR_1 as F1 _ _ | destruct (wfF A W) as (F1 & _ & _) ]). (first [ pose proof ((F1 ff f Hf)) as dR_2; dand3 dR_2 as K E AG | destruct (F1 ff f Hf) as (K & E & AG) ]). cbv zeta in *. unfold ff_addr_of_ in E.
  (first [ pose proof ((place_fs A W)) as dR_3; dand3 dR_3 as FS1 FS2 FSM | pose proof (place_fs A W) as (FS1 & FS2 & FSM) ]). unfold a_fs in *.
  pose proof (ff_pos_range (a_fhint A (ff_class f)) (ff_class f) (ff_age f) K) as PR.
  (first [ pose proof ((fframe_addr_range (p_fs (a_pl A)) (ff_class f) _ K PR)) as dR_4; dand3 dR_4 as R1 R2 R3 | pose proof (fframe_addr_range (p_fs (a_pl A)) (ff_class f) _ K PR) as (R1 & R2 & R3) ]). rewrite <- E in R1, R2, R3.
  pose proof (fsize_pos _ K) as [FS _]. (first [ pose proof ((fsize_facts _ K)) as dR_5; dand4 dR_5 as M8 C8 D8 M64 | pose proof (fsize_facts _ K) as (M8 & C8 & D8 & M64) ]).
  pose proof (fframe_addr_align (p_fs (a_pl A)) (ff_class f) (ff_pos (a_fhint A (ff_class f)) (ff_class f) (ff_age f)) K ltac:(lia) FSM) as AL.
  rewrite <- E in AL.
  assert (M64f : ff mod 64 = 0).
  { rewrite E. unfold fframe_addr, kFakeFramesOffset, kFakeStackSizeLog. unfold fsize.
    pose proof (Z_div_exact_full_2 (p_fs (a_pl A)) 4096 ltac:(lia) FSM) as Efs. rewrite Efs at 1.
    match goal with |- ?x mod 64 = 0 =>
      replace x with ((p_fs (a_pl A) / 4096 * 64 + 576 + 2 ^ 14 * ff_class f + 2 ^ ff_class f * ff_pos (a_fhint A (ff_class f)) (ff_class f) (ff_age f)) * 64) by ring end.
    apply Z_mod_mult. }
  pose proof (sh_ceil_le ff (fsize (ff_class f)) (p_fs (a_pl A)) kFakeStackBytes ltac:(apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M64f])
    ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact FSM]) eq_refl ltac:(unfold kFakeFramesOffset in *; lia) R3) as [S1 S2].
  rewrite C8 in S2.
  (first [ pose proof ((app_facts _ _ FS1)) as dR_6; dand5 dR_6 as G1 G2 G3 G4 G5 | pose proof (app_facts _ _ FS1) as (G1 & G2 & G3 & G4 & G5) ]).
  pose proof (sh_add (p_fs (a_pl A)) (kFakeStackBytes - 8) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact FSM]) eq_refl) as SA.
  change ((kFakeStackBytes - 8) / 8) with (kFakeStackBytes / 8 - 1) in SA.
  assert (X1 : p_fs (a_pl A) + kFakeFramesOffset <= ff) by (unfold kFakeFramesOffset in *; lia).
  assert (SR : 0x7fff8200 <= sh (p_fs (a_pl A)) /\ sh (p_fs (a_pl A)) + kFakeStackBytes / 8 <= kHighMemBeg).
  { destruct G5 as [LO|HI].
    - pose proof (sh_lowapp_range (p_fs (a_pl A)) ltac:(unfold kFakeStackBytes in *; lia)).
      pose proof (sh_lowapp_range (p_fs (a_pl A) + (kFakeStackBytes - 8)) ltac:(unfold kFakeStackBytes in *; lia)). unfold kHighMemBeg. lia.
    - pose proof (sh_high_range (p_fs (a_pl A)) ltac:(unfold kFakeStackBytes in *; lia)).
      pose proof (sh_high_range (p_fs (a_pl A) + (kFakeStackBytes - 8)) ltac:(unfold kFakeStackBytes in *; lia)).
      unfold kHighShadowMapBeg, kHighMemBeg in *. lia. }
  destruct SR as [SR1 X2].
  split; [exact K|]. split; [exact E|]. split; [exact AG|]. split; [exact X1|]. split; [exact R3|]. split; [exact FS1|]. split; [exact FS2|].
  split; [exact FSM|]. split; [exact FS|]. split; [exact M64f|]. split; [exact AL|]. split; [exact S1|]. split; [exact S2|]. split; [exact SR1| exact X2].
Qed.

Lemma asI_frame_ok : forall A m md ff k age, pa_ainv A m md -> as_fframe A ff = Some (k, age) ->
  0 <= k <= 10 /\ ff mod Z.min (fsize k) 4096 = 0 /\ app_range LPA ff (fsize k) /\ ff + fsize k <= alloc_ceiling /\
  ~ in_image LPA ff /\
  wr_at (cl_segs LPA) (aview_of (pa_hull A) m) ff (fsize k - 8) /\ mapped (aview_of (pa_hull A) m) ff (fsize k) /\
  wr_at (cl_segs LPA) (aview_of (pa_hull A) m) (sh ff) (fsize k / 8) /\ mapped (aview_of (pa_hull A) m) (sh ff) (fsize k / 8) /\
  (forall i, 0 <= i < fsize k - 8 -> ~ pa_owned A (ff + i)) /\
  (forall i, 0 <= i < fsize k / 8 -> ~ pa_owned A (sh ff + i)).
Proof.
  intros A m md ff k age AI HF. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W. pose proof alloc_ceiling_val as CE.
  unfold as_fframe, as_fframe_ in HF. destruct (a_fframes A !! ff) as [f|] eqn:Hf; [|discriminate]. cbn in HF. injection HF as Hk Hage. subst k age.
  pose proof (frame_facts A m md ff f AI Hf) as FF. cbv zeta in FF.
  (first [ dand15 FF as K E AG R1 R2 FS1 FS2 FSM SZ M64 AL S1 S2 SR1 SR2 | destruct FF as (K & E & AG & R1 & R2 & FS1 & FS2 & FSM & SZ & M64 & AL & S1 & S2 & SR1 & SR2) ]). unfold kFakeFramesOffset in *.
  (first [ pose proof ((ar_fsbase _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_8; dand5 dR_8 as _ _ _ MF MS | destruct (ar_fsbase _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & _ & _ & MF & MS) ]). unfold a_fs in *.
  set (v := aview_of (ahull_of pa_image_ivs AL_pasan A) m) in *. change (aview_of (pa_hull A) m) with v.
  assert (MV1 : mapped v ff (fsize (ff_class f))) by (eapply mapped_sub; [exact MF| unfold kFakeFramesOffset in *; lia| lia]).
  assert (MV2 : mapped v (sh ff) (fsize (ff_class f) / 8)) by (eapply mapped_sub; [exact MS| lia| lia]).
  (first [ pose proof ((app_facts _ _ FS1)) as dR_9; dand5 dR_9 as G1 G2 G3 G4 G5 | pose proof (app_facts _ _ FS1) as (G1 & G2 & G3 & G4 & G5) ]).
  assert (FSR : app_rangeA AL_pasan ff (fsize (ff_class f))) by (apply (app_rangeA_sub _ _ _ _ _ FS1); unfold kFakeFramesOffset in *; lia).
  (first [ pose proof ((app_facts _ _ FSR)) as dR_10; dand5 dR_10 as F1' _ _ F4' F5' | pose proof (app_facts _ _ FSR) as (F1' & _ & _ & F4' & F5') ]).
  split; [exact K|]. split; [exact AL|]. split; [apply app_range_pasan; exact FSR|]. split; [lia|].
  split. { unfold in_image. cbn [cl_image_lo cl_image_hi LPA]. lia. }
  split. { apply wr_at_of_mapped; [unfold kFakeStackBytes in *; lia| lia|]. eapply mapped_sub; [exact MV1| lia| lia]. }
  split; [exact MV1|].
  split. { apply wr_at_of_mapped; [lia| unfold kHighMemBeg in *; lia| exact MV2]. }
  split; [exact MV2|].
  split.
  - intros i Hi OW. assert (NSM : ~ in_shadow_maps (ff + i)) by (apply app_not_in_shadow_maps; lia).
    destruct OW as [[S|[[(IR & NU & NF)|[HS|[FS _]]]|GH]]|IS].
    + cbn [cl_static LPA] in S. unfold pa_static in S. clear - S F1' F4' Hi. lia.
    + apply NF. exists ff, f. split; [exact Hf| lia].
    + exact (NSM (heap_shadow_range A _ W HS)).
    + exact (NSM (fs_shadow_in_maps A _ W FS)).
    + exact (NSM (proj1 GH)).
    + exact (NSM (image_shadow_in_maps _ IS)).
  - intros i Hi OW. pose proof (fs_shadow_strict A (sh ff + i) W ltac:(unfold a_fs; lia)) as STR.
    destruct OW as [[S|[[(IR & NU & NF)|[HS|[FS NFS]]]|GH]]|IS].
    + cbn [cl_static LPA] in S. unfold pa_static, in_shadow_strict, kLowShadowBeg, kHighShadowMapBeg in *. clear - S STR. lia.
    + (first [ dex2 IR as b s; destruct IR as [Hin Hb] | dand4 IR as b s Hin Hb | destruct IR as (b & s & Hin & Hb) ]). pose proof (runtime_maps_range A b s _ W Hin Hb) as X. cbn [al_image_lo al_image_hi AL_pasan] in X.
      apply (strict_not_app _ STR). clear - X CE. unfold kLowMemEnd, kLowShadowMapBeg in *. lia.
    + (* [comment removed for export] *)
      (first [ pose proof ((bm_nth_fixed A)) as dR_12; dand8 dR_12 as E0 _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & _ & _ & E6 & _) ]).
      unfold heap_shadow, heap_shadow_ in HS. change (p_sb (a_pl A)) with (a_sb A) in HS.
      destruct HS as [(c & Hc & R)|[(c & Hc & R)|(sc & Hsc & R)]]; cbv zeta in R.
      * pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in RB. (first [ dand12 RB as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | destruct RB as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]).
        assert (B6 : forall x, region_beg (a_sb A) c <= x < region_beg (a_sb A) c + rg_mapped_user (a_reg A c) -> a_b6 A <= x < a_b6 A + kSpaceReserve).
        { intros x Hx. apply primary_in_b6; [exact W| unfold kRegionSize, kFreeArrayOffset in *; lia]. }
        destruct (sh_disjoint ff (fsize (ff_class f)) (region_beg (a_sb A) c) (rg_mapped_user (a_reg A c))
                   ltac:(apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M64]) ltac:(apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact Q9])
                   ltac:(apply (proj1 (fsize_facts _ K))) Q10); [|lia|lia].
        destruct (Z.eq_dec (rg_mapped_user (a_reg A c)) 0) as [Z0|NZ]; [rewrite Z0 in R; change (0/8) with 0 in R; lia|].
        destruct (bm_sep A 0 6 _ _ _ _ W E0 E6 ltac:(lia)) as [D|D].
        -- right. specialize (B6 (region_beg (a_sb A) c + rg_mapped_user (a_reg A c) - 1) ltac:(lia)). unfold a_fs in *. lia.
        -- left. specialize (B6 (region_beg (a_sb A) c) ltac:(lia)). unfold a_fs in *. lia.
      * pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in RB. (first [ dand12 RB as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | destruct RB as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]).
        assert (B6 : forall x, region_beg (a_sb A) c + kFreeArrayOffset <= x < region_beg (a_sb A) c + kFreeArrayOffset + rg_mapped_fa (a_reg A c) -> a_b6 A <= x < a_b6 A + kSpaceReserve).
        { intros x Hx. apply primary_in_b6; [exact W| unfold kRegionSize, kFreeArrayOffset in *; lia]. }
        destruct (sh_disjoint ff (fsize (ff_class f)) (region_beg (a_sb A) c + kFreeArrayOffset) (rg_mapped_fa (a_reg A c))
                   ltac:(apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M64])
                   ltac:(rewrite Z.add_mod by lia; rewrite (mod0_down _ 0x10000 8 ltac:(exists 8192; reflexivity) Q9); reflexivity)
                   ltac:(apply (proj1 (fsize_facts _ K))) Q12); [|lia|lia].
        destruct (Z.eq_dec (rg_mapped_fa (a_reg A c)) 0) as [Z0|NZ]; [rewrite Z0 in R; change (0/8) with 0 in R; lia|].
        destruct (bm_sep A 0 6 _ _ _ _ W E0 E6 ltac:(lia)) as [D|D].
        -- right. specialize (B6 (region_beg (a_sb A) c + kFreeArrayOffset + rg_mapped_fa (a_reg A c) - 1) ltac:(lia)). unfold a_fs in *. lia.
        -- left. specialize (B6 (region_beg (a_sb A) c + kFreeArrayOffset) ltac:(lia)). unfold a_fs in *. lia.
      * (first [ pose proof ((sec_chunk_bounds A sc W Hsc)) as dR_15; dand5 dR_15 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_bounds A sc W Hsc) as (B1 & B2 & B3 & B4 & B5) ]). pose proof (map_size_page (cs_n sc)) as MP. pose proof (map_size_room (cs_n sc)).
        destruct (In_nth_error' _ _ Hsc) as [j Hj]. pose proof (bm_nth_sec A j sc Hj) as Ej.
        destruct (sh_disjoint ff (fsize (ff_class f)) (cs_map sc) (map_size (cs_n sc))
                   ltac:(apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M64]) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact B2])
                   ltac:(apply (proj1 (fsize_facts _ K))) ltac:(apply (mod0_down _ kPageSize 8); [exists 512; reflexivity| exact MP])); [|lia|lia].
        destruct (bm_sep A (15 + j) 6 _ _ _ _ W Ej E6 ltac:(lia)); unfold a_fs in *; lia.
    + apply NFS. exists ff, f. split; [exact Hf| lia].
    + exfalso. refine (fs_shadow_not_ghost A (sh ff + i) W _ GH). unfold a_fs. lia.
    + (* [comment removed for export] *)
      unfold pa_image_shadow in IS. assert (E5 : sh 0x60a000 = sh 0x10000 + 0x5fa000 / 8) by reflexivity.
      destruct (sh_disjoint ff (fsize (ff_class f)) 0x10000 0x5fa000
                 ltac:(apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M64]) eq_refl (proj1 (fsize_facts _ K)) eq_refl
                 ltac:(clear - F1' F4'; unfold kFakeStackBytes in *; lia)); lia.
Qed.

Lemma asI_frame_blk_disjoint : forall A m md ff k age p n, pa_ainv A m md ->
  as_fframe A ff = Some (k, age) -> as_live A p = Some n -> ff + fsize k <= p - 16 \/ p + n <= ff.
Proof.
  intros A m md ff k age p n AI HF HL. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W.
  unfold as_fframe, as_fframe_ in HF. destruct (a_fframes A !! ff) as [f|] eqn:Hf; [|discriminate]. cbn in HF. injection HF as Hk Hage. subst k age.
  unfold as_live, as_live_ in HL. destruct (a_livemap A !! p) as [li|] eqn:Hl; [|discriminate]. cbn in HL. injection HL as HL. subst n.
  pose proof (frame_facts A m md ff f AI Hf) as FF. cbv zeta in FF. (first [ dand6 FF as K _ _ R1 R2 _ | destruct FF as (K & _ & _ & R1 & R2 & _) ]).
  (first [ pose proof ((bm_nth_fixed A)) as dR_17; dand8 dR_17 as E0 _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & _ & _ & E6 & _) ]).
  destruct (wfV A W) as (V1 & _). (first [ pose proof ((V1 p li Hl)) as dR_18; dand3 dR_18 as N U C | pose proof (V1 p li Hl) as (N & U & C) ]). cbv zeta in *.
  pose proof (live_user_where A p li p W Hl ltac:(lia)) as LW. destruct (li_chunk li) as [[c k]|sc] eqn:EC.
  - (first [ dand9 LW as CR Hk NR HC U2 IN RB1 RB2 SB | destruct LW as (CR & Hk & NR & HC & U2 & IN & RB1 & RB2 & SB) ]). cbn [user_of alloc_beg] in U2.
    pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in RB.
    (first [ pose proof ((primary_layout (a_sb A) c k (li_n li) CR ltac:(lia) HC)) as dR_20; dand3 dR_20 as L1 L2 _ | pose proof (primary_layout (a_sb A) c k (li_n li) CR ltac:(lia) HC) as (L1 & L2 & _) ]). cbn [user_of alloc_beg] in L1, L2. rewrite <- U2 in L1, L2.
    assert (B6a : a_b6 A <= chunk_addr (a_sb A) c k < a_b6 A + kSpaceReserve) by (apply primary_in_b6; [exact W| unfold kRegionSize, kFreeArrayOffset in *; lia]).
    assert (B6b : a_b6 A <= p + li_n li - 1 < a_b6 A + kSpaceReserve) by (apply primary_in_b6; [exact W| unfold kRegionSize, kFreeArrayOffset in *; lia]).
    unfold kFakeFramesOffset in *.
    destruct (bm_sep A 0 6 _ _ _ _ W E0 E6 ltac:(lia)); unfold a_fs in *; [right; lia| left; lia].
  - (first [ dand5 LW as Hin N2 EN U2 R | destruct LW as (Hin & N2 & EN & U2 & R) ]). destruct (In_nth_error' _ _ Hin) as [j Hj]. pose proof (bm_nth_sec A j sc Hj) as Ej.
    (first [ pose proof ((secondary_layout (cs_map sc) (cs_n sc) ltac:(lia))) as dR_22; dand7 dR_22 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout (cs_map sc) (cs_n sc) ltac:(lia)) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]). unfold kFakeFramesOffset in *.
    rewrite S6, EN in S3. rewrite EN in Ej.
    destruct (bm_sep A (15 + j) 6 _ _ _ _ W Ej E6 ltac:(lia)); unfold a_fs in *; [right; lia| left; lia].
Qed.

Lemma asI_frame_disjoint : forall A m md ff k age ff' k' age', pa_ainv A m md ->
  as_fframe A ff = Some (k, age) -> as_fframe A ff' = Some (k', age') -> ff <> ff' ->
  ff + fsize k <= ff' \/ ff' + fsize k' <= ff.
Proof.
  intros A m md ff k age ff' k' age' AI H1 H2 NE. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W.
  unfold as_fframe, as_fframe_ in H1, H2.
  destruct (a_fframes A !! ff) as [f|] eqn:Hf; [|discriminate]. destruct (a_fframes A !! ff') as [f'|] eqn:Hf'; [|discriminate].
  cbn in H1, H2. injection H1 as <- <-. injection H2 as <- <-. eapply live_frames_disjoint; eauto.
Qed.

Lemma le8_wz_inj : forall a b, le8 (Z_to_bv 64 a) = le8 (Z_to_bv 64 b) -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b E. rewrite <- (le_bytes_to_word_le8 (Z_to_bv 64 a)), <- (le_bytes_to_word_le8 (Z_to_bv 64 b)). rewrite E. reflexivity. Qed.

Lemma asI_sframe_flag : forall A m md ff k age, pa_ainv A m md -> as_fframe A ff = Some (k, age) ->
  exists fa, bytes_at (cl_segs LPA) (aview_of (pa_hull A) m) (ff + fsize k - 8) (le8 (wz fa))
    /\ pa_owned A fa /\ ~ in_image LPA fa /\ wr_at (cl_segs LPA) (aview_of (pa_hull A) m) fa 1
    /\ (forall ff' k' age', as_fframe A ff' = Some (k', age') -> ff' <> ff ->
          forall fa', bytes_at (cl_segs LPA) (aview_of (pa_hull A) m) (ff' + fsize k' - 8) (le8 (wz fa')) -> fa' <> fa).
Proof.
  intros A m md ff k age AI HF. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W. pose proof alloc_ceiling_val as CE.
  pose proof HF as HF0. unfold as_fframe, as_fframe_ in HF. destruct (a_fframes A !! ff) as [f|] eqn:Hf; [|discriminate]. cbn in HF. injection HF as Hk Hage. subst k age.
  pose proof (frame_facts A m md ff f AI Hf) as FF. cbv zeta in FF. (first [ dand10 FF as K E AG R1 R2 FS1 FS2 FSM SZ _ | destruct FF as (K & E & AG & R1 & R2 & FS1 & FS2 & FSM & SZ & _) ]).
  pose proof (ar_fsptrs _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) ff f Hf) as PTR. pose proof (ar_fsflags _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as FL.
  unfold a_fs in *. set (v := aview_of (ahull_of pa_image_ivs AL_pasan A) m) in *. change (aview_of (pa_hull A) m) with v.
  set (pos := ff_pos (a_fhint A (ff_class f)) (ff_class f) (ff_age f)) in *.
  pose proof (ff_pos_range (a_fhint A (ff_class f)) (ff_class f) (ff_age f) K) as PR. fold pos in PR.
  set (fa := fflag_addr (p_fs (a_pl A)) (ff_class f) pos) in *.
  pose proof (fflag_addr_range (p_fs (a_pl A)) (ff_class f) pos K PR) as FR. fold fa in FR.
  exists fa. split; [exact PTR|].
  assert (OWN : pa_owned A fa).
  { (first [ pose proof ((bm_nth_fixed A)) as dR_24; dand8 dR_24 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]).
    eapply (owned_rt A fa (a_fs A) kFakeStackBytes); [apply rt_fixed_in; mem_side| unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *; lia| |].
    - eapply (fixed_bm_no_live_user A 6); [exact W| lia| exact E6| unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *; lia].
    - intros LF. pose proof (live_frame_zone A fa W LF). unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset in *. lia. }
  split; [exact OWN|].
  (first [ pose proof ((app_facts _ _ FS1)) as dR_25; dand5 dR_25 as G1 G2 G3 G4 G5 | pose proof (app_facts _ _ FS1) as (G1 & G2 & G3 & G4 & G5) ]).
  split. { unfold in_image. cbn [cl_image_lo cl_image_hi LPA]. unfold kFakeStackBytes, kFakeFlagsOffset, kFakeFramesOffset in *. lia. }
  split. { (first [ pose proof ((FL (ff_class f) pos K PR)) as dR_26; dex1 dR_26 as b; destruct dR_26 as [U8 _] | pose proof ((FL (ff_class f) pos K PR)) as dR_26; dand3 dR_26 as b U8 _ | destruct (FL (ff_class f) pos K PR) as (b & U8 & _) ]). fold fa in U8.
           apply wr_at_of_mapped; [unfold kFakeStackBytes, kFakeFlagsOffset, kFakeFramesOffset in *; lia| unfold kFakeFramesOffset in *; lia|].
           intros i Hi. replace i with 0 by lia. eapply (bytes_at_nonnull _ v fa [Z_to_bv 8 b] 0 U8); [cbn; lia| apply pa_rom_high| unfold kFakeStackBytes, kFakeFlagsOffset, kFakeFramesOffset in *; lia]. }
  intros ff' k' age' HF' NE fa' B'.
  unfold as_fframe, as_fframe_ in HF'. destruct (a_fframes A !! ff') as [f'|] eqn:Hf'; [|discriminate]. cbn in HF'. injection HF' as Hk' Hage'. subst k' age'.
  pose proof (ar_fsptrs _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) ff' f' Hf') as PTR'. fold v in PTR'.
  pose proof (frame_facts A m md ff' f' AI Hf') as FF'. cbv zeta in FF'. (first [ dand4 FF' as K' E' AG' _ | destruct FF' as (K' & E' & AG' & _) ]).
  pose proof (ff_pos_range (a_fhint A (ff_class f')) (ff_class f') (ff_age f') K') as PR'.
  pose proof (fflag_addr_range (p_fs (a_pl A)) (ff_class f') _ K' PR') as FR'.
  intros EQ. subst fa'.
  pose proof (bytes_at_func _ v _ _ _ B' PTR' ltac:(rewrite !length_le8; reflexivity)) as LE. apply le8_wz_inj in LE.
  unfold a_fs in LE. apply wz_inj in LE; [| clear -FR G1 FS2 CE; kun; lia | clear -FR' G1 FS2 CE; kun; lia].
  unfold fa in LE. destruct (fflag_addr_inj _ _ _ _ _ K K' PR PR' LE) as [EK EP].
  (first [ pose proof ((wfF A W)) as dR_28; dand3 dR_28 as _ _ F3 | destruct (wfF A W) as (_ & _ & F3) ]). apply (F3 ff ff' f f' Hf Hf' ltac:(congruence) EK).
  apply (ff_pos_inj (a_fhint A (ff_class f)) (ff_class f)); [exact K| exact AG| rewrite EK; exact AG'|].
  unfold pos in EP. rewrite EP, EK. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma asI_release_spec : forall A m md ff k age, pa_ainv A m md -> as_fframe A ff = Some (k, age) ->
  as_fframe (as_release A ff) ff = None
  /\ (forall g, g <> ff -> as_fframe (as_release A ff) g = as_fframe A g)
  /\ (forall q, as_live (as_release A ff) q = as_live A q)
  /\ as_livebytes (as_release A ff) = as_livebytes A /\ as_tinycred (as_release A ff) = as_tinycred A
  /\ as_seccred (as_release A ff) = as_seccred A     (* [comment removed for export] *)
  /\ as_primcred (as_release A ff) = as_primcred A   (* [comment removed for export] *)
  /\ as_nlive (as_release A ff) = as_nlive A
  /\ pa_hull (as_release A ff) = pa_hull A /\ pa_eager (as_release A ff) = pa_eager A
  /\ (forall a, pa_owned (as_release A ff) a <-> (pa_owned A a \/ ff <= a < ff + fsize k - 8 \/ sh ff <= a < sh ff + fsize k / 8)).
Proof.
  intros A m md ff k age AI HF. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W.
  split; [apply as_fframe_release_same|]. split; [intros; apply as_fframe_release_other; assumption|].
  split; [intros; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  pose proof HF as HF0. unfold as_fframe, as_fframe_ in HF. destruct (a_fframes A !! ff) as [f|] eqn:Hf; [|discriminate]. cbn in HF. injection HF as Hk Hage. subst k age.
  pose proof (frame_facts A m md ff f AI Hf) as FF. cbv zeta in FF. (first [ dand15 FF as K E AG R1 R2 FS1 FS2 FSM SZ M64 AL S1 S2 SR1 SR2 | destruct FF as (K & E & AG & R1 & R2 & FS1 & FS2 & FSM & SZ & M64 & AL & S1 & S2 & SR1 & SR2) ]).
  (first [ pose proof ((bm_nth_fixed A)) as dR_30; dand8 dR_30 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]).
  assert (DEL : forall g, delete ff (a_fframes A) !! g = if decide (g = ff) then None else a_fframes A !! g).
  { intros g. destruct (decide (g = ff)) as [->|NE]; [apply lookup_delete_eq| apply lookup_delete_ne; congruence]. }
  intros a. unfold pa_owned, as_release. athin.
  unfold aowned_, fs_shadow_owned_, in_live_user_, in_live_frame_, in_live_frame_shadow_. unfold a_fs in *.
  assert (OTHER : forall (X : Prop) g f', a_fframes A !! g = Some f' -> (g <> ff -> delete ff (a_fframes A) !! g = Some f' -> X) ->
                  (g = ff -> f' = f -> X) -> X).
  { intros X g f' Hg H1 H2. destruct (Z.eq_dec g ff) as [EG|NE]; [apply H2; [exact EG| subst g; congruence]|]. apply H1; [exact NE|]. rewrite DEL, decide_False by exact NE. exact Hg. }
  split.
  - intros [[S|[[(IR & NU & NF)|[HS|[R NFS]]]|GH]]|IS].
    + left. left. left. exact S.
    + destruct (Z.lt_ge_cases a ff) as [LT|GE]; [|destruct (Z.lt_ge_cases a (ff + fsize (ff_class f) - 8)) as [LT2|GE2]].
      * left. left. right. left. left. split; [exact IR|]. split; [exact NU|]. ((first [ intro dR_73; dex2 dR_73 as g f'; destruct dR_73 as [Hg Hr] | intro dR_73; dand4 dR_73 as g f' Hg Hr | intros (g & f' & Hg & Hr) ])).
        apply (OTHER False g f' Hg); [intros NE Hd; apply NF; exists g, f'; split; assumption| intros -> ->; lia].
      * right. left. lia.
      * left. left. right. left. left. split; [exact IR|]. split; [exact NU|]. ((first [ intro dR_74; dex2 dR_74 as g f'; destruct dR_74 as [Hg Hr] | intro dR_74; dand4 dR_74 as g f' Hg Hr | intros (g & f' & Hg & Hr) ])).
        apply (OTHER False g f' Hg); [intros NE Hd; apply NF; exists g, f'; split; assumption| intros -> ->; lia].
    + left. left. right. left. right. left. exact HS.
    + destruct (Z.lt_ge_cases a (sh ff)) as [LT|GE]; [|destruct (Z.lt_ge_cases a (sh ff + fsize (ff_class f) / 8)) as [LT2|GE2]].
      * left. left. right. left. right. right. split; [exact R|]. ((first [ intro dR_75; dex2 dR_75 as g f'; destruct dR_75 as [Hg Hr] | intro dR_75; dand4 dR_75 as g f' Hg Hr | intros (g & f' & Hg & Hr) ])).
        apply (OTHER False g f' Hg); [intros NE Hd; apply NFS; exists g, f'; split; assumption| intros -> ->; lia].
      * right. right. lia.
      * left. left. right. left. right. right. split; [exact R|]. ((first [ intro dR_76; dex2 dR_76 as g f'; destruct dR_76 as [Hg Hr] | intro dR_76; dand4 dR_76 as g f' Hg Hr | intros (g & f' & Hg & Hr) ])).
        apply (OTHER False g f' Hg); [intros NE Hd; apply NFS; exists g, f'; split; assumption| intros -> ->; lia].
    + left. left. right. right. exact GH.
    + left. right. exact IS.
  - intros [[[S|[[(IR & NU & NF)|[HS|[R NFS]]]|GH]]|IS]|[FR|FSH]].
    + left. left. exact S.
    + left. right. left. left. split; [exact IR|]. split; [exact NU|]. ((first [ intro dR_77; dex2 dR_77 as g f'; destruct dR_77 as [Hg Hr] | intro dR_77; dand4 dR_77 as g f' Hg Hr | intros (g & f' & Hg & Hr) ])). apply NF. exists g, f'. rewrite DEL in Hg. destruct (decide (g = ff)); [discriminate|]. split; assumption.
    + left. right. left. right. left. exact HS.
    + left. right. left. right. right. split; [exact R|]. ((first [ intro dR_78; dex2 dR_78 as g f'; destruct dR_78 as [Hg Hr] | intro dR_78; dand4 dR_78 as g f' Hg Hr | intros (g & f' & Hg & Hr) ])). apply NFS. exists g, f'. rewrite DEL in Hg. destruct (decide (g = ff)); [discriminate|]. split; assumption.
    + left. right. right. exact GH.
    + right. exact IS.
    + (* [comment removed for export] *)
      left. right. left. left. split; [|split].
      * exists (p_fs (a_pl A)), kFakeStackBytes. split; [apply rt_fixed_in; mem_side| unfold kFakeFramesOffset in *; lia].
      * change (~ in_live_user A a). eapply (fixed_bm_no_live_user A 6); [exact W| lia| exact E6| unfold a_fs, kFakeFramesOffset in *; lia].
      * ((first [ intro dR_79; dex2 dR_79 as g f'; destruct dR_79 as [Hg Hr] | intro dR_79; dand4 dR_79 as g f' Hg Hr | intros (g & f' & Hg & Hr) ])). rewrite DEL in Hg. destruct (decide (g = ff)) as [|NE]; [discriminate|].
        destruct (live_frames_disjoint A ff f g f' W Hf Hg ltac:(congruence)); lia.
    + (* [comment removed for export] *)
      left. right. left. right. right. split; [lia|].
      ((first [ intro dR_80; dex2 dR_80 as g f'; destruct dR_80 as [Hg Hr] | intro dR_80; dand4 dR_80 as g f' Hg Hr | intros (g & f' & Hg & Hr) ])). rewrite DEL in Hg. destruct (decide (g = ff)) as [|NE]; [discriminate|].
      pose proof (frame_facts A m md g f' AI Hg) as FF'. cbv zeta in FF'. (first [ dand11 FF' as K' _ _ _ _ _ _ _ _ M64' _ | destruct FF' as (K' & _ & _ & _ & _ & _ & _ & _ & _ & M64' & _) ]).
      destruct (sh_disjoint ff (fsize (ff_class f)) g (fsize (ff_class f'))
                 ltac:(apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M64]) ltac:(apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M64'])
                 ltac:(apply (proj1 (fsize_facts _ K))) ltac:(apply (proj1 (fsize_facts _ K'))) (live_frames_disjoint A ff f g f' W Hf Hg ltac:(congruence))); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma visible_in_hull : forall (H : hull) a, hidc H (wz a) = false -> 0 <= a < 2^64 -> exists lo hi, In (lo, hi) H /\ lo <= a < hi.
Proof.
  intros H a V Ha. unfold hidc in V. apply negb_false_iff in V. unfold in_hullb in V. apply existsb_exists in V as ([lo hi] & Hin & B).
  unfold in_ivb in B. cbn [fst snd] in B. rewrite unsigned_lit in B by lia. apply andb_true_iff in B as [B1 B2].
  apply Z.leb_le in B1. apply Z.ltb_lt in B2. exists lo, hi. split; [exact Hin| lia].
Qed.

Lemma classes_regions_inv : forall sb reg n r, In r (classes_regions_ sb reg n) ->
  exists c, 1 <= c <= Z.of_nat n /\ In r (class_regions_ sb (reg c) c).
Proof.
  intros sb reg n. induction n as [|n IH]; intros r H; [destruct H|].
  cbn [classes_regions_] in H. apply in_app_iff in H as [H|H].
  - (first [ pose proof ((IH r H)) as dR_32; dex1 dR_32 as c; destruct dR_32 as [Hc Hr] | pose proof ((IH r H)) as dR_32; dand3 dR_32 as c Hc Hr | destruct (IH r H) as (c & Hc & Hr) ]). exists c. split; [lia| exact Hr].
  - exists (Z.of_nat (S n)). split; [lia| exact H].
Qed.
Lemma class_regions_inv : forall sb R c r, In r (class_regions_ sb R c) ->
  let rb := region_beg sb c in
  (r = (rb, rg_mapped_user R) /\ rg_mapped_user R <> 0) \/ (r = shadow_region rb (rg_mapped_user R) /\ rg_mapped_user R <> 0) \/
  (r = (rb + kFreeArrayOffset, rg_mapped_fa R) /\ rg_mapped_fa R <> 0) \/ (r = shadow_region (rb + kFreeArrayOffset) (rg_mapped_fa R) /\ rg_mapped_fa R <> 0).
Proof.
  intros sb R c r H. cbv zeta. unfold class_regions_ in H. cbv zeta in H. apply in_app_iff in H as [H|H].
  - destruct (Z.eqb_spec (rg_mapped_user R) 0); [destruct H|]. destruct H as [<-|[<-|[]]]; [left| right; left]; split; auto.
  - destruct (Z.eqb_spec (rg_mapped_fa R) 0); [destruct H|]. destruct H as [<-|[<-|[]]]; [right; right; left| right; right; right]; split; auto.
Qed.

Lemma shadow_word_in_region : forall b s x, b <= x < b + s ->
  fst (shadow_region b s) <= sh x - sh x mod 8 /\ sh x - sh x mod 8 + 8 <= fst (shadow_region b s) + snd (shadow_region b s).
Proof.
  intros b s x Hx. unfold shadow_region. cbn [fst snd].
  set (lo := round_down (sh b) 8). set (hi := round_up (sh (b + s - 1) + 1) 8).
  pose proof (round_down_le (sh b) 8 ltac:(lia)). pose proof (round_down_mod (sh b) 8 ltac:(lia)).
  pose proof (round_up_ge (sh (b + s - 1) + 1) 8 ltac:(lia)). pose proof (round_up_mod (sh (b + s - 1) + 1) 8 ltac:(lia)).
  fold lo in H, H0. fold hi in H1, H2.
  pose proof (round_down_gt (sh b) 8 ltac:(lia)). fold lo in H3.
  pose proof (sh_mono b x ltac:(lia)). pose proof (sh_mono x (b + s - 1) ltac:(lia)).
  pose proof (Z.mod_pos_bound (sh x) 8 ltac:(lia)). pose proof (Z_div_mod_eq_full (sh x) 8).
  pose proof (Z_div_exact_full_2 lo 8 ltac:(lia) H0). pose proof (Z_div_exact_full_2 hi 8 ltac:(lia) H2).
  split; lia.
Qed.
Lemma shadow_region_high : forall b s, kHighMemBeg <= b -> b + s <= 2^47 -> 0 < s ->
  kHighShadowMapBeg <= fst (shadow_region b s) /\ fst (shadow_region b s) + snd (shadow_region b s) <= kHighMemBeg.
Proof.
  intros b s H1 H2 H3. unfold shadow_region. cbn [fst snd].
  pose proof (sh_high_range b ltac:(lia)) as [A1 _]. pose proof (sh_high_range (b + s - 1) ltac:(lia)) as [_ A2].
  pose proof (round_down_gt (sh b) 8 ltac:(lia)). pose proof (round_down_mod (sh b) 8 ltac:(lia)).
  pose proof (round_up_lt (sh (b + s - 1) + 1) 8 ltac:(lia)). pose proof (round_up_mod (sh (b + s - 1) + 1) 8 ltac:(lia)).
  pose proof (Z_div_exact_full_2 _ 8 ltac:(lia) H0). pose proof (Z_div_exact_full_2 _ 8 ltac:(lia) H5).
  unfold kHighShadowMapBeg, kHighMemBeg in *. split; lia.
Qed.
Lemma shadow_region_len_nonneg : forall b s, 0 < s -> 0 <= snd (shadow_region b s).
Proof.
  intros b s Hs. unfold shadow_region. cbn [snd]. pose proof (round_down_le (sh b) 8 ltac:(lia)).
  pose proof (round_up_ge (sh (b + s - 1) + 1) 8 ltac:(lia)). pose proof (sh_mono b (b + s - 1) ltac:(lia)). lia.
Qed.
(* [comment removed for export] *)
Lemma shadow_region_aligned : forall b s, b mod 64 = 0 -> s mod 64 = 0 -> 0 < s ->
  shadow_region b s = (sh b, s / 8).
Proof.
  intros b s Hb Hs Hp. unfold shadow_region.
  assert (SB : sh b mod 8 = 0) by (unfold sh, kShadowOffset; lia).
  assert (E2 : sh (b + s - 1) + 1 = sh b + s / 8) by (unfold sh; lia).
  rewrite E2. replace (round_down (sh b) 8) with (sh b) by (unfold round_down; lia).
  assert (S8 : (sh b + s / 8) mod 8 = 0) by (unfold sh, kShadowOffset in *; lia).
  rewrite round_up_id; [f_equal; lia| lia| exact S8].
Qed.

(* [comment removed for export] *)
Lemma shadow_word_mapped_of : forall A m b s x,
  In (shadow_region b s) (aregions AL_pasan A) -> b <= x < b + s ->
  mapped (aview_of (pa_hull A) m) (fst (shadow_region b s)) (snd (shadow_region b s)) ->
  mapped (aview_of (pa_hull A) m) (sh x - sh x mod 8) 8.
Proof.
  intros A m b s x Hin Hx M. pose proof (shadow_word_in_region b s x Hx) as [W1 W2].
  eapply mapped_sub; [exact M| exact W1| exact W2].
Qed.

(* [comment removed for export] *)
Lemma vis0_cases : forall P b n, In (b, n) (VIS0 P) ->
  (b, n) = (p_gvec P, 4096) \/ (b, n) = (p_dvec P, 4096) \/ (b, n) = (p_frames0 P, kStackStoreBlockBytes) \/
  (b, n) = (p_nodes0 P, kDepotNodesBlock) \/ (b, n) = (p_fs P, kFakeStackBytes) \/ (b, n) = (p_thr P, 4096) \/
  (b, n) = (p_m11 P, 4096) \/ (b, n) = (p_ctx P, 0x10000) \/ (b, n) = (p_dtls P, 4096) \/ (b, n) = (p_ri P, 4096) \/
  (b, n) = (p_itab P, 0x38e000) \/ (b, n) = (p_m64k P, 0x10000) \/ (b, n) = (0x10000, 0x5fa000) \/ (b, n) = stack_band_iv.
Proof. intros P b n H. cbn -[stack_band_iv] in H. intuition (try (symmetry; assumption)). all: left + right; congruence. Qed.

(* [comment removed for export] *)
Lemma shadow_word_mapped_hidden : forall A m md b s x, pa_ainv A m md ->
  In (shadow_region b s) (aregions AL_pasan A) -> b <= x < b + s ->
  ((4096 <= b /\ b + s <= kLowShadowMapBeg) \/ (kHighMemBeg <= b /\ b + s <= 2^47)) -> b mod 64 = 0 -> s mod 64 = 0 ->
  (forall b' n', In (b', n') (VIS0 (a_pl A)) -> b + s <= b' \/ b' + n' <= b) ->
  mapped (aview_of (pa_hull A) m) (sh x - sh x mod 8) 8.
Proof.
  intros A m md b s x AI Hin Hx HR Ab As SEP. pose proof (proj1 (ai_hidden _ _ _ _ _ _ _ AI)) as HID.
  pose proof (shadow_word_in_region b s x Hx) as [W1 W2].
  rewrite (shadow_region_aligned b s Ab As ltac:(lia)) in Hin, W1, W2. cbn [fst snd] in W1, W2.
  pose proof (Z_div_exact_full_2 s 64 ltac:(lia) As) as ES.
  assert (E2 : sh (b + s - 1) + 1 = sh b + s / 8) by (unfold sh; lia).
  assert (SM : forall z, sh b <= z < sh b + s / 8 -> in_shadow_strict z).
  { intros z Hz. apply (sh_iv_strict b s z); [apply (mod0_down _ 64 8); [exists 8; reflexivity| exact Ab]
      | apply (mod0_down _ 64 8); [exists 8; reflexivity| exact As] | lia | exact HR | exact Hz]. }
  pose proof (SM (sh b) ltac:(lia)) as SB. pose proof (SM (sh b + s / 8 - 1) ltac:(lia)) as ST.
  unfold in_shadow_strict, kLowShadowBeg, kShadowGapBeg, kHighShadowMapBeg, kHighMemBeg in SB, ST.
  intros i Hi. unfold aview_of. rewrite view_visible.
  2:{ apply (zrange_visible_hidc (pa_hull A) (sh b) (sh b + s / 8) (sh x - sh x mod 8) 8);
        first [apply pa_hull_region; exact Hin | lia]. }
  apply (fun G => proj1 (HID _ G)). split.
  { apply strict_in_maps. apply SM. lia. }
  ((first [ intro dR_81; dex2 dR_81 as b' n'; destruct dR_81 as [Hv Rv] | intro dR_81; dand4 dR_81 as b' n' Hv Rv | intros (b' & n' & Hv & Rv) ])). destruct (SEP b' n' Hv) as [D|D].
  - (* [comment removed for export] *)
    assert (sh (b + s - 1) < kShadowOffset + b' / 8) by (unfold sh; lia). lia.
  - assert (kShadowOffset + (b' + n') / 8 <= sh b) by (unfold sh; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma vis0_clear_primary : forall A b' n', WF A -> In (b', n') (VIS0 (a_pl A)) ->
  a_sb A + kSpaceSize <= b' \/ b' + n' <= a_sb A.
Proof.
  intros A b' n' W Hv. pose proof alloc_ceiling_val as CE. (first [ pose proof ((sb_facts A W)) as dR_33; dand5 dR_33 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]).
  (first [ pose proof ((bm_nth_fixed A)) as dR_34; dand15 dR_34 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
  unfold a_sb, a_b6, a_thr, a_ctx, a_fs, a_nodes0, a_frames0, a_itab, a_m64k in *.
  assert (SEP : forall i bb ss, (1 <= i)%nat -> nth_error (big_maps A) i = Some (bb, ss) ->
                p_b6 (a_pl A) + kSpaceReserve <= bb \/ bb + ss <= p_b6 (a_pl A)).
  { intros i bb ss Hi Hn. destruct (bm_sep A 0 i _ _ _ _ W E0 Hn ltac:(lia)); lia. }
  destruct (vis0_cases _ _ _ Hv) as [Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|Q]]]]]]]]]]]]]; [injection Q as -> -> ..|].
  - destruct (SEP 11%nat _ _ ltac:(lia) E11); unfold kSpaceReserve, kSpaceSize in *; lia.
  - destruct (SEP 12%nat _ _ ltac:(lia) E12); unfold kSpaceReserve, kSpaceSize in *; lia.
  - destruct (SEP 8%nat _ _ ltac:(lia) E8); unfold kSpaceReserve, kSpaceSize in *; lia.
  - destruct (SEP 7%nat _ _ ltac:(lia) E7); unfold kSpaceReserve, kSpaceSize in *; lia.
  - destruct (SEP 6%nat _ _ ltac:(lia) E6); unfold kSpaceReserve, kSpaceSize in *; lia.
  - destruct (SEP 4%nat _ _ ltac:(lia) E4); unfold kSpaceReserve, kSpaceSize in *; lia.
  - destruct (SEP 13%nat _ _ ltac:(lia) E13); unfold kSpaceReserve, kSpaceSize in *; lia.
  - destruct (SEP 5%nat _ _ ltac:(lia) E5); unfold kSpaceReserve, kSpaceSize in *; lia.
  - destruct (SEP 14%nat _ _ ltac:(lia) E14); unfold kSpaceReserve, kSpaceSize in *; lia.
  - unfold p_ri. lia.
  - destruct (SEP 9%nat _ _ ltac:(lia) E9); unfold kSpaceReserve, kSpaceSize in *; lia.
  - destruct (SEP 10%nat _ _ ltac:(lia) E10); unfold kSpaceReserve, kSpaceSize in *; lia.
  - unfold kHighMemBeg in *. lia.
  - unfold stack_band_iv in Q. injection Q as -> ->. lia.
Qed.
Lemma vis0_clear_sec : forall A sc b' n', WF A -> In sc (sr_chunks (a_sec A)) -> In (b', n') (VIS0 (a_pl A)) ->
  cs_map sc + map_size (cs_n sc) <= b' \/ b' + n' <= cs_map sc.
Proof.
  intros A sc b' n' W Hsc Hv. pose proof alloc_ceiling_val as CE. (first [ pose proof ((sb_facts A W)) as dR_35; dand5 dR_35 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]).
  (first [ pose proof ((bm_nth_fixed A)) as dR_36; dand15 dR_36 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
  destruct (In_nth_error' _ _ Hsc) as [j Hj]. pose proof (bm_nth_sec A j sc Hj) as Ej.
  (first [ pose proof ((sec_chunk_bounds A sc W Hsc)) as dR_37; dand5 dR_37 as _ _ B3 B4 _ | pose proof (sec_chunk_bounds A sc W Hsc) as (_ & _ & B3 & B4 & _) ]).
  unfold a_sb, a_b6, a_thr, a_ctx, a_fs, a_nodes0, a_frames0, a_itab, a_m64k in *.
  assert (SEP : forall i bb ss, (i <= 14)%nat -> nth_error (big_maps A) i = Some (bb, ss) ->
                cs_map sc + map_size (cs_n sc) <= bb \/ bb + ss <= cs_map sc).
  { intros i bb ss Hi Hn. destruct (bm_sep A (15 + j) i _ _ _ _ W Ej Hn ltac:(lia)); lia. }
  destruct (vis0_cases _ _ _ Hv) as [Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|Q]]]]]]]]]]]]]; [injection Q as -> -> ..|].
  - exact (SEP 11%nat _ _ ltac:(lia) E11).
  - exact (SEP 12%nat _ _ ltac:(lia) E12).
  - exact (SEP 8%nat _ _ ltac:(lia) E8).
  - exact (SEP 7%nat _ _ ltac:(lia) E7).
  - exact (SEP 6%nat _ _ ltac:(lia) E6).
  - exact (SEP 4%nat _ _ ltac:(lia) E4).
  - exact (SEP 13%nat _ _ ltac:(lia) E13).
  - exact (SEP 5%nat _ _ ltac:(lia) E5).
  - exact (SEP 14%nat _ _ ltac:(lia) E14).
  - destruct (SEP 0%nat _ _ ltac:(lia) E0); unfold p_ri, kSpaceReserve, kSpaceSize in *; lia.
  - exact (SEP 9%nat _ _ ltac:(lia) E9).
  - exact (SEP 10%nat _ _ ltac:(lia) E10).
  - apply app_facts in B3. clear - B3 B4. lia.
  - unfold stack_band_iv in Q. injection Q as -> ->. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma place_extra : forall A m md, pa_ainv A m md ->
  Forall (fun lh => 0 <= fst lh /\ fst lh <= snd lh <= 2^47) (p_extra (a_pl A)) /\
  (forall lo hi a, In (lo, hi) (p_extra (a_pl A)) -> lo <= a < hi ->
      (0 <= a <= kLowMemEnd \/ kHighMemBeg <= a < alloc_ceiling) ->
      forall z, sh a - sh a mod 8 <= z < sh a - sh a mod 8 + 8 -> exists lo' hi', In (lo', hi') (p_extra (a_pl A)) /\ lo' <= z < hi') /\
  (forall lo hi, In (lo, hi) (p_extra (a_pl A)) -> lo mod 4096 = 0 /\ hi mod 4096 = 0) /\   (* [comment removed for export] *)
  cl_image_hi LPA <= p_brk (a_pl A) <= cl_image_hi LPA + 2^31 /\
  (forall pc ra, In pc pa_site_pcs -> In ra (cl_sites LPA) -> In [pc; ra] (p_dkeys (a_pl A)) /\ In [pc] (p_dkeys (a_pl A))) /\
  hull_bytes (p_extra (a_pl A)) <= 2^28 + 2^26 /\   (* [comment removed for export] *)
  (forall lo hi a, In (lo, hi) (p_extra (a_pl A)) -> lo <= a < hi -> ~ (p_sb (a_pl A) <= a < p_sb (a_pl A) + kSpaceSize)) /\   (* [comment removed for export] *)
  TLIM_MIN <= p_tlim (a_pl A).   (* [comment removed for export] *)
Proof. intros A m md AI. pose proof (ai_extra _ _ _ _ _ _ _ AI) as P. unfold wf_extra in P. exact P. Qed.

Lemma sh_low_range0 : forall a, 0 <= a <= kLowMemEnd -> 0x7fff8000 <= sh a < 0x8fff7000.
Proof.
  intros a H. unfold sh, kShadowOffset, kLowMemEnd in *. pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  assert (a / 8 <= 0x7fff7fff / 8) by (apply Z.div_le_mono; lia). change (0x7fff7fff / 8) with 0xfffefff in *. lia.
Qed.
Lemma align8_lo : forall x B, B mod 8 = 0 -> B <= x -> B <= x - x mod 8.
Proof.
  intros x B HB Hx. pose proof (Z_div_mod_eq_full x 8). pose proof (Z_div_mod_eq_full B 8). pose proof (Z.mod_pos_bound x 8).
  assert (B / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma align8_hi : forall x E, E mod 8 = 0 -> x < E -> x - x mod 8 + 8 <= E.
Proof.
  intros x E HE Hx. pose proof (Z_div_mod_eq_full x 8). pose proof (Z_div_mod_eq_full E 8). pose proof (Z.mod_pos_bound x 8).
  assert (x / 8 <= (E - 1) / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z_div_mod_eq_full (E - 1) 8). pose proof (Z.mod_pos_bound (E - 1) 8). lia.
Qed.
(* [comment removed for export] *)
Lemma vis_word_back : forall a b n z, 0 <= a -> 0 <= b -> b mod 64 = 0 -> n mod 64 = 0 -> 0 <= n ->
  sh a - sh a mod 8 <= z < sh a - sh a mod 8 + 8 -> kShadowOffset + b / 8 <= z < kShadowOffset + (b + n) / 8 -> b <= a < b + n.
Proof.
  intros a b n z Ha Hb Mb Mn Hn Hz Hv.
  pose proof (Z_div_mod_eq_full a 8) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ra.
  pose proof (Z_div_mod_eq_full (sh a) 8) as Ds. pose proof (Z.mod_pos_bound (sh a) 8 ltac:(lia)) as Rs.
  pose proof (Z_div_exact_full_2 b 64 ltac:(lia) Mb) as Eb.
  assert (Mbn : (b + n) mod 64 = 0) by (rewrite Z.add_mod, Mb, Mn by lia; reflexivity).
  pose proof (Z_div_exact_full_2 (b + n) 64 ltac:(lia) Mbn) as Ebn.
  assert (E8 : b / 8 = 8 * (b / 64)) by (rewrite Eb at 1; replace (64 * (b / 64)) with (8 * (b / 64) * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
  assert (E8n : (b + n) / 8 = 8 * ((b + n) / 64)) by (rewrite Ebn at 1; replace (64 * ((b + n) / 64)) with (8 * ((b + n) / 64) * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
  unfold sh, kShadowOffset in *. change 0x7fff8000 with (8 * 0xffff000) in *.
  assert (L1 : b / 64 <= sh a / 8 - 0xffff000) by (unfold sh, kShadowOffset; lia).
  pose proof (Z.div_le_mono b a 8 ltac:(lia)) as M1.
  assert (A1 : b <= a \/ a < b) by lia. destruct A1 as [A1|A1].
  - split; [exact A1|].
    destruct (Z.lt_ge_cases a (b + n)) as [L|G]; [exact L|]. exfalso.
    pose proof (Z.div_le_mono (b + n) a 8 ltac:(lia)) as M2. unfold sh, kShadowOffset in *. lia.
  - exfalso. pose proof (Z.div_le_mono a (b - 1) 8 ltac:(lia)) as M2.
    pose proof (Z_div_mod_eq_full (b - 1) 8). pose proof (Z.mod_pos_bound (b - 1) 8 ltac:(lia)). unfold sh, kShadowOffset in *. lia.
Qed.
Lemma in_ranges_dec : forall (V : list (Z * Z)) a,
  (exists b n, In (b, n) V /\ b <= a < b + n) \/ (forall b n, In (b, n) V -> ~ (b <= a < b + n)).
Proof.
  induction V as [|[b n] V IH]; intros a.
  - right. intros b n [].
  - destruct (IH a) as [(b' & n' & Hin & R)|NO]; [left; exists b', n'; split; [right; exact Hin| exact R]|].
    destruct (Z_le_dec b a) as [H1|H1]; [destruct (Z_lt_dec a (b + n)) as [H2|H2]|].
    + left. exists b, n. split; [left; reflexivity| lia].
    + right. intros b' n' [E|Hin]; [injection E as <- <-; lia| exact (NO _ _ Hin)].
    + right. intros b' n' [E|Hin]; [injection E as <- <-; lia| exact (NO _ _ Hin)].
Qed.
(* [comment removed for export] *)
Lemma vis0_aligned : forall A b n, WF A -> In (b, n) (VIS0 (a_pl A)) ->
  (b, n) = stack_band_iv \/ (0 <= b /\ b mod 64 = 0 /\ n mod 64 = 0 /\ 0 <= n).
Proof.
  intros A b n W Hv. (first [ pose proof ((place_facts A W)) as dR_38; dand14 dR_38 as Pthr Pctx Pn0 Pf0 Pfs Pitab Pm64k Pgvec Pdvec Pm11 Pdtls Ppa Psp0 _ | pose proof (place_facts A W) as (Pthr & Pctx & Pn0 & Pf0 & Pfs & Pitab & Pm64k & Pgvec & Pdvec & Pm11 & Pdtls & Ppa & Psp0 & _) ]).
  cbv zeta in Pthr, Pctx, Pn0, Pf0, Pfs, Pitab, Pm64k, Pgvec, Pdvec, Pm11, Pdtls, Ppa.
  (first [ pose proof ((sb_facts A W)) as dR_39; dand5 dR_39 as _ SBA HB6 RSB _ | pose proof (sb_facts A W) as (_ & SBA & HB6 & RSB & _) ]). unfold a_sb, a_b6 in *.
  assert (D : (64 | 4096)) by (exists 64; reflexivity).
  assert (G : forall p k, app_rangeA AL_pasan p k /\ p + k <= alloc_ceiling /\ p mod 4096 = 0 -> 0 <= p /\ p mod 64 = 0).
  { (intros p k; (first [ intro dR_82; dand3 dR_82 as X1 _ X3 | intros (X1 & _ & X3) ])). split; [pose proof (app_facts _ _ X1); lia| apply (mod0_down _ 4096 64); [exact D| exact X3]]. }
  destruct (vis0_cases _ _ _ Hv) as [Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|Q]]]]]]]]]]]]];
    [injection Q as -> -> .. | left; exact Q]; right.
  all: try match goal with |- 0 <= ?p /\ ?p mod 64 = 0 /\ _ /\ _ =>
         first [ destruct (G p _ Pgvec) as [Y1 Y2] | destruct (G p _ Pdvec) as [Y1 Y2] | destruct (G p _ Pf0) as [Y1 Y2]
               | destruct (G p _ Pn0) as [Y1 Y2] | destruct (G p _ Pfs) as [Y1 Y2] | destruct (G p _ Pthr) as [Y1 Y2]
               | destruct (G p _ Pm11) as [Y1 Y2] | destruct (G p _ Pctx) as [Y1 Y2] | destruct (G p _ Pdtls) as [Y1 Y2]
               | destruct (G p _ Pitab) as [Y1 Y2] | destruct (G p _ Pm64k) as [Y1 Y2] ];
         split; [exact Y1| split; [exact Y2| split; [reflexivity| unfold kStackStoreBlockBytes, kDepotNodesBlock, kFakeStackBytes; lia]]] end.
  - (* [comment removed for export] *) unfold p_ri, kSpaceSize, kHighMemBeg in *. split; [lia|]. split; [| split; [reflexivity| lia]].
    rewrite Z.add_mod by lia. rewrite (mod0_down _ 0x10000 64 ltac:(exists 1024; reflexivity) SBA). reflexivity.
  - (* [comment removed for export] *) OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity || lia.
Qed.

(* [comment removed for export] *)
Lemma stack_shadow_word_mapped : forall A m md w, pa_ainv A m md ->
  fst stack_shadow_iv <= w -> w + 8 <= kHighMemBeg ->
  mapped (aview_of (pa_hull A) m) w 8.
Proof.
  intros A m md w AI H1 H2. (first [ pose proof (stack_shadow_iv_facts) as dR_40; dand4 dR_40 as SF1 SF2 SF3 SF4 | pose proof stack_shadow_iv_facts as (SF1 & SF2 & SF3 & SF4) ]).
  (first [ pose proof ((ar_maps _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_41; dand4 dR_41 as _ _ M3 _ | pose proof (ar_maps _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & _ & M3 & _) ]).
  change (aview_of (ahull_of pa_image_ivs AL_pasan A) m) with (aview_of (pa_hull A) m) in M3.
  eapply mapped_sub; [exact M3| exact H1| lia].
Qed.

(* [comment removed for export] *)
Lemma extra_shadow_mapped : forall A m md a lo hi, pa_ainv A m md ->
  In (lo, hi) (p_extra (a_pl A)) -> lo <= a < hi -> ~ (cl_image_lo LPA <= a < cl_image_hi LPA) ->
  (0 <= a <= kLowMemEnd \/ kHighMemBeg <= a < alloc_ceiling) -> ~ pa_owned A a ->
  mapped (aview_of (pa_hull A) m) (sh a - sh a mod 8) 8.
Proof.
  intros A m md a lo hi AI HinX R NIM APP NOW. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W. pose proof alloc_ceiling_val as CE.
  (first [ pose proof ((place_extra A m md AI)) as dR_42; dand5 dR_42 as WX1 WX2 _ BRK _ | pose proof (place_extra A m md AI) as (WX1 & WX2 & _ & BRK & _) ]). pose proof (ai_hidden _ _ _ _ _ _ _ AI) as [HID1 _].
  cbn [cl_image_lo cl_image_hi LPA] in BRK.
  (first [ pose proof ((bm_nth_fixed A)) as dR_43; dand15 dR_43 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
  assert (NN : 0 <= a) by (unfold kLowMemEnd, kHighMemBeg in APP; lia).
  pose proof (Z.mod_pos_bound (sh a) 8 ltac:(lia)) as MB. pose proof (Z_div_mod_eq_full (sh a) 8) as DM.
  assert (SHP : 8 <= sh a) by (unfold sh, kShadowOffset; pose proof (Z.div_pos a 8 NN ltac:(lia)); lia).
  assert (OWNF : forall i bb bs, (1 <= i <= 14)%nat -> i <> 6%nat -> nth_error (big_maps A) i = Some (bb, bs) ->
                 In (bb, bs) (runtime_maps A) -> bb <= a < bb + bs -> False).
  { intros i bb bs Hi N6 Hn Hrt Ha. apply NOW. eapply (owned_rt A a bb bs); [exact Hrt| exact Ha| |].
    - eapply (fixed_bm_no_live_user A i); [exact W| exact Hi| exact Hn| exact Ha].
    - eapply (fixed_bm_no_live_frame A i); [exact W| lia| exact N6| exact Hn| exact Ha]. }
  destruct (in_ranges_dec (VIS0 (a_pl A)) a) as [(b' & n' & Hv & Rv)|OUT].
  - (* [comment removed for export] *)
    destruct (vis0_cases _ _ _ Hv) as [Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|Q]]]]]]]]]]]]]; injection Q as -> ->.
    + exfalso. eapply (OWNF 11%nat); [lia| lia| exact E11| apply rt_fixed_in; mem_side| exact Rv].
    + exfalso. eapply (OWNF 12%nat); [lia| lia| exact E12| apply rt_fixed_in; mem_side| exact Rv].
    + exfalso. eapply (OWNF 8%nat); [lia| lia| exact E8| apply rt_fixed_in; mem_side| exact Rv].
    + exfalso. eapply (OWNF 7%nat); [lia| lia| exact E7| apply rt_fixed_in; mem_side| exact Rv].
    + (first [ pose proof ((ar_fsbase _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_44; dand5 dR_44 as _ _ _ _ MFS | pose proof (ar_fsbase _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & _ & _ & _ & MFS) ]).
      change (aview_of (ahull_of pa_image_ivs AL_pasan A) m) with (aview_of (pa_hull A) m) in MFS.
      (first [ pose proof ((place_fs A W)) as dR_45; dand3 dR_45 as _ _ FSM | pose proof (place_fs A W) as (_ & _ & FSM) ]). unfold a_fs in FSM.
      apply (shadow_word_mapped_of A m (p_fs (a_pl A)) kFakeStackBytes a); [apply fixed_in_aregions; mem_side| exact Rv|].
      rewrite shadow_region_aligned; [cbn [fst snd]; exact MFS| | reflexivity| unfold kFakeStackBytes; lia].
      apply (mod0_down _ 4096 64); [exists 64; reflexivity| exact FSM].
    + exfalso. eapply (OWNF 4%nat); [lia| lia| exact E4| apply rt_fixed_in; mem_side| exact Rv].
    + exfalso. eapply (OWNF 13%nat); [lia| lia| exact E13| apply rt_fixed_in; mem_side| exact Rv].
    + exfalso. eapply (OWNF 5%nat); [lia| lia| exact E5| apply rt_fixed_in; mem_side| exact Rv].
    + exfalso. eapply (OWNF 14%nat); [lia| lia| exact E14| apply rt_fixed_in; mem_side| exact Rv].
    + (* [comment removed for export] *) exfalso. apply NOW. (first [ pose proof ((sb_facts A W)) as dR_46; dand5 dR_46 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]).
      assert (B6 : a_b6 A <= a < a_b6 A + kSpaceReserve) by (apply primary_in_b6; [exact W| unfold a_sb, p_ri, kSpaceSize in *; lia]).
      eapply (owned_rt A a (a_ri A) 4096); [apply rt_fixed_in; mem_side| exact Rv| |].
      * intros LU. destruct (live_user_zone A a W LU) as [[_ SB]|(j & sc & Hj & Rj)]; [unfold a_sb, p_ri, kSpaceSize in *; lia|].
        pose proof (bm_nth_sec A j sc Hj) as Ej. destruct (bm_sep A 0 (15 + j) _ _ _ _ W E0 Ej ltac:(lia)); lia.
      * apply b6_no_live_frame; assumption.
    + exfalso. eapply (OWNF 9%nat); [lia| lia| exact E9| apply rt_fixed_in; mem_side| exact Rv].
    + exfalso. eapply (OWNF 10%nat); [lia| lia| exact E10| apply rt_fixed_in; mem_side| exact Rv].
    + exfalso. apply NIM. cbn [cl_image_lo cl_image_hi LPA]. lia.
    + exfalso. unfold kLowMemEnd, kHighMemBeg in APP. lia.
  - (* [comment removed for export] *)
    (first [ pose proof (stack_shadow_iv_facts) as dR_47; dand4 dR_47 as SF1 SF2 SF3 SF4 | pose proof stack_shadow_iv_facts as (SF1 & SF2 & SF3 & SF4) ]).
    destruct (Z.le_gt_cases (fst stack_shadow_iv) (sh a - sh a mod 8)) as [GEw|LTw].
    { (* [comment removed for export] *)
      apply (stack_shadow_word_mapped A m md _ AI GEw).
      assert (SHI : sh a < kHighMemBeg).
      { destruct APP as [LOW|HIGH]; [pose proof (sh_low_range0 a LOW); unfold kHighMemBeg; lia| pose proof (sh_high_range a ltac:(lia)); lia]. }
      pose proof (align8_hi (sh a) kHighMemBeg ltac:(reflexivity) SHI). lia. }
    assert (WLO : sh a - sh a mod 8 + 8 <= fst stack_shadow_iv).
    { pose proof (Z_div_mod_eq_full (sh a) 8). pose proof (Z.mod_pos_bound (sh a) 8 ltac:(lia)). pose proof (Z_div_exact_full_2 _ 8 ltac:(lia) SF1). lia. }
    (* [comment removed for export] *)
    intros i Hi.
    (first [ pose proof ((WX2 lo hi a HinX R APP (sh a - sh a mod 8 + i) ltac:(lia))) as dR_48; dex2 dR_48 as lo' hi'; destruct dR_48 as [Hin' Rz] | pose proof ((WX2 lo hi a HinX R APP (sh a - sh a mod 8 + i) ltac:(lia))) as dR_48; dand4 dR_48 as lo' hi' Hin' Rz | destruct (WX2 lo hi a HinX R APP (sh a - sh a mod 8 + i) ltac:(lia)) as (lo' & hi' & Hin' & Rz) ]).
    pose proof (proj1 (Forall_forall _ _) WX1 _ Hin') as B'. cbn [fst snd] in B'.
    unfold aview_of. rewrite view_visible.
    2:{ pose proof (zrange_visible_hidc (pa_hull A) lo' hi' (sh a - sh a mod 8 + i) 1 (pa_hull_extra A lo' hi' Hin')
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as ZV.
        specialize (ZV 0 ltac:(lia)). rewrite Z.add_0_r in ZV. exact ZV. }
    destruct APP as [LOW|HIGH].
    + (* [comment removed for export] *)
      pose proof (sh_low_range0 a LOW) as SR.
      pose proof (align8_lo (sh a) 0x7fff8000 ltac:(reflexivity) ltac:(lia)) as AL1. pose proof (align8_hi (sh a) 0x8fff7000 ltac:(reflexivity) ltac:(lia)) as AL2.
      apply (fun G => proj1 (HID1 _ G)). split.
      * left. clear - SR AL1 AL2 Hi. unfold kLowShadowMapBeg in *. lia.
      * ((first [ intro dR_83; dex2 dR_83 as b' n'; destruct dR_83 as [Hv Rz'] | intro dR_83; dand4 dR_83 as b' n' Hv Rz' | intros (b' & n' & Hv & Rz') ])). destruct (vis0_aligned A b' n' W Hv) as [Eq|(Hb0 & Hb64 & Hn64 & Hn0)].
        -- unfold stack_band_iv in Eq. injection Eq as -> ->. unfold sh in SF2. lia.
        -- apply (OUT b' n' Hv). apply (vis_word_back a b' n' (sh a - sh a mod 8 + i)); try assumption. lia.
    + apply (fun G => proj1 (HID1 _ G)). split.
      * pose proof (sh_high_range a ltac:(lia)) as SR.
        pose proof (align8_lo (sh a) kHighShadowMapBeg ltac:(reflexivity) ltac:(lia)) as AL1.
        pose proof (align8_hi (sh a) kHighMemBeg ltac:(reflexivity) ltac:(lia)) as AL2.
        right. clear - SR AL1 AL2 Hi. unfold kHighShadowMapBeg, kHighShadowMapSize, kHighMemBeg in *. lia.
      * ((first [ intro dR_84; dex2 dR_84 as b' n'; destruct dR_84 as [Hv Rz'] | intro dR_84; dand4 dR_84 as b' n' Hv Rz' | intros (b' & n' & Hv & Rz') ])). destruct (vis0_aligned A b' n' W Hv) as [Eq|(Hb0 & Hb64 & Hn64 & Hn0)].
        -- (* [comment removed for export] *)
           unfold stack_band_iv in Eq. injection Eq as -> ->. unfold sh in SF2. lia.
        -- apply (OUT b' n' Hv). apply (vis_word_back a b' n' (sh a - sh a mod 8 + i)); try assumption. lia.
Qed.

Lemma asI_shadow_visible : forall A m md a, pa_ainv A m md ->
  (0 <= a <= kLowMemEnd \/ kHighMemBeg <= a < 2^47) ->
  ~ pa_owned A a -> (in_image LPA a \/ aview_of (pa_hull A) m (wz a) <> None) ->
  mapped (aview_of (pa_hull A) m) (sh a - sh a mod 8) 8.
Proof.
  intros A m md a AI APP NOW VIS. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W. pose proof alloc_ceiling_val as CE.
  (first [ pose proof ((place_facts A W)) as dR_49; dand14 dR_49 as _ _ _ _ Pfs _ _ _ _ _ _ Ppa Psp0 _ | pose proof (place_facts A W) as (_ & _ & _ & _ & Pfs & _ & _ & _ & _ & _ & _ & Ppa & Psp0 & _) ]). cbv zeta in Pfs, Ppa, Psp0.
  (first [ pose proof ((sb_facts A W)) as dR_50; dand5 dR_50 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]).
  (first [ pose proof ((bm_nth_fixed A)) as dR_51; dand15 dR_51 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
  (first [ pose proof ((ar_maps _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_52; dand4 dR_52 as M1 M2 M3 M4 | pose proof (ar_maps _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (M1 & M2 & M3 & M4) ]). cbn [al_image_lo al_image_hi AL_pasan] in M4.
  change (aview_of (ahull_of pa_image_ivs AL_pasan A) m) with (aview_of (pa_hull A) m) in M1, M2, M3, M4.
  assert (IMG : in_image LPA a -> mapped (aview_of (pa_hull A) m) (sh a - sh a mod 8) 8).
  { intros IM. unfold in_image in IM. cbn [cl_image_lo cl_image_hi LPA] in IM.
    apply (shadow_word_mapped_of A m 0x10000 0x5fa000 a); [| lia| exact M4].
    apply fixed_in_aregions. cbn. tauto. }
  destruct VIS as [IM|VS]; [exact (IMG IM)|].
  assert (NN : 0 <= a) by (unfold kLowMemEnd, kHighMemBeg in APP; lia).
  assert (A64 : a < 2^64) by (unfold kLowMemEnd, kHighMemBeg in APP; lia).
  pose proof (view_some_visible _ _ _ VS) as V.
  (first [ pose proof ((visible_in_hull (pa_hull A) a V ltac:(lia))) as dR_53; dex2 dR_53 as lo hi; destruct dR_53 as [Hin R] | pose proof ((visible_in_hull (pa_hull A) a V ltac:(lia))) as dR_53; dand4 dR_53 as lo hi Hin R | destruct (visible_in_hull (pa_hull A) a V ltac:(lia)) as (lo & hi & Hin & R) ]).
  (* [comment removed for export] *)
  (first [ pose proof (stack_shadow_iv_facts) as dR_54; dand4 dR_54 as SF1 SF2 SF3 SF4 | pose proof stack_shadow_iv_facts as (SF1 & SF2 & SF3 & SF4) ]).
  assert (STKW : alloc_ceiling <= a -> mapped (aview_of (pa_hull A) m) (sh a - sh a mod 8) 8).
  { intros GE. assert (LOB : alloc_ceiling <= a < 2^47) by (unfold kLowMemEnd, kHighMemBeg in APP; lia).
    pose proof (sh_mono alloc_ceiling a GE) as S1. pose proof (sh_high_range a ltac:(unfold kHighMemBeg; lia)) as [_ S2].
    apply (stack_shadow_word_mapped A m md _ AI).
    - apply align8_lo; [exact SF1| lia].
    - apply align8_hi; [reflexivity| exact S2]. }
  unfold pa_hull, ahull_of, ahull_of_ in Hin. apply in_app_iff in Hin as [Hin|Hin].
  { apply IMG. unfold in_image. cbn [cl_image_lo cl_image_hi LPA]. cbn in Hin.
    repeat match type of Hin with _ \/ _ => destruct Hin as [E|Hin]; [injection E as <- <-; lia|] end. destruct Hin. }
  apply in_app_iff in Hin as [Hin|HinX].
  2:{ apply in_app_iff in HinX as [HinD|HinX].
      { (* [comment removed for export] *)
        exfalso. (first [ pose proof ((wfE A W)) as dR_55; dand4 dR_55 as _ DF _ _ | destruct (wfE A W) as (_ & DF & _ & _) ]). (first [ pose proof ((proj1 (Forall_forall _ _) DF _ HinD)) as dR_56; dand4 dR_56 as D1 D2 D3 _ | pose proof (proj1 (Forall_forall _ _) DF _ HinD) as (D1 & D2 & D3 & _) ]).
        cbn [fst snd] in D1, D2, D3. unfold kHighShadowMapBeg, kLowShadowBeg, kShadowGapBeg, kLowMemEnd, kHighMemBeg in *. lia. }
      (* [comment removed for export] *)
      destruct (Z.lt_ge_cases a alloc_ceiling) as [LT|GE]; [| exact (STKW GE)].
      destruct (Z.lt_ge_cases a 0x10000) as [Blo|Bge];
        [| destruct (Z.lt_ge_cases a 0x60a000) as [Ilt|Ige]; [apply IMG; unfold in_image; cbn [cl_image_lo cl_image_hi LPA]; lia|]].
      all: apply (extra_shadow_mapped A m md a lo hi AI HinX R);
        [cbn [cl_image_lo cl_image_hi LPA]; lia| unfold kLowMemEnd, kHighMemBeg in *; lia| exact NOW]. }
  unfold hull_of in Hin. apply in_map_iff in Hin as ([b s] & E & Hbs). cbn in E. injection E as <- <-.
  assert (AREG : In (b, s) (aregions AL_pasan A)) by exact Hbs.
  (* [comment removed for export] *)
  assert (OWNF : forall i bb bs b' s', (1 <= i <= 14)%nat -> i <> 6%nat -> nth_error (big_maps A) i = Some (bb, bs) ->
                 In (b', s') (runtime_maps A) -> b' <= a < b' + s' -> bb <= a < bb + bs -> False).
  { intros i bb bs b' s' Hi N6 Hn Hrt Ha Hbb. apply NOW. eapply (owned_rt A a b' s'); [exact Hrt| exact Ha| |].
    - eapply (fixed_bm_no_live_user A i); [exact W| exact Hi| exact Hn| exact Hbb].
    - eapply (fixed_bm_no_live_frame A i); [exact W| lia| exact N6| exact Hn| exact Hbb]. }
  (* [comment removed for export] *)
  assert (NOTAPP : forall b' s', ((4096 <= b' /\ b' + s' <= kLowShadowMapBeg) \/ (kHighMemBeg <= b' /\ b' + s' <= 2^47)) ->
                   0 < s' -> b' mod 8 = 0 -> (b, s) = shadow_region b' s' -> b <= a < b + s -> False).
  { intros b' s' Q1 Q3 Q8 Q4 Q5. apply (strict_not_app a); [| clear - APP; lia].
    apply (shadow_region_strict b' s' a Q8 Q3 Q1). rewrite <- Q4. cbn [fst snd]. exact Q5. }
  assert (M8 : forall p, p mod 4096 = 0 -> p mod 8 = 0) by (intros p Hp; apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact Hp]).
  unfold aregions_ in Hbs. apply in_app_iff in Hbs as [Hbs|Hbs]; [|apply in_app_iff in Hbs as [Hbs|Hbs]].
  - (* [comment removed for export] *)
    cbn -[shadow_region stack_shadow_iv Z.add Z.sub Z.mul] in Hbs. cbn [al_image_lo al_image_hi AL_pasan] in Hbs.
    destruct Hbs as [Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[]]]]]]]]]]]]]]]]]]]]]]]]]].
    + (* [comment removed for export] *) injection Q as <- <-.
      apply STKW. lia.
    + (* [comment removed for export] *) exfalso. rewrite Q in SF2, SF3, SF4. cbn [fst snd] in SF2, SF3, SF4.
      unfold sh in SF2. unfold kLowMemEnd, kHighMemBeg in *. clear - APP R SF2 SF3 SF4 CE. lia.
    + exfalso. cbv in Q. injection Q as <- <-. unfold kLowMemEnd, kHighMemBeg in APP. lia.
    + exfalso. injection Q as <- <-. eapply (OWNF 4%nat); [lia| lia| exact E4| | exact R| exact R]; apply rt_fixed_in; mem_side.
    + exfalso. injection Q as <- <-. eapply (OWNF 5%nat); [lia| lia| exact E5| | exact R| exact R]; apply rt_fixed_in; mem_side.
    + (* [comment removed for export] *) exfalso. injection Q as <- <-. apply NOW.
      assert (B6 : a_b6 A <= a < a_b6 A + kSpaceReserve) by (apply primary_in_b6; [exact W| unfold a_sb, p_ri, kSpaceSize in *; lia]).
      eapply (owned_rt A a (a_ri A) 4096); [apply rt_fixed_in; mem_side| exact R| |].
      * intros LU. destruct (live_user_zone A a W LU) as [[_ SB]|(j & sc & Hj & Rj)]; [unfold a_sb, p_ri, kSpaceSize in *; lia|].
        pose proof (bm_nth_sec A j sc Hj) as Ej. destruct (bm_sep A 0 (15 + j) _ _ _ _ W E0 Ej ltac:(lia)); lia.
      * apply b6_no_live_frame; assumption.
    + (* [comment removed for export] *) injection Q as <- <-.
      (first [ pose proof ((ar_fsbase _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_57; dand5 dR_57 as _ _ _ _ MFS | pose proof (ar_fsbase _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & _ & _ & _ & MFS) ]).
      change (aview_of (ahull_of pa_image_ivs AL_pasan A) m) with (aview_of (pa_hull A) m) in MFS.
      apply (shadow_word_mapped_of A m (p_fs (a_pl A)) kFakeStackBytes a); [apply fixed_in_aregions; mem_side| lia|].
      rewrite shadow_region_aligned; [cbn [fst snd]; exact MFS| | reflexivity| unfold kFakeStackBytes; lia].
      apply (mod0_down _ 4096 64); [exists 64; reflexivity| tauto].
    + exfalso. pose proof (app_facts _ _ (proj1 Pfs)) as AF. eapply (NOTAPP (p_fs (a_pl A)) kFakeStackBytes);
        [clear - AF CE; lia| unfold kFakeStackBytes; lia| apply M8; tauto| exact (eq_sym Q)| exact R].
    + exfalso. injection Q as <- <-. eapply (OWNF 7%nat); [lia| lia| exact E7| | exact R| exact R]; apply rt_fixed_in; mem_side.
    + exfalso. injection Q as <- <-. eapply (OWNF 8%nat); [lia| lia| exact E8| | exact R| exact R]; apply rt_fixed_in; mem_side.
    + (* [comment removed for export] *)
      exfalso. injection Q as <- <-. eapply (OWNF 1%nat); [lia| lia| exact E1| | exact R| unfold a_pa, kChunksBlockCount, kPtrArrayReserve in *; lia]; apply rt_fixed_in; mem_side.
    + exfalso. injection Q as <- <-. eapply (OWNF 9%nat); [lia| lia| exact E9| | exact R| exact R]; apply rt_fixed_in; mem_side.
    + exfalso. injection Q as <- <-. eapply (OWNF 10%nat); [lia| lia| exact E10| | exact R| exact R]; apply rt_fixed_in; mem_side.
    + (* [comment removed for export] *) exfalso. injection Q as <- <-. eapply (OWNF 14%nat); [lia| lia| exact E14| | exact R| exact R]; apply rt_fixed_in; mem_side.
    (* [comment removed for export] *)
    + exfalso. (first [ pose proof ((place_facts A W)) as dR_58; dand9 dR_58 as _ _ _ _ _ _ _ (X1 & X2 & X3) _ | pose proof (place_facts A W) as (_ & _ & _ & _ & _ & _ & _ & (X1 & X2 & X3) & _) ]). clear - X1 X3 Q R NOTAPP M8 CE APP. cbv zeta in X1, X3. apply app_facts in X1.
      eapply (NOTAPP (p_gvec (a_pl A)) 4096); [clear - X1 CE; lia| lia| apply M8; exact X3| exact (eq_sym Q)| exact R].
    + exfalso. (first [ pose proof ((place_facts A W)) as dR_59; dand10 dR_59 as _ _ _ _ _ _ _ _ (X1 & X2 & X3) _ | pose proof (place_facts A W) as (_ & _ & _ & _ & _ & _ & _ & _ & (X1 & X2 & X3) & _) ]). clear - X1 X3 Q R NOTAPP M8 CE APP. cbv zeta in X1, X3. apply app_facts in X1.
      eapply (NOTAPP (p_dvec (a_pl A)) 4096); [clear - X1 CE; lia| lia| apply M8; exact X3| exact (eq_sym Q)| exact R].
    + exfalso. (first [ pose proof ((place_facts A W)) as dR_60; dand11 dR_60 as _ _ _ _ _ _ _ _ _ (X1 & X2 & X3) _ | pose proof (place_facts A W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (X1 & X2 & X3) & _) ]). clear - X1 X3 Q R NOTAPP M8 CE APP. cbv zeta in X1, X3. apply app_facts in X1.
      eapply (NOTAPP (p_m11 (a_pl A)) 4096); [clear - X1 CE; lia| lia| apply M8; exact X3| exact (eq_sym Q)| exact R].
    + exfalso. pose proof (place_facts A W) as ((X1 & X2 & X3) & _). clear - X1 X3 Q R NOTAPP M8 CE APP. cbv zeta in X1, X3. apply app_facts in X1.
      eapply (NOTAPP (p_thr (a_pl A)) 4096); [clear - X1 CE; lia| lia| apply M8; exact X3| exact (eq_sym Q)| exact R].
    + exfalso. (first [ pose proof ((place_facts A W)) as dR_61; dand3 dR_61 as _ (X1 & X2 & X3) _ | pose proof (place_facts A W) as (_ & (X1 & X2 & X3) & _) ]). clear - X1 X3 Q R NOTAPP M8 CE APP. cbv zeta in X1, X3. apply app_facts in X1.
      eapply (NOTAPP (p_ctx (a_pl A)) 0x10000); [clear - X1 CE; lia| lia| apply M8; exact X3| exact (eq_sym Q)| exact R].
    + exfalso. (first [ pose proof ((place_facts A W)) as dR_62; dand12 dR_62 as _ _ _ _ _ _ _ _ _ _ (X1 & X2 & X3) _ | pose proof (place_facts A W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (X1 & X2 & X3) & _) ]). clear - X1 X3 Q R NOTAPP M8 CE APP. cbv zeta in X1, X3. apply app_facts in X1.
      eapply (NOTAPP (p_dtls (a_pl A)) 4096); [clear - X1 CE; lia| lia| apply M8; exact X3| exact (eq_sym Q)| exact R].
    + exfalso. (first [ pose proof ((sb_facts A W)) as dR_63; dand3 dR_63 as _ SBA _ | pose proof (sb_facts A W) as (_ & SBA & _) ]). clear - HB6 RSB SCE SBA Q R NOTAPP CE APP. unfold a_sb, a_b6 in *.
      eapply (NOTAPP (p_ri (a_pl A)) 4096); [unfold p_ri, kSpaceSize, kHighMemBeg in *; lia| lia| | exact (eq_sym Q)| exact R].
      unfold p_ri. rewrite Z.add_mod by lia. rewrite (mod0_down _ 0x10000 8 ltac:(exists 8192; reflexivity) SBA). reflexivity.
    + exfalso. (first [ pose proof ((place_facts A W)) as dR_64; dand4 dR_64 as _ _ (X1 & X2 & X3) _ | pose proof (place_facts A W) as (_ & _ & (X1 & X2 & X3) & _) ]). clear - X1 X3 Q R NOTAPP M8 CE APP. cbv zeta in X1, X3. apply app_facts in X1.
      eapply (NOTAPP (p_nodes0 (a_pl A)) kDepotNodesBlock); [clear - X1 CE; lia| unfold kDepotNodesBlock; lia| apply M8; exact X3| exact (eq_sym Q)| exact R].
    + exfalso. (first [ pose proof ((place_facts A W)) as dR_65; dand5 dR_65 as _ _ _ (X1 & X2 & X3) _ | pose proof (place_facts A W) as (_ & _ & _ & (X1 & X2 & X3) & _) ]). clear - X1 X3 Q R NOTAPP M8 CE APP. cbv zeta in X1, X3. apply app_facts in X1.
      eapply (NOTAPP (p_frames0 (a_pl A)) kStackStoreBlockBytes); [clear - X1 CE; lia| unfold kStackStoreBlockBytes; lia| apply M8; exact X3| exact (eq_sym Q)| exact R].
    + exfalso. (first [ pose proof ((place_facts A W)) as dR_66; dand7 dR_66 as _ _ _ _ _ (X1 & X2 & X3) _ | pose proof (place_facts A W) as (_ & _ & _ & _ & _ & (X1 & X2 & X3) & _) ]). clear - X1 X3 Q R NOTAPP M8 CE APP. cbv zeta in X1, X3. apply app_facts in X1.
      eapply (NOTAPP (p_itab (a_pl A)) 0x38e000); [clear - X1 CE; lia| lia| apply M8; exact X3| exact (eq_sym Q)| exact R].
    + exfalso. (first [ pose proof ((place_facts A W)) as dR_67; dand8 dR_67 as _ _ _ _ _ _ (X1 & X2 & X3) _ | pose proof (place_facts A W) as (_ & _ & _ & _ & _ & _ & (X1 & X2 & X3) & _) ]). clear - X1 X3 Q R NOTAPP M8 CE APP. cbv zeta in X1, X3. apply app_facts in X1.
      eapply (NOTAPP (p_m64k (a_pl A)) 0x10000); [clear - X1 CE; lia| lia| apply M8; exact X3| exact (eq_sym Q)| exact R].
  - (* [comment removed for export] *)
    (first [ pose proof ((classes_regions_inv _ _ _ _ Hbs)) as dR_68; dex1 dR_68 as c; destruct dR_68 as [Hc Hr] | pose proof ((classes_regions_inv _ _ _ _ Hbs)) as dR_68; dand3 dR_68 as c Hc Hr | destruct (classes_regions_inv _ _ _ _ Hbs) as (c & Hc & Hr) ]). (first [ pose proof ((wfR A W)) as dR_69; dand3 dR_69 as WR1 WR2 _ | destruct (wfR A W) as (WR1 & WR2 & _) ]).
    destruct (Z.eq_dec c 31) as [->|N31]. { rewrite (WR2 31) in Hr by lia. cbn in Hr. destruct Hr. }
    assert (HC : 1 <= c <= 30) by lia.
    pose proof (region_piece_bounds A c W HC) as RB. cbv zeta in RB. unfold a_sb in RB.
    (first [ pose proof ((WR1 c HC)) as dR_70; dand7 dR_70 as _ _ MUK _ _ MFK _ | pose proof (WR1 c HC) as (_ & _ & MUK & _ & _ & MFK & _) ]).
    assert (MU64 : rg_mapped_user (a_reg A c) mod 64 = 0) by (apply (mod0_down _ kUserMapSize 64); [exists 4096; reflexivity| exact MUK]).
    assert (MF64 : rg_mapped_fa (a_reg A c) mod 64 = 0) by (apply (mod0_down _ kFreeArrayMapSize 64); [exists 4096; reflexivity| exact MFK]).
    assert (RB64 : region_beg (p_sb (a_pl A)) c mod 64 = 0) by (apply (mod0_down _ 0x10000 64); [exists 1024; reflexivity| tauto]).
    destruct (class_regions_inv _ _ _ _ Hr) as [[Q NZ]|[[Q NZ]|[[Q NZ]|[Q NZ]]]].
    + injection Q as -> ->.
      apply (shadow_word_mapped_hidden A m md (region_beg (p_sb (a_pl A)) c) (rg_mapped_user (a_reg A c)) a AI); try assumption.
      * apply (class_in_aregions A _ c); [lia|]. unfold class_regions_, a_sb. cbv zeta. apply in_or_app. left.
        destruct (Z.eqb_spec (rg_mapped_user (a_reg A c)) 0); [lia|]. cbn. tauto.
      * right. unfold kHighMemBeg, kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia.
      * intros b' n' Hv. destruct (vis0_clear_primary A b' n' W Hv); unfold a_sb, kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia.
    + exfalso. eapply (NOTAPP (region_beg (p_sb (a_pl A)) c) (rg_mapped_user (a_reg A c))); [| | exact (mod0_down _ 64 8 ltac:(exists 8; reflexivity) RB64)| exact Q| exact R];
        (first [ dand9 RB as B1 B2 B3 B4 B5 B6 B7 B8 _ | destruct RB as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & _) ]); clear - B1 B2 B3 B4 B5 B6 B7 B8 NZ HC CE; unfold kHighMemBeg, kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia.
    + injection Q as -> ->.
      apply (shadow_word_mapped_hidden A m md (region_beg (p_sb (a_pl A)) c + kFreeArrayOffset) (rg_mapped_fa (a_reg A c)) a AI); try assumption.
      * apply (class_in_aregions A _ c); [lia|]. unfold class_regions_, a_sb. cbv zeta. apply in_or_app. right.
        destruct (Z.eqb_spec (rg_mapped_fa (a_reg A c)) 0); [lia|]. cbn. tauto.
      * right. unfold kHighMemBeg, kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia.
      * rewrite Z.add_mod, RB64 by lia. reflexivity.
      * intros b' n' Hv. destruct (vis0_clear_primary A b' n' W Hv); unfold a_sb, kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia.
    + exfalso. eapply (NOTAPP (region_beg (p_sb (a_pl A)) c + kFreeArrayOffset) (rg_mapped_fa (a_reg A c))); [| | | exact Q| exact R];
        [unfold kHighMemBeg, kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia| lia|].
      rewrite Z.add_mod by lia. rewrite (mod0_down _ 64 8 ltac:(exists 8; reflexivity) RB64). reflexivity.
  - (* [comment removed for export] *)
    unfold sec_regions_ in Hbs. apply in_flat_map in Hbs as (sc & Hsc & Hr).
    (first [ pose proof ((sec_chunk_bounds A sc W Hsc)) as dR_71; dand5 dR_71 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_bounds A sc W Hsc) as (B1 & B2 & B3 & B4 & B5) ]). pose proof (map_size_room (cs_n sc)).
    pose proof (rounded_size_ge (cs_n sc)) as RG. rewrite needed_size2_secondary in B5 by lia. pose proof (map_size_page (cs_n sc)) as MP.
    destruct Hr as [Q|[Q|[]]].
    + injection Q as <- <-. pose proof (app_facts _ _ B3) as AF.
      apply (shadow_word_mapped_hidden A m md (cs_map sc) (map_size (cs_n sc)) a AI); try assumption.
      * apply sec_in_aregions. unfold sec_regions_. apply in_flat_map. exists sc. split; [exact Hsc| mem_side].
      * clear - AF CE. lia.
      * apply (mod0_down _ 4096 64); [exists 64; reflexivity| exact B2].
      * apply (mod0_down _ kPageSize 64); [exists 64; reflexivity| exact MP].
      * intros b' n' Hv. exact (vis0_clear_sec A sc b' n' W Hsc Hv).
    + exfalso. pose proof (app_facts _ _ B3) as AF. eapply (NOTAPP (cs_map sc) (map_size (cs_n sc))); [| | | exact (eq_sym Q)| exact R];
        [clear - AF CE; lia| unfold kPageSize in *; lia| apply M8; exact B2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac lia ::= Zify.zify; xlia zchecker.
(* [comment removed for export] *)
Lemma lclasses_regions_in : forall sb reg n r c, (1 <= c)%nat -> (c <= n)%nat ->
  In r (lclass_regions_ sb (reg (Z.of_nat c)) (Z.of_nat c)) -> In r (lclasses_regions_ sb reg n).
Proof.
  intros sb reg n. induction n as [|n IH]; intros r c H1 H2 Hr; [lia|].
  cbn [lclasses_regions_]. apply in_or_app. destruct (Nat.eq_dec c (S n)) as [->|NE]; [right; exact Hr|].
  left. apply (IH r c); [lia|lia|exact Hr].
Qed.
Lemma lclasses_regions_inv : forall sb reg n r, In r (lclasses_regions_ sb reg n) ->
  exists c, 1 <= c <= Z.of_nat n /\ In r (lclass_regions_ sb (reg c) c).
Proof.
  intros sb reg n. induction n as [|n IH]; intros r H; [destruct H|].
  cbn [lclasses_regions_] in H. apply in_app_iff in H as [H|H].
  - destruct (IH r H) as (c & Hc & Hr). exists c. split; [lia| exact Hr].
  - exists (Z.of_nat (S n)). split; [lia| exact H].
Qed.
Lemma lclass_regions_inv : forall sb R c r, In r (lclass_regions_ sb R c) ->
  let rb := region_beg sb c in
  (r = shadow_region rb (rg_mapped_user R) /\ rg_mapped_user R <> 0) \/
  (r = shadow_region (rb + kFreeArrayOffset) (rg_mapped_fa R) /\ rg_mapped_fa R <> 0).
Proof.
  intros sb R c r H. cbv zeta. unfold lclass_regions_ in H. cbv zeta in H. apply in_app_iff in H as [H|H].
  - destruct (Z.eqb_spec (rg_mapped_user R) 0); [destruct H|]. destruct H as [<-|[]]. left. split; auto.
  - destruct (Z.eqb_spec (rg_mapped_fa R) 0); [destruct H|]. destruct H as [<-|[]]. right. split; auto.
Qed.
(* [comment removed for export] *)
Lemma lclass_regions_shadows : forall sb R c,
  (rg_mapped_user R <> 0 -> In (shadow_region (region_beg sb c) (rg_mapped_user R)) (lclass_regions_ sb R c)) /\
  (rg_mapped_fa R <> 0 -> In (shadow_region (region_beg sb c + kFreeArrayOffset) (rg_mapped_fa R)) (lclass_regions_ sb R c)).
Proof.
  intros sb R c. unfold lclass_regions_. cbv zeta. split; intros NZ; apply in_or_app.
  - left. destruct (Z.eqb_spec (rg_mapped_user R) 0); [lia|]. cbn [In]. left. reflexivity.
  - right. destruct (Z.eqb_spec (rg_mapped_fa R) 0); [lia|]. cbn [In]. left. reflexivity.
Qed.
Lemma pa_lhull_lregion : forall A b s, In (b, s) (alregions AL_pasan A) -> In (b, b + s) (pa_lhull A).
Proof. intros A b s H. unfold pa_lhull, alhull_of, alhull_of_. apply in_or_app. left. apply in_hull_of. exact H. Qed.
Lemma pa_lhull_dead : forall A r, In r (a_deadsh A) -> In r (pa_lhull A).
Proof. intros A r H. unfold pa_lhull, alhull_of, alhull_of_. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma pa_lhull_extra : forall A r, In r (p_extra (a_pl A)) -> In r (pa_lhull A).
Proof. intros A r H. unfold pa_lhull, alhull_of, alhull_of_. apply in_or_app. right. apply in_or_app. right. exact H. Qed.
Lemma lfixed_in_alregions : forall A r, In r (lfixed_regions_ AL_pasan (a_pl A)) -> In r (alregions AL_pasan A).
Proof. intros A r H. unfold alregions, alregions_. apply in_or_app. left. exact H. Qed.
Lemma lsec_in_alregions : forall A r, In r (lsec_regions_ (sr_chunks (a_sec A))) -> In r (alregions AL_pasan A).
Proof. intros A r H. unfold alregions, alregions_. apply in_or_app. right. apply in_or_app. right. exact H. Qed.
Lemma lclass_in_alregions : forall A r c, 1 <= c <= 31 ->
  In r (lclass_regions_ (a_sb A) (a_reg A c) c) -> In r (alregions AL_pasan A).
Proof.
  intros A r c Hc Hr. unfold alregions, alregions_. apply in_or_app. right. apply in_or_app. left.
  unfold a_sb in Hr. replace c with (Z.of_nat (Z.to_nat c)) in Hr by lia.
  apply (lclasses_regions_in _ _ 31 r (Z.to_nat c)); [lia|lia|exact Hr].
Qed.
(* [comment removed for export] *)
Lemma pa_lhull_incl : forall A, incl (pa_lhull A) (pa_hull A).
Proof.
  intros A r Hr. unfold pa_lhull, alhull_of, alhull_of_ in Hr. unfold pa_hull, ahull_of, ahull_of_.
  apply in_or_app. right. apply in_app_iff in Hr as [Hr|Hr]; [| apply in_or_app; right; exact Hr].
  apply in_or_app. left. unfold hull_of in Hr |- *. apply in_map_iff in Hr as ([b s] & <- & Hbs). apply in_map_iff. exists (b, s). split; [reflexivity|].
  unfold alregions_ in Hbs. unfold aregions_. rewrite !in_app_iff in Hbs |- *. destruct Hbs as [F|[C|S]].
  - left. rewrite fixed_regions_split. right. exact F.
  - right; left. apply lclasses_regions_inv in C as (c & Hc & Hin).
    apply lclass_regions_inv in Hin. cbv zeta in Hin.
    assert (G : In (b, s) (class_regions_ (p_sb (a_pl A)) (a_reg A c) c)).
    { unfold class_regions_. cbv zeta. destruct Hin as [[-> NZ]|[-> NZ]]; apply in_or_app.
      + left. destruct (Z.eqb_spec (rg_mapped_user (a_reg A c)) 0); [lia|]. cbn [In]. right. left. reflexivity.
      + right. destruct (Z.eqb_spec (rg_mapped_fa (a_reg A c)) 0); [lia|]. cbn [In]. right. left. reflexivity. }
    replace c with (Z.of_nat (Z.to_nat c)) in G by lia. exact (classes_regions_in _ _ 31 _ (Z.to_nat c) ltac:(lia) ltac:(lia) G).
  - right; right. unfold lsec_regions_ in S. apply in_map_iff in S as (sc & <- & Hsc). unfold sec_regions_. apply in_flat_map. exists sc. split; [exact Hsc|]. cbn [In]. right. left. reflexivity.
Qed.
Lemma pa_lhull_le : forall A, hull_le (pa_lhull A) (pa_hull A).
Proof. intros A. apply hull_le_incl. apply pa_lhull_incl. Qed.

(* [comment removed for export] *)
Theorem ahull_cover_ : forall P reg sec dead md,
  alzfree_ AL_pasan P reg md ->
  Forall (fun sc => eager_map (wz (cs_map sc)) (wz (map_size (cs_n sc))) md) (sr_chunks sec) ->
  (forall s, In s (sr_chunks sec) -> 0 <= cs_map s /\ 0 <= map_size (cs_n s) /\ cs_map s + map_size (cs_n s) < 2^64) ->
  hull_cover (ahull_of_ pa_image_ivs AL_pasan P reg sec dead) (alhull_of_ AL_pasan P reg sec dead) (m_vm_lazy md).
Proof.
  intros P reg sec dead md (Z1 & Z2 & Z3) L6 SB.
  assert (LREG : forall b s, In (b, s) (alregions_ AL_pasan P reg sec) -> In (b, b + s) (alhull_of_ AL_pasan P reg sec dead)).
  { intros b s H. unfold alhull_of_. apply in_or_app. left. apply in_hull_of. exact H. }
  intros lo hi Hin. unfold ahull_of_ in Hin. apply in_app_iff in Hin as [Hin|Hin].
  { (* [comment removed for export] *) right. cbn [al_image_lo al_image_hi AL_pasan] in Z1.
    unfold pa_image_ivs in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; apply (lazy_free_shrink _ _ _ _ _ Z1); lia. }
  apply in_app_iff in Hin as [Hin|Hin]; [| left; apply iv_sub_In; unfold alhull_of_; apply in_or_app; right; exact Hin].
  unfold hull_of in Hin. apply in_map_iff in Hin as ([b s] & E & Hbs). cbn in E. injection E as <- <-.
  unfold aregions_ in Hbs. rewrite !in_app_iff in Hbs. destruct Hbs as [F|[C|S]].
  - (* [comment removed for export] *)
    rewrite fixed_regions_split in F. destruct F as [E|F].
    + injection E as <- <-. right. intros x Hx. apply Z2. lia.
    + left. apply iv_sub_In. apply LREG. unfold alregions_. apply in_or_app. left. exact F.
  - (* [comment removed for export] *)
    apply classes_regions_inv in C as (c & Hc & Hin). change (Z.of_nat 31) with 31 in Hc.
    pose proof (Z3 c Hc) as [ZU ZF]. pose proof (lclass_regions_shadows (p_sb P) (reg c) c) as [SU SF].
    assert (LC : forall r, In r (lclass_regions_ (p_sb P) (reg c) c) -> In r (alregions_ AL_pasan P reg sec)).
    { intros r Hr. unfold alregions_. apply in_or_app. right. apply in_or_app. left.
      replace c with (Z.of_nat (Z.to_nat c)) in Hr by lia. apply (lclasses_regions_in _ _ 31 r (Z.to_nat c)); [lia|lia|exact Hr]. }
    apply class_regions_inv in Hin. cbv zeta in Hin. destruct Hin as [[E NZ]|[[E NZ]|[[E NZ]|[E NZ]]]].
    + injection E as -> ->. right. exact ZU.
    + left. apply iv_sub_In. rewrite (surjective_pairing (shadow_region _ _)) in E. injection E as -> ->.
      apply LREG. apply LC. exact (SU NZ).
    + injection E as -> ->. right. exact ZF.
    + left. apply iv_sub_In. rewrite (surjective_pairing (shadow_region _ _)) in E. injection E as -> ->.
      apply LREG. apply LC. exact (SF NZ).
  - (* [comment removed for export] *)
    unfold sec_regions_ in S. apply in_flat_map in S as (sc & Hsc & Hin). cbn [In] in Hin.
    destruct Hin as [E|[E|[]]].
    + injection E as <- <-. right. pose proof (proj1 (Forall_forall _ _) L6 sc Hsc) as EM. cbv beta in EM.
      pose proof (SB sc Hsc) as (B1 & B2 & B3).
      pose proof (lazy_free_of_eager_map _ _ md EM) as LF. rewrite !unsigned_lit in LF by lia. exact LF.
    + left. apply iv_sub_In. rewrite (surjective_pairing (shadow_region _ _)) in E. injection E as <- <-.
      apply LREG. unfold alregions_. apply in_or_app. right. apply in_or_app. right. unfold lsec_regions_. apply in_map_iff. exists sc. split; [reflexivity| exact Hsc].
Qed.

Theorem ahull_cover : forall A md, WF A -> aledger_ AL_pasan (a_pl A) (a_reg A) (a_sec A) md ->
  hull_cover (pa_hull A) (pa_lhull A) (m_vm_lazy md).
Proof.
  intros A md W LED. destruct LED as (_ & _ & _ & _ & _ & L6 & _ & _ & Z9).
  unfold pa_hull, ahull_of, pa_lhull, alhull_of. apply (ahull_cover_ _ _ _ _ md Z9 L6).
  intros sc Hsc. (first [ pose proof ((sec_chunk_bounds A sc W Hsc)) as dR; dand5 dR as B1 _ B3 B4 _ | pose proof (sec_chunk_bounds A sc W Hsc) as (B1 & _ & B3 & B4 & _) ]).
  apply app_facts in B3. pose proof alloc_ceiling_val. lia.
Qed.
End Pasan.
